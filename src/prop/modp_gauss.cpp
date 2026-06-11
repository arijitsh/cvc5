/******************************************************************************
 * Top contributors (to current version):
 *   Arijit Shaw
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Incremental Gauss-Jordan elimination engine over Z_p (a prime field).
 */

#include "prop/modp_gauss.h"

#include <cstdint>
#include <cstdlib>

#include "base/check.h"

namespace cvc5::internal {
namespace prop {

uint64_t ModpGaussEngine::modmul(uint64_t a, uint64_t b, uint64_t m)
{
  return (a % m) * (b % m) % m;
}

uint64_t ModpGaussEngine::modinv(uint64_t a, uint64_t m)
{
  // Extended Euclid. m is prime and a is reduced and nonzero, so gcd(a,m)=1.
  int64_t t = 0, newt = 1;
  int64_t r = static_cast<int64_t>(m), newr = static_cast<int64_t>(a % m);
  while (newr != 0)
  {
    int64_t q = r / newr;
    int64_t tmp = t - q * newt;
    t = newt;
    newt = tmp;
    tmp = r - q * newr;
    r = newr;
    newr = tmp;
  }
  if (t < 0)
  {
    t += static_cast<int64_t>(m);
  }
  return static_cast<uint64_t>(t);
}

void ModpGaussEngine::addRow(const SatClause& clause,
                             const std::vector<uint64_t>& weights,
                             uint64_t rhs,
                             uint64_t modulus)
{
  Assert(clause.size() == weights.size());
  Assert(modulus > 1);
  std::unordered_map<SatVariable, uint64_t> acc;
  std::vector<SatVariable> order;
  uint64_t r = rhs % modulus;
  for (size_t i = 0; i < clause.size(); ++i)
  {
    const SatLiteral& lit = clause[i];
    uint64_t w = weights[i] % modulus;
    SatVariable v = lit.getSatVariable();
    if (lit.isNegated())
    {
      // weight*(1 - b) = weight - weight*b. The constant 'weight' is on the LHS
      // (sum == rhs), so move it to the rhs by SUBTRACTING it; the variable's
      // coefficient becomes -weight (= modulus - weight).
      r = (r + modulus - w) % modulus;
      w = (modulus - w) % modulus;
    }
    auto it = acc.find(v);
    if (it == acc.end())
    {
      acc.emplace(v, w);
      order.push_back(v);
    }
    else
    {
      it->second = (it->second + w) % modulus;
    }
  }
  // Tuning knob for the reachability DP modulus cutoff (perf experiments).
  if (const char* e = std::getenv("CVC5_MODP_REACH_MAX"))
  {
    d_reachMaxModulus = static_cast<uint64_t>(std::strtoull(e, nullptr, 10));
  }

  Row row;
  row.rhs = r;
  row.mod = modulus;
  for (SatVariable v : order)
  {
    uint64_t w = acc[v] % modulus;
    if (w == 0)
    {
      continue;  // a zero net coefficient does not constrain the variable
    }
    row.vars.push_back(v);
    row.coeffs.push_back(w);
  }
  d_rows.push_back(std::move(row));
}

bool ModpGaussEngine::findConflict(const AssignmentFn& value,
                                   SatClause& conflict) const
{
  for (const Row& row : d_rows)
  {
    uint64_t sum = 0;
    bool all_assigned = true;
    for (size_t i = 0; i < row.vars.size(); ++i)
    {
      int32_t a = value(row.vars[i]);
      if (a == 0)
      {
        all_assigned = false;
        break;
      }
      if (a > 0)
      {
        sum = (sum + row.coeffs[i]) % row.mod;
      }
    }
    if (all_assigned && sum != row.rhs)
    {
      conflict.clear();
      for (SatVariable v : row.vars)
      {
        // Emit the literal currently FALSE so the clause is fully falsified:
        // variable true -> ~v, variable false -> v.
        conflict.push_back(SatLiteral(v, value(v) > 0));
      }
      return true;
    }
  }
  return false;
}

bool ModpGaussEngine::reachabilityRow(const Row& row,
                                      const AssignmentFn& value,
                                      const SkipFn& skip,
                                      const EmitFn& emit,
                                      const ConflictFn& emitConflict) const
{
  const uint64_t p = row.mod;
  uint64_t s = 0;  // sum of assigned-true weights (mod p)
  std::vector<size_t> un;
  un.reserve(row.vars.size());
  // Falsifying literals of the assigned vars: the currently-FALSE literal of
  // each (var true -> ~v, var false -> v). These form the conflict clause /
  // the body of a forced literal's reason.
  std::vector<SatLiteral> assignedFalse;
  assignedFalse.reserve(row.vars.size());
  for (size_t i = 0; i < row.vars.size(); ++i)
  {
    int32_t a = value(row.vars[i]);
    if (a == 0)
    {
      un.push_back(i);
    }
    else
    {
      if (a > 0)
      {
        s = (s + row.coeffs[i]) % p;
      }
      assignedFalse.push_back(SatLiteral(row.vars[i], a > 0));
    }
  }
  const uint64_t t = (row.rhs + p - s) % p;  // residue the unassigned must hit
  if (un.empty())
  {
    if (t != 0 && !std::getenv("CVC5_MODP_NO_CONFLICT"))  // fully assigned, violated
    {
      emitConflict(SatClause(assignedFalse.begin(), assignedFalse.end()));
      return true;
    }
    return false;
  }

  const size_t k = un.size();
  // prefix[i] = residues reachable by subsets of un[0..i-1]; suffix likewise.
  std::vector<std::vector<char>> prefix(k + 1), suffix(k + 1);
  prefix[0].assign(p, 0);
  prefix[0][0] = 1;
  for (size_t i = 0; i < k; ++i)
  {
    const uint64_t w = row.coeffs[un[i]];
    prefix[i + 1] = prefix[i];
    for (uint64_t r = 0; r < p; ++r)
    {
      if (prefix[i][r])
      {
        prefix[i + 1][(r + w) % p] = 1;
      }
    }
  }
  // Early conflict: the unassigned bits cannot reach the required residue.
  if (!prefix[k][t])
  {
    if (std::getenv("CVC5_MODP_NO_CONFLICT"))
    {
      return false;
    }
    emitConflict(SatClause(assignedFalse.begin(), assignedFalse.end()));
    return true;
  }

  suffix[k].assign(p, 0);
  suffix[k][0] = 1;
  for (size_t i = k; i-- > 0;)
  {
    const uint64_t w = row.coeffs[un[i]];
    suffix[i] = suffix[i + 1];
    for (uint64_t r = 0; r < p; ++r)
    {
      if (suffix[i + 1][r])
      {
        suffix[i][(r + w) % p] = 1;
      }
    }
  }

  // Forced-bit propagation: bit un[i] may be 0 iff t is reachable by the OTHER
  // unassigned bits, and may be 1 iff t-w_i is. If only one value keeps t
  // reachable, force it. reach_without_i = sumset(prefix[i], suffix[i+1]).
  if (std::getenv("CVC5_MODP_NO_FORCE"))
  {
    return false;
  }
  for (size_t i = 0; i < k; ++i)
  {
    SatVariable v = row.vars[un[i]];
    if (skip(v))
    {
      continue;
    }
    const uint64_t w = row.coeffs[un[i]];
    const std::vector<char>& pre = prefix[i];
    const std::vector<char>& suf = suffix[i + 1];
    bool can0 = false;  // reach_without_i[t]
    bool can1 = false;  // reach_without_i[(t - w) mod p]
    const uint64_t t1 = (t + p - w % p) % p;
    for (uint64_t a = 0; a < p && !(can0 && can1); ++a)
    {
      if (!pre[a])
      {
        continue;
      }
      if (suf[(t + p - a) % p])
      {
        can0 = true;
      }
      if (suf[(t1 + p - a) % p])
      {
        can1 = true;
      }
    }
    if (can0 == can1)
    {
      continue;  // both values feasible (or row infeasible, already conflicted)
    }
    // Force the only feasible value. Reason: forced lit + the falsifying lit of
    // every assigned var in the row (so the clause is unit and implies it).
    SatLiteral forced(v, /*negated=*/!can1);  // can1 -> must be true
    SatClause reason;
    reason.reserve(assignedFalse.size() + 1);
    reason.push_back(forced);
    reason.insert(reason.end(), assignedFalse.begin(), assignedFalse.end());
    emit(forced, std::move(reason));
  }
  return false;
}

void ModpGaussEngine::propagate(const AssignmentFn& value,
                                const SkipFn& skip,
                                const EmitFn& emit,
                                const ConflictFn& emitConflict) const
{
  if (d_rows.empty())
  {
    return;
  }
  // All rows of a counting run use the same prime; only combine those.
  const uint64_t mod = d_rows.front().mod;

  // Per-row subset-sum reachability over Z_p (small modulus): early conflicts
  // and forced bits that stop the brute-force enumerate-and-reject blow-up the
  // plain Gauss-Jordan engine suffers (it only acts on rows reduced to a single
  // unassigned variable). For large moduli the DP is too costly; fall through
  // to Gauss-Jordan only.
  if (mod <= d_reachMaxModulus)
  {
    for (const Row& row : d_rows)
    {
      if (row.mod != mod)
      {
        continue;
      }
      if (reachabilityRow(row, value, skip, emit, emitConflict))
      {
        return;  // a conflict was emitted; let the SAT solver resolve it
      }
    }
  }

  // Dense column index for every variable occurring in a row of this modulus.
  std::unordered_map<SatVariable, int> col_of;
  std::vector<SatVariable> var_of_col;
  std::vector<size_t> row_idx;
  for (size_t ri = 0; ri < d_rows.size(); ++ri)
  {
    if (d_rows[ri].mod != mod)
    {
      continue;
    }
    row_idx.push_back(ri);
    for (SatVariable v : d_rows[ri].vars)
    {
      if (col_of.find(v) == col_of.end())
      {
        col_of[v] = static_cast<int>(var_of_col.size());
        var_of_col.push_back(v);
      }
    }
  }
  const size_t ncols = var_of_col.size();
  const size_t nrows = row_idx.size();
  if (ncols == 0 || nrows == 0)
  {
    return;
  }

  // Dense coefficient matrix (mod 'mod') plus the rhs column.
  std::vector<uint64_t> mat(nrows * ncols, 0);
  std::vector<uint64_t> rrhs(nrows, 0);
  for (size_t r = 0; r < nrows; ++r)
  {
    const Row& row = d_rows[row_idx[r]];
    uint64_t* mr = &mat[r * ncols];
    for (size_t i = 0; i < row.vars.size(); ++i)
    {
      int c = col_of[row.vars[i]];
      mr[c] = (mr[c] + row.coeffs[i]) % mod;
    }
    rrhs[r] = row.rhs % mod;
  }

  // Gauss-Jordan over the currently-unassigned columns only.
  std::vector<char> pivoted(nrows, 0);
  for (size_t c = 0; c < ncols; ++c)
  {
    if (value(var_of_col[c]) != 0)
    {
      continue;  // pivot only on currently-unassigned columns
    }
    int pr = -1;
    for (size_t r = 0; r < nrows; ++r)
    {
      if (!pivoted[r] && mat[r * ncols + c] != 0)
      {
        pr = static_cast<int>(r);
        break;
      }
    }
    if (pr < 0)
    {
      continue;
    }
    pivoted[pr] = 1;
    uint64_t* prow = &mat[static_cast<size_t>(pr) * ncols];
    const uint64_t inv = modinv(prow[c], mod);
    // Normalise the pivot row so the pivot coefficient becomes 1.
    for (size_t cc = 0; cc < ncols; ++cc)
    {
      if (prow[cc])
      {
        prow[cc] = modmul(prow[cc], inv, mod);
      }
    }
    rrhs[pr] = modmul(rrhs[pr], inv, mod);
    // Eliminate column c from every other row.
    for (size_t r = 0; r < nrows; ++r)
    {
      if (static_cast<int>(r) == pr)
      {
        continue;
      }
      uint64_t f = mat[r * ncols + c];
      if (f == 0)
      {
        continue;
      }
      uint64_t* rw = &mat[r * ncols];
      for (size_t cc = 0; cc < ncols; ++cc)
      {
        if (prow[cc])
        {
          rw[cc] = (rw[cc] + mod - modmul(f, prow[cc], mod)) % mod;
        }
      }
      rrhs[r] = (rrhs[r] + mod - modmul(f, rrhs[pr], mod)) % mod;
    }
  }

  // Propagate every reduced row with exactly one unassigned variable whose
  // forced value is Boolean.
  for (size_t r = 0; r < nrows; ++r)
  {
    const uint64_t* mr = &mat[r * ncols];
    int n_un = 0, n_as = 0;
    size_t uc = 0;
    uint64_t eff = rrhs[r];  // rhs minus assigned contributions
    for (size_t c = 0; c < ncols; ++c)
    {
      if (mr[c] == 0)
      {
        continue;
      }
      int32_t a = value(var_of_col[c]);
      if (a == 0)
      {
        ++n_un;
        uc = c;
      }
      else
      {
        ++n_as;
        if (a > 0)
        {
          eff = (eff + mod - mr[c]) % mod;  // move assigned-true term to rhs
        }
      }
    }
    if (n_un != 1 || n_as < 1)
    {
      continue;  // conflicts / global units handled by findConflict
    }
    // mr[uc] * b == eff (mod p)  =>  b == eff * inv(mr[uc]).
    uint64_t val = modmul(eff, modinv(mr[uc], mod), mod);
    if (val > 1)
    {
      continue;  // non-Boolean forced value: caught at full assignment
    }
    SatVariable uvar = var_of_col[uc];
    if (skip(uvar))
    {
      continue;  // already assigned or already queued
    }
    SatLiteral forced(uvar, /*negated=*/val == 0);
    // Reason clause: forced literal plus the falsifying literal of every
    // assigned variable in the reduced row, so the clause is unit and implies
    // 'forced'.
    SatClause reason;
    reason.push_back(forced);
    for (size_t c = 0; c < ncols; ++c)
    {
      if (mr[c] == 0)
      {
        continue;
      }
      int32_t a = value(var_of_col[c]);
      if (a == 0)
      {
        continue;
      }
      reason.push_back(SatLiteral(var_of_col[c], a > 0));
    }
    emit(forced, std::move(reason));
  }
}

}  // namespace prop
}  // namespace cvc5::internal
