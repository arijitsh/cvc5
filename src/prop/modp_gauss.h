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
 *
 * Solves systems of linear constraints  sum_i a_i * b_i == c  (mod p)  where
 * the b_i are Boolean (0/1) SAT variables. This is the "prime hash" used by
 * approximate model counting; it generalises the GF(2) parity (XOR) engine to
 * an arbitrary prime modulus. The engine is self-contained: it stores the rows
 * and computes conflicts and unit propagations, but it does not talk to the SAT
 * solver itself. The owning CadicalPropagator drives it (supplying the current
 * assignment) and routes the results through the external-propagation channel
 * so CaDiCaL performs sound conflict analysis / backjumping.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__MODP_GAUSS_H
#define CVC5__PROP__MODP_GAUSS_H

#include <cstdint>
#include <functional>
#include <unordered_map>
#include <vector>

#include "prop/sat_solver_types.h"

namespace cvc5::internal {
namespace prop {

class ModpGaussEngine
{
 public:
  /**
   * Assignment query for a variable, as the propagator stores it:
   *   0  unassigned,  >0  assigned true,  <0  assigned false.
   */
  using AssignmentFn = std::function<int32_t(SatVariable)>;

  /** Predicate: should this (about-to-be-forced) variable be skipped? */
  using SkipFn = std::function<bool(SatVariable)>;

  /** Sink for a forced literal and its reason clause (forced lit included). */
  using EmitFn = std::function<void(SatLiteral, SatClause&&)>;

  /** Sink for a conflict clause (currently all-falsified). */
  using ConflictFn = std::function<void(SatClause&&)>;

  /**
   * Register a row  sum_i weights[i] * clause[i] == rhs (mod modulus).
   * A negated literal ~b contributes weight*(1-b): its weight is folded as
   * rhs += weight and stored as (modulus - weight) over the positive variable.
   * Coefficients are accumulated per variable and reduced mod modulus; a
   * variable whose net coefficient is 0 is dropped.
   */
  void addRow(const SatClause& clause,
              const std::vector<uint64_t>& weights,
              uint64_t rhs,
              uint64_t modulus);

  /** @return whether any rows are registered. */
  bool hasRows() const { return !d_rows.empty(); }

  /**
   * If some fully-assigned row is violated (sum a_i*val_i mod p != rhs), fill
   * `conflict` with the negation of the current assignment of that row's
   * variables (an all-falsified clause) and return true.
   */
  bool findConflict(const AssignmentFn& value, SatClause& conflict) const;

  /**
   * Gauss-Jordan over the currently-unassigned columns. For every reduced row
   * left with exactly one unassigned variable whose forced value is Boolean
   * (0 or 1) and that `skip` does not reject, append the forced literal to
   * `propagations` and its reason clause (forced literal + the falsifying
   * literal of every assigned variable in the reduced row) to `reasons`.
   * Non-Boolean forced values and fully-assigned violations are left to
   * findConflict.
   */
  void propagate(const AssignmentFn& value,
                 const SkipFn& skip,
                 const EmitFn& emit,
                 const ConflictFn& emitConflict) const;

 private:
  struct Row
  {
    std::vector<SatVariable> vars;
    std::vector<uint64_t> coeffs;
    uint64_t rhs;
    uint64_t mod;
  };

  /** (a * b) mod m, with a,b reduced and m < 2^32 so the product fits 64 bits. */
  static uint64_t modmul(uint64_t a, uint64_t b, uint64_t m);
  /** Modular inverse of a (mod m), m prime, a != 0 (mod m). */
  static uint64_t modinv(uint64_t a, uint64_t m);

  /**
   * Subset-sum reachability propagation for a single row (only when the modulus
   * is small, see d_reachMaxModulus). Given the currently-assigned bits fixing a
   * partial sum, a DP over the unassigned weights computes which residues the
   * unassigned bits can still reach. If the required residue is unreachable the
   * row is already violated -> early conflict (before a full assignment). When
   * exactly one Boolean value of an unassigned bit keeps the residue reachable,
   * that bit is forced. @return true if a conflict was emitted.
   */
  bool reachabilityRow(const Row& row,
                       const AssignmentFn& value,
                       const SkipFn& skip,
                       const EmitFn& emit,
                       const ConflictFn& emitConflict) const;

  std::vector<Row> d_rows;
  /**
   * Max modulus for which the (O(k*p)/O(k*p^2)) subset-sum reachability DP is
   * used during propagation. DEFAULT 0 = OFF: although it gives the strong
   * partial-assignment pruning the plain GJE lacks, it is UNSOUND in this
   * architecture -- the propagator reasons over the (= extract #b1) atoms, which
   * are only lazily linked to x's real bits (bits live in the bv-sat-solver), so
   * aggressive forcing/conflicting on partial atom states that do not yet match
   * x desyncs them and over-counts. Enable only for experiments via env
   * CVC5_MODP_REACH_MAX. See memory prime-gj-modp-propagator.
   */
  uint64_t d_reachMaxModulus = 0;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__MODP_GAUSS_H
