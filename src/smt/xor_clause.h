/******************************************************************************
 * Top contributors (to current version):
 *   ChatGPT (OpenAI),
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Data structure representing an XOR clause assertion.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__XOR_CLAUSE_H
#define CVC5__SMT__XOR_CLAUSE_H

#include <cstdint>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace smt {

/** Information about an asserted native XOR clause. */
struct XorClause
{
  /** The literals that form the XOR clause. */
  std::vector<Node> d_clause;
  /** The desired parity of the XOR clause. */
  bool d_rhs = false;
  /**
   * The Boolean formula corresponding to this XOR clause. This is the node
   * that is exposed through get-assertions and used for bookkeeping such as
   * proofs and unsat cores.
   */
  Node d_formula;

  /* ----- Optional mod-p (linear-over-Z_p) row, see assertModpClause -------- *
   * When d_modulus != 0 this struct describes, instead of a GF(2) parity, a
   * linear constraint  sum_i d_weights[i] * lit_i  ==  d_rhsValue (mod
   * d_modulus), where lit_i are the literals in d_clause. This is the prime
   * hash (Sum a_i x_i mod p == c) handed to the CadicalPropagator's Z_p
   * Gauss-Jordan engine instead of being bit-blasted. d_rhs is unused here. */
  /** Coefficient of each literal in d_clause (aligned by index). */
  std::vector<uint64_t> d_weights;
  /** The (prime) modulus; 0 means "this is an ordinary XOR clause". */
  uint64_t d_modulus = 0;
  /** Right-hand side value of the mod-p row. */
  uint64_t d_rhsValue = 0;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
