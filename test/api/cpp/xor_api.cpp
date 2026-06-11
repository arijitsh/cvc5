/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regression test for Boolean xor helper APIs.
 */

#include <cvc5/cvc5.h>

#include <iostream>
#include <string>

using namespace cvc5;
using namespace std;

int main()
{
  TermManager tm;
  Solver slv(tm);
  slv.setLogic("QF_BOOL");

  Sort boolSort = tm.getBooleanSort();
  Term x = tm.mkConst(boolSort, "x");
  Term y = tm.mkConst(boolSort, "y");
  Term z = tm.mkConst(boolSort, "z");

  Term notX = x.notTerm();
  Term notY = y.notTerm();
  Term notZ = z.notTerm();

  Term formula1 = notX.orTerm(notY);
  Term formula2 = notX.orTerm(y);
  Term tripleXor = x.xorTerm(notY).xorTerm(z);
  Term tripleXorMulti = x.xorTerm({notY, z});
  Term tripleXorViaManager = tm.mkTerm(Kind::XOR, {x, notY, z});
  Term doubleXor = y.xorTerm(z);
  Term doubleXorMulti = y.xorTerm({z});
  Term doubleXorViaManager = tm.mkTerm(Kind::XOR, {y, z});

  auto checkAssignment = [&](const string& name,
                             const Term& formula,
                             bool expected,
                             bool vx,
                             bool vy,
                             bool vz) {
    slv.push();
    slv.assertFormula(vx ? x : notX);
    slv.assertFormula(vy ? y : notY);
    slv.assertFormula(vz ? z : notZ);
    Term assumption = expected ? formula.notTerm() : formula;
    Result r = slv.checkSatAssuming(assumption);
    slv.pop();
    if (!r.isUnsat())
    {
      cerr << "Unexpected result while testing " << name << " with assignment"
           << " x=" << vx << " y=" << vy << " z=" << vz
           << ". Expected value: " << expected << ", solver result: " << r
           << endl;
      return false;
    }
    return true;
  };

  auto testFormula = [&](const string& name, const Term& formula, auto eval) {
    bool ok = true;
    for (int xv = 0; xv < 2; ++xv)
    {
      for (int yv = 0; yv < 2; ++yv)
      {
        for (int zv = 0; zv < 2; ++zv)
        {
          bool vx = xv != 0;
          bool vy = yv != 0;
          bool vz = zv != 0;
          bool expected = eval(vx, vy, vz);
          ok &= checkAssignment(name, formula, expected, vx, vy, vz);
        }
      }
    }
    return ok;
  };

  bool success = true;
  success &= testFormula("notX_or_notY", formula1,
                         [](bool vx, bool vy, bool) { return (!vx) || (!vy); });
  success &= testFormula("notX_or_y", formula2,
                         [](bool vx, bool vy, bool) { return (!vx) || vy; });
  success &= testFormula("triple_xor_term", tripleXor, [](bool vx, bool vy, bool vz) {
    bool partial = vx ^ (!vy);
    return partial ^ vz;
  });
  success &= testFormula("triple_xor_term_multi",
                         tripleXorMulti,
                         [](bool vx, bool vy, bool vz) {
                           bool partial = vx ^ (!vy);
                           return partial ^ vz;
                         });
  success &= testFormula("double_xor_term", doubleXor,
                         [](bool, bool vy, bool vz) { return vy ^ vz; });
  success &= testFormula("double_xor_term_multi",
                         doubleXorMulti,
                         [](bool, bool vy, bool vz) { return vy ^ vz; });
  success &= testFormula("triple_xor_manager", tripleXorViaManager,
                         [](bool vx, bool vy, bool vz) {
                           bool partial = vx ^ (!vy);
                           return partial ^ vz;
                         });
  success &= testFormula("double_xor_manager", doubleXorViaManager,
                         [](bool, bool vy, bool vz) { return vy ^ vz; });

  if (!success)
  {
    return 1;
  }

  // Verify that xor terms built via helper methods match the ones built via
  // TermManager::mkTerm for XOR.
  slv.push();
  Term eqDouble = doubleXor.eqTerm(doubleXorViaManager);
  Result doubleEq = slv.checkSatAssuming(eqDouble.notTerm());
  slv.pop();
  if (!doubleEq.isUnsat())
  {
    cerr << "Double xor helpers produced non-equivalent terms." << endl;
    return 1;
  }

  slv.push();
  Term eqTriple = tripleXor.eqTerm(tripleXorViaManager);
  Result tripleEq = slv.checkSatAssuming(eqTriple.notTerm());
  slv.pop();
  if (!tripleEq.isUnsat())
  {
    cerr << "Triple xor helpers produced non-equivalent terms." << endl;
    return 1;
  }

  slv.push();
  Term eqTripleMulti = tripleXorMulti.eqTerm(tripleXorViaManager);
  Result tripleMultiEq = slv.checkSatAssuming(eqTripleMulti.notTerm());
  slv.pop();
  if (!tripleMultiEq.isUnsat())
  {
    cerr << "Multi-argument xor helper produced non-equivalent term." << endl;
    return 1;
  }

  slv.push();
  Term eqDoubleMulti = doubleXorMulti.eqTerm(doubleXorViaManager);
  Result doubleMultiEq = slv.checkSatAssuming(eqDoubleMulti.notTerm());
  slv.pop();
  if (!doubleMultiEq.isUnsat())
  {
    cerr << "Multi-argument xor helper produced non-equivalent double term." << endl;
    return 1;
  }

  return 0;
}
