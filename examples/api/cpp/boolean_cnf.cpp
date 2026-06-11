#include <cvc5/cvc5.h>
#include <cvc5/cvc5_parser.h>
#ifdef CVC5_USE_CRYPTOMINISAT
#include <cryptominisat5/cryptominisat.h>
#endif
#include <iostream>

using namespace cvc5;
using namespace cvc5::parser;

int main()
{
  TermManager tm;
  Solver slv(tm);
  SymbolManager sm(tm);

  InputParser decls(&slv, &sm);
  std::stringstream ss;
  ss << "(set-logic QF_LRA)\n";
  ss << "(declare-fun x () Real)\n";
  ss << "(declare-fun y () Real)\n";
  decls.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, ss, "decls");
  Command cmd;
  while (!(cmd = decls.nextCommand()).isNull())
  {
    cmd.invoke(&slv, &sm, std::cout);
  }

  InputParser fparser(&slv, &sm);
  std::stringstream fs;
  fs << "(and (> x y) (> y 0))";
  fparser.setStreamInput(modes::InputLanguage::SMT_LIB_2_6, fs, "formula");
  Term formula = fparser.nextTerm();
  std::cout << "Parsed formula: " << formula << std::endl;

  slv.assertFormula(formula);
  std::cout << "cvc5 result: " << slv.checkSat() << std::endl;

  auto res = slv.getBooleanAbstraction(formula);
  std::vector<uint32_t> cnf = res.first;
  auto map = res.second;

#ifdef CVC5_USE_CRYPTOMINISAT
  CMSat::SATSolver cms;
  size_t maxVar = 0;
  for (uint32_t lit : cnf)
  {
    if (lit != 0)
    {
      size_t v = std::abs((int)lit) - 1;
      if (v > maxVar) maxVar = v;
    }
  }
  for (size_t i = 0; i <= maxVar; ++i) cms.new_var();
  std::vector<CMSat::Lit> clause;
  for (uint32_t lit : cnf)
  {
    if (lit == 0)
    {
      cms.add_clause(clause);
      clause.clear();
    }
    else
    {
      bool sign = ((int)lit) < 0;
      uint32_t v = std::abs((int)lit) - 1;
      clause.push_back(CMSat::Lit(v, sign));
    }
  }
  auto ret = cms.solve();
  std::cout << "CryptoMiniSat result: "
            << (ret == CMSat::l_True ? "SAT" : ret == CMSat::l_False ? "UNSAT" : "UNKNOWN")
            << std::endl;
#else
  std::cout << "CryptoMiniSat not available" << std::endl;
#endif
  return 0;
}

