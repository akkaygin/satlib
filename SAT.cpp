#include "SAT.hpp"
#include <string>
#include <print>

namespace rocket::sat {
void solver::RegisterClause(clause const& cls) {
  if (LearnedOffset > static_cast<clause::index>(0)) { throw; }

  if (cls.is_unit_in(Variables)) {
    AssignValue(cls.Literals[static_cast<literal::index>(0)].Variable(), cls.Literals[static_cast<literal::index>(0)].EffectiveValue(variable::assignment::TRUE), std::nullopt);
  } else {
    for (literal::index i{0}; i < literal::index{2} && i < cls.Literals.size(); i = i + literal::index{1}) {
      RegisterWatcher(cls.Literals[i].Raw, Clauses.size());
    }
  }

  Statistics.ClauseCount++;
  Clauses.push_back(cls);
}

void solver::RegisterLearned(clause const& cls) {
  for (literal::index i {0}; i < literal::index{2} && i < cls.Literals.size(); i = i + literal::index{1}) {
    RegisterWatcher(cls.Literals[i].Raw, Clauses.size());
  }
  Statistics.LearnedCount++;
  Clauses.push_back(cls);
}

void solver::ResolveConflict(clause::index const reason_idx) {
  Statistics.ConflictCount++;
  clause const conflicting {Clauses[reason_idx]};
  decision_level const current_level {CurrentLevel()};

  clause lemma {conflicting};

  n32 nof_variables_in_current_level {
    static_cast<n32>(std::count_if(lemma.Literals.begin(), lemma.Literals.end(),
    [this, current_level](literal const l) {return AssignmentLevels[l.Variable()] == current_level; }))
  };

  variable::index Cursor {Trail.size() - static_cast<variable::index>(1)};

  while (nof_variables_in_current_level > 1) {
    variable::index vi;
    literal::vector::iterator fres;

    while (Cursor >= static_cast<variable::index>(0)) {
      vi = {Trail[Cursor]};
      Cursor = Cursor - static_cast<variable::index>(1);
      fres = std::find_if(lemma.Literals.begin(), lemma.Literals.end(), [this, vi](literal const l) { return l.Variable() == vi; });
      if (fres != lemma.Literals.end()) {
        // variable is in the lemma
        goto foundlbl;
      }
    }
    throw;
    foundlbl:

    std::optional<clause::index> const ridx {Reasons[vi]};
    if (!ridx) throw;

    lemma.Literals.erase(fres);
    nof_variables_in_current_level--;

    clause const rsn {Clauses[ridx.value()]};
    for (literal const& lit : rsn.Literals) {
      if (lit.Variable() == vi) { continue; }
      if (std::find(lemma.Literals.begin(), lemma.Literals.end(), lit) != lemma.Literals.end()) {
        continue;
      }
      lemma.Literals.push_back(lit);
      if (AssignmentLevels[lit.Variable()] == current_level) {
        nof_variables_in_current_level++;
      }
    }
  }

  literal asserting;
  bool asserting_found {false};
  decision_level bt_tgt {0};

  for (literal const& l : lemma.Literals) {
    decision_level const curr_lvl {AssignmentLevels[l.Variable()].value_or(decision_level{0})};
    if (curr_lvl == current_level) {
      if (asserting_found) throw;
      asserting_found = true;
      asserting = l; continue;
    }
    if (curr_lvl > bt_tgt) { bt_tgt = curr_lvl; }
  }

  BacktrackTo(bt_tgt);
  std::sort(lemma.Literals.begin(), lemma.Literals.end(), [](auto const& lhs, auto const& rhs) { return lhs > rhs; });
  RegisterLearned(lemma);
  AssignValue(asserting.Variable(), asserting.EffectiveValue(variable::assignment::TRUE), Clauses.size() - static_cast<clause::index>(1));
}

void solver::RegisterWatcher(n32 const litraw, clause::index const ci) {
  Watchlists[litraw].push_back(ci);
}

void solver::RemoveWatcher(n32 const litraw, clause::index const ci) {
  auto& wl {Watchlists[litraw]};
  auto it = std::find(wl.begin(), wl.end(), ci);
  if (it != wl.end()) {
    wl.erase(it);
  }
}

std::optional<clause::index> solver::Propagate() {
  while (PropagationCursor < Trail.size()) {
    auto const index {Trail[PropagationCursor]};
    auto const trigger {Variables[index].Value == variable::assignment::TRUE ? literal::polarity::NEGATIVE : literal::polarity::POSITIVE };
    std::vector<clause::index> Watchlist {Watchlists[literal(index, trigger).Raw]};
    PropagationCursor = PropagationCursor + static_cast<variable::index>(1);
    std::size_t i {0};
    while (i < Watchlist.size()) {
      auto const clause_idx {Watchlist[i]};
      auto& cls {Clauses[clause_idx]};

      if (cls.Literals[static_cast<literal::index>(0)].false_in(Variables)) {
        auto const temp {cls.Literals[static_cast<literal::index>(0)]};
        cls.Literals[static_cast<literal::index>(0)] = cls.Literals[static_cast<literal::index>(1)];
        cls.Literals[static_cast<literal::index>(1)] = temp;
      }

      if (!cls.is_satisfied_in(Variables)) {
        bool found_new_watcher = false;
        for (literal::index j {2}; j < cls.Literals.size(); j = j + static_cast<literal::index>(1)) {
          auto const al {cls.Literals[j]};
          if (!al.false_in(Variables)) {
            RemoveWatcher(cls.Literals[static_cast<literal::index>(1)].Raw, clause_idx);
            
            auto const temp {cls.Literals[static_cast<literal::index>(1)]};
            cls.Literals[static_cast<literal::index>(1)] = cls.Literals[j];
            cls.Literals[j] = temp;
            
            RegisterWatcher(cls.Literals[static_cast<literal::index>(1)].Raw, clause_idx);
            found_new_watcher = true;
            break;
          }
        }
        if (found_new_watcher) {
          i++;
          continue;
        }

        if (cls.is_unsatisfied_in(Variables)) {
          PropagationCursor = Trail.size();
          return clause_idx;
        } else {
          auto const lit = cls.Literals[static_cast<literal::index>(0)];
          AssignValue(lit.Variable(), lit.EffectiveValue(variable::assignment::TRUE), clause_idx);
        }
      }
      i++;
    }
  }

  return std::nullopt;
}

void solver::ReadDIMACS_CNF(std::istream& is) {
  clause current_clause;
  std::string line;

  auto is_whitespace = [](char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\v' || c == '\f';
  };

  while (std::getline(is, line)) {
    std::string_view line_view = line;

    while (!line_view.empty() && is_whitespace(line_view.front())) {
      line_view.remove_prefix(1);
    }

    if (line_view.empty()) {
      continue;
    }

    if (line_view.front() == 'c') {
      continue;
    }

    if (line_view.front() == '%') {
      break;
    }

    if (line_view.starts_with("p cnf")) {
      std::string_view p_view = line_view.substr(5);
      while (!p_view.empty() && is_whitespace(p_view.front())) {
        p_view.remove_prefix(1);
      }
      int num_vars = 0;
      auto [ptr, ec] = std::from_chars(p_view.data(), p_view.data() + p_view.length(), num_vars);
      if (ec == std::errc{}) {
        for (int i = 1; i <= num_vars; ++i) {
          std::string idf = std::to_string(i);
          if (SymbolTable.find(idf) == SymbolTable.end()) {
            variable::index var_idx {Variables.size()};
            Variables.push_back(variable{.Value = variable::assignment::UNDEFINED});
            FreeVariables.insert(var_idx);
            Watchlists.push_back(std::vector<clause::index>());
            Watchlists.push_back(std::vector<clause::index>());
            Reasons.push_back(std::nullopt);
            AssignmentLevels.push_back(std::nullopt);
            SymbolTable[idf] = var_idx;
            IndexToIdentifier[var_idx] = idf;
          }
        }
      }
      continue;
    }

    std::size_t pos = 0;
    while (pos < line_view.length()) {
      while (pos < line_view.length() && is_whitespace(line_view[pos])) {
        pos++;
      }
      if (pos >= line_view.length()) {
        break;
      }

      std::size_t end = pos;
      while (end < line_view.length() && !is_whitespace(line_view[end])) {
        end++;
      }
      std::string_view token = line_view.substr(pos, end - pos);
      pos = end;

      if (token == "%") {
        return;
      }

      int literal_val = 0;
      auto [ptr, ec] = std::from_chars(token.data(), token.data() + token.length(), literal_val);
      if (ec == std::errc{}) {
        if (literal_val == 0) {
          RegisterClause(current_clause);
          current_clause = clause();
        } else {
          int identifier = std::abs(literal_val);
          std::string idf = std::to_string(identifier);
          
          variable::index var_idx;
          auto it = SymbolTable.find(idf);
          if (it != SymbolTable.end()) {
            var_idx = it->second;
          } else {
            var_idx = variable::index{Variables.size()};
            Variables.push_back(variable{.Value = variable::assignment::UNDEFINED});
            FreeVariables.insert(var_idx);
            Watchlists.push_back(std::vector<clause::index>());
            Watchlists.push_back(std::vector<clause::index>());
            Reasons.push_back(std::nullopt);
            AssignmentLevels.push_back(std::nullopt);
            SymbolTable[idf] = var_idx;
            IndexToIdentifier[var_idx] = idf;
          }

          literal::polarity pol = (literal_val > 0) ? literal::polarity::POSITIVE : literal::polarity::NEGATIVE;
          current_clause.Literals.push_back(literal(var_idx, pol));
        }
      }
    }
  }

  Statistics.VariableCount = Variables.size().value;
}

std::string solver::RenderClause(clause const& cls, logic const inlined) const {
  std::string prefix = "";
  if (!inlined) {
    if (cls.is_satisfied_in(Variables)) {
      prefix = "\033[32mSAT\033[0m";
    } else if (cls.is_unsatisfied_in(Variables)) {
      prefix = "\033[31mUST\033[0m";
    } else {
      prefix = "UNK";
    }
  }

  std::vector<std::string> rendered_literals;
  for (literal const& lit : cls.Literals) {
    std::string color_start = "";
    std::string color_end = "";
    auto const val = lit.ValueIn(Variables);
    if (val == literal::value::TRUE) {
      color_start = "\033[32m";
      color_end = "\033[0m";
    } else if (val == literal::value::FALSE) {
      color_start = "\033[31m";
      color_end = "\033[0m";
    }

    std::string const sym {IndexToIdentifier.find(lit.Variable())->second};
    std::string const lit_str = color_start + (lit.is_negative() ? "~" : "") + sym + color_end;
    rendered_literals.push_back(lit_str);
  }

  std::string clause_str = prefix + " ";
  for (std::size_t i = 0; i < rendered_literals.size(); ++i) {
    clause_str += rendered_literals[i];
    if (i + 1 < rendered_literals.size()) {
      clause_str += " v ";
    }
  }
  return clause_str;
}

void solver::Dump() const {
  for (clause::index i {0}; i < Clauses.size(); i = i + static_cast<clause::index>(1)) {
    std::println("{}", RenderClause(Clauses[i]));
  }
}

solver::conclusion solver::Search() {
  LearnedOffset = Clauses.size();

  while (true) {
    std::optional<clause::index> propagation_result = Propagate();
    if (propagation_result) {
      if (LevelSeparators.size() == decision_level{0}) {
        return conclusion::UNSATISFIABLE;
      }

      ResolveConflict(propagation_result.value());
    } else {
      if (FreeVariables.empty()) {
        return conclusion::SATISFIABLE;
      }

      variable::index pick;
      //std::sample(FreeVariables.begin(), FreeVariables.end(), &pick, 1, PRNG);
      pick = *FreeVariables.begin();

      PushLevel();
      AssignValue(pick, variable::assignment::FALSE, std::nullopt);
    }
  }

  return conclusion::INCONCLUSIVE;
}

void solver::AssignValue(variable::index const index, variable::assignment const assignment, std::optional<clause::index> const reason_idx) {
  Variables[index].Value = assignment;
  Reasons[index] = reason_idx;
  AssignmentLevels[index] = CurrentLevel();
  FreeVariables.erase(index);
  Trail.push_back(index);
}

void solver::PopLevel() {
  variable::index const target_index = LevelSeparators.pop_back();

  while (Trail.size() > target_index) {
    variable::index const var {Trail.pop_back()};
    Variables[var].Value = variable::assignment::UNDEFINED;
    Reasons[var] = std::nullopt;
    AssignmentLevels[var] = std::nullopt;
    FreeVariables.insert(var);
  }
}

void solver::BacktrackTo(decision_level const target) {
  while (CurrentLevel() > target) {
    PopLevel();
  }

  PropagationCursor = Trail.size();
}

}