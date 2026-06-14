#pragma once

#include <random>
#include <algorithm>
#include <istream>
#include <optional>
#include <span>
#include <vector>
#include <array>
#include <print>
#include <charconv>
#include <unordered_map>
#include <unordered_set>
#include <bitset>

#include "Types.hpp"
#include "TypedContainers.hpp"

namespace rocket::sat {
enum struct tri_state : i32 {
  FALSE     = -1,
  UNDEFINED =  0,
  TRUE      =  1,
};

constexpr tri_state operator~(tri_state ts) {
  return static_cast<tri_state>(
    static_cast<n32>(ts) * -1
  );
}

struct variable {
  using index = typed_index<variable>;
  using vector = typed_vector<variable, index>;
  using assignment = tri_state;

  assignment Value;
};

struct literal {
  using index = typed_index<literal>;
  using vector = typed_vector<literal, index>;
  using value = tri_state;

  enum struct polarity : n32 {
    NEGATIVE = 0,
    POSITIVE = 1,
  };

  literal() = default;
  literal(variable::index const i, polarity const p) : Raw((static_cast<n32>(i.value) << 1) + static_cast<n32>(p)) {}
  explicit literal(n32 const n) : Raw(n) {}

  variable::index Variable() const { return variable::index {Raw >> 1}; }
  polarity Polarity() const { return Raw & 1 ? literal::polarity::POSITIVE : literal::polarity::NEGATIVE; }
  
  bool operator==(literal other) const { return Raw == other.Raw; }
  bool operator!=(literal other) const { return Raw != other.Raw; }
  bool operator<(literal other) const { return Raw < other.Raw; }
  bool operator>(literal other) const { return Raw > other.Raw; }
  literal operator~() const { return literal(Raw ^ 1); }

  value ValueIn(variable::vector const& vec) const {
    variable::assignment const Value {vec[this->Variable()].Value};
    return this->Polarity() == literal::polarity::POSITIVE ? Value : ~Value;
  }

  logic false_in(variable::vector const& vec) const { return ValueIn(vec) == value::FALSE; }
  logic true_in(variable::vector const& vec) const { return ValueIn(vec) == value::TRUE; }
  logic undefined_in(variable::vector const& vec) const { return ValueIn(vec) == value::UNDEFINED; }

  logic is_positive() const { return this->Polarity() == literal::polarity::POSITIVE; }
  logic is_negative() const { return this->Polarity() == literal::polarity::NEGATIVE; }

  variable::assignment EffectiveValue(variable::assignment const desired) const { return is_positive() ? desired : ~desired; }

  n32 Raw {0};
};

struct clause {
  using index = typed_index<clause>;
  using vector = typed_vector<clause, index>;

  literal::vector Literals;

  clause() = default;

  explicit clause(literal::vector const& literals) {
    for (literal const& l : literals) {
      Literals.push_back(l);
    }
  }

  logic is_satisfied_in(variable::vector const& vec) const {
    return count_values(vec, literal::value::TRUE) > 0;
  }

  logic is_unsatisfied_in(variable::vector const& vec) const {
    return count_values(vec, literal::value::FALSE) == Literals.size().value;
  }

  logic is_unit_in(variable::vector const& vec) const {
    return count_values(vec, literal::value::UNDEFINED) == 1;
  }

  n32 count_values(variable::vector const& vec, literal::value target) const {
    n32 accumulator {0};
    for (literal const& l : Literals) {
      if (l.ValueIn(vec) == target) {
        accumulator++;
      }
    }
    return accumulator;
  }
};

struct solver {
  enum struct conclusion {
    UNSATISFIABLE = -1,
     INCONCLUSIVE =  0,
      SATISFIABLE =  1,
  };

  struct statistics {
    n32 ClauseCount {0};
    n32 LearnedCount {0};
    n32 VariableCount {0};
    n32 ConflictCount {0};
    n32 DecisionCount {0};
    n32 PropagationCount {0};
    n32 RestartCount{0};
  } Statistics;

  typed_vector<clause, clause::index> Clauses;
  clause::index LearnedOffset;
  
  typed_vector<variable::index, variable::index> Trail;
  using decision_level = typed_index<literal::index>;
  typed_vector<variable::index, decision_level> LevelSeparators;
  std::unordered_set<variable::index> FreeVariables;
  variable::index PropagationCursor;
  variable::vector Variables;
  typed_vector<std::optional<clause::index>, variable::index> Reasons;
  typed_vector<std::optional<decision_level>, variable::index> AssignmentLevels;

  std::vector<std::vector<clause::index>> Watchlists;

  std::unordered_map<std::string, variable::index> SymbolTable;
  std::unordered_map<variable::index, std::string> IndexToIdentifier;

  std::mt19937 PRNG;

  explicit solver(unsigned int const seed = std::mt19937::default_seed) {
    PRNG.seed(seed);
  }

  void RegisterClause(clause const&);
  void RegisterLearned(clause const&);

  void ResolveConflict(clause::index const);
  void RegisterWatcher(n32 const, clause::index const);
  void RemoveWatcher(n32 const, clause::index const);
  std::optional<clause::index> Propagate();

  void ReadDIMACS_CNF(std::istream&);

  conclusion Search();

  std::string RenderClause(clause const& cls, logic const inlined = true) const;
  void Dump() const;

  void AssignValue(variable::index const, variable::assignment const, std::optional<clause::index> const);

  decision_level CurrentLevel() const { return LevelSeparators.size(); }
  void PushLevel() { Trail.empty() ? LevelSeparators.push_back(variable::index {0}) : LevelSeparators.push_back(Trail.size()) ; }
  void PopLevel();
  void BacktrackTo(decision_level const);
};
}