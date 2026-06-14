#include <compare>
#include <vector>
#include <span>
#include <functional>

template<typename T>
struct typed_index {
  std::size_t value;

  typed_index() : value(0) {}
  explicit typed_index(std::size_t v) : value(v) {}

  constexpr auto operator<=>(typed_index<T> const&) const = default;
  constexpr bool operator>(typed_index const& other) const { return value > other.value; }
  constexpr bool operator>=(typed_index const& other) const { return value >= other.value; }
  constexpr bool operator==(typed_index const& other) const { return value == other.value; }
  constexpr typed_index<T> operator-(typed_index const& other) const { return typed_index<T>{value - other.value}; }
  constexpr typed_index<T> operator+(typed_index const& other) const { return typed_index<T>{value + other.value}; }
};

namespace std {
  template<typename T>
  struct hash<typed_index<T>> {
    std::size_t operator()(typed_index<T> const& idx) const noexcept {
      return std::hash<std::size_t>{}(idx.value);
    }
  };
}


template<typename T, typename Index>
struct typed_vector {
  using storage_type = std::vector<T>;

  using value_type = T;
  using iterator = typename storage_type::iterator;
  using const_iterator = typename storage_type::const_iterator;

  T& operator[](Index idx) {
    return data_[idx.value];
  }

  const T& operator[](Index idx) const {
    return data_[idx.value];
  }

  void push_back(const T& value) {
    data_.push_back(value);
  }

  T last() const {
    return data_[data_.size() - 1];
  }

  T pop_back() {
    T val = last();
    data_.pop_back();
    return val;
  }

  void erase(iterator it) {
    data_.erase(it);
  }

  iterator begin() {
    return data_.begin();
  }

  iterator end() {
    return data_.end();
  }

  const_iterator begin() const {
    return data_.begin();
  }

  const_iterator end() const {
    return data_.end();
  }

  const_iterator cbegin() const {
    return data_.cbegin();
  }

  const_iterator cend() const {
    return data_.cend();
  }

  using size_type = Index;

  size_type size() const {
    return size_type{data_.size()};
  }

  bool empty() const {
    return data_.empty();
  }

  T* data() noexcept {
    return data_.data();
  }

  const T* data() const noexcept {
    return data_.data();
  }

  operator std::span<T>() {
    return std::span<T>(data_.data(), data_.size());
  }

  operator std::span<const T>() const {
    return std::span<const T>(data_.data(), data_.size());
  }

private:
  storage_type data_;
};