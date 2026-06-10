#pragma once

#include <algorithm>
#include <cstdint>
#include <ranges>
#include <vector>

/// Element with a key for ordering and an index for stability verification.
struct IndexedElement {
    int64_t key;
    int64_t index;

    static int64_t proj(const IndexedElement& el) { return el.key; }
};

class TestArray {
   public:
    using iterator = std::vector<IndexedElement>::iterator;
    using const_iterator = std::vector<IndexedElement>::const_iterator;
    using value_type = IndexedElement;

    TestArray() = default;
    TestArray(std::vector<IndexedElement> data) : data_(std::move(data)) {}
    TestArray(int64_t size) : data_(size) {}
    template <std::ranges::input_range R>
        requires std::convertible_to<std::ranges::range_value_t<R>, IndexedElement>
    TestArray(R&& r) : data_(std::ranges::to<std::vector<IndexedElement>>(std::forward<R>(r))) {}

    auto begin() { return data_.begin(); }
    auto begin() const { return data_.begin(); }
    auto end() { return data_.end(); }
    auto end() const { return data_.end(); }
    int64_t size() const { return static_cast<int64_t>(data_.size()); }
    bool empty() const { return data_.empty(); }
    IndexedElement& operator[](int64_t i) { return data_[i]; }
    const IndexedElement& operator[](int64_t i) const { return data_[i]; }

    void iota_index() {
        for (int64_t i = 0; i < static_cast<int64_t>(data_.size()); i++) {
            data_[i].index = i;
        }
    }

    bool is_stable() const {
        auto sorted = data_;
        std::ranges::stable_sort(sorted, {}, IndexedElement::proj);
        for (int64_t i = 0; i < static_cast<int64_t>(sorted.size()) - 1; i++) {
            if (sorted[i].key == sorted[i + 1].key && sorted[i].index > sorted[i + 1].index) {
                return false;
            }
        }
        return true;
    }

   private:
    std::vector<IndexedElement> data_;
};
