#pragma once

#include <cstdint>
#include <vector>

#include "tcs/common/assert.hpp"
#include "tcs/common/bit.hpp"

namespace tcs::basic {
struct BitVector {
    static constexpr int64_t n_word_bits = common::n_machine_word_bits;
    int64_t size_ = 0;
    std::vector<uint64_t> data_;

    static uint64_t low_mask(int64_t len) {
        common::assert_or_throw(len >= 0 && len <= n_word_bits);
        return len == n_word_bits ? ~uint64_t{0} : (uint64_t{1} << len) - 1;
    }

    static BitVector create() { return {.size_ = 0, .data_ = {}}; }

    int64_t size() const { return size_; }

    void resize(int64_t new_size) {
        common::assert_or_throw(new_size >= 0);
        data_.resize((new_size + n_word_bits - 1) / n_word_bits, 0);
        if (new_size % n_word_bits != 0) {
            data_.back() &= low_mask(new_size % n_word_bits);
        }
        size_ = new_size;
    }

    bool load(int64_t index) const {
        common::assert_or_throw(index >= 0 && index < size_);
        return (data_[index / n_word_bits] >> (index % n_word_bits) & 1) == 1;
    }

    void store(int64_t index, bool value) {
        common::assert_or_throw(index >= 0 && index < size_);
        uint64_t& word = data_[index / n_word_bits];
        uint64_t mask = uint64_t{1} << (index % n_word_bits);
        word = value ? word | mask : word & ~mask;
    }

    uint64_t load(int64_t pos, int64_t len) const {
        common::assert_or_throw(pos >= 0 && len >= 0 && pos + len <= size_);
        common::assert_or_throw(len <= n_word_bits);
        if (len == 0) {
            return 0;
        }
        int64_t off = pos % n_word_bits;
        int64_t n_low = n_word_bits - off;
        uint64_t low = data_[pos / n_word_bits] >> off;
        if (len <= n_low) {
            return low & low_mask(len);
        }
        return (low & low_mask(n_low)) | (data_[(pos + len) / n_word_bits] & low_mask(len - n_low))
                                             << n_low;
    }

    void store(int64_t pos, int64_t len, uint64_t value) {
        common::assert_or_throw(pos >= 0 && len >= 0 && pos + len <= size_);
        common::assert_or_throw(len <= n_word_bits);
        common::assert_or_throw(std::bit_width(value) <= len);
        if (len == 0) {
            return;
        }
        int64_t off = pos % n_word_bits;
        int64_t n_low = n_word_bits - off;
        uint64_t& low_word = data_[pos / n_word_bits];
        if (len <= n_low) {
            low_word = (low_word & ~(low_mask(len) << off)) | (value << off);
        } else {
            low_word = ((low_word & low_mask(off)) | (value << off)) & low_mask(n_word_bits);
            uint64_t& high_word = data_[(pos + len) / n_word_bits];
            high_word = (high_word & ~low_mask(len - n_low)) | (value >> n_low);
        }
    }

    void push_back(bool value) {
        size_++;
        if (static_cast<int64_t>(data_.size()) * n_word_bits < size_) {
            data_.push_back(0);
        }
        common::assert_or_throw(static_cast<int64_t>(data_.size()) * n_word_bits >= size_);
        store(size_ - 1, value);
    }

    void pop_back() {
        common::assert_or_throw(size_ > 0);
        store(size_ - 1, false);
        size_--;
    }

    void push_back(uint64_t value, int64_t n_bits) {
        common::assert_or_throw(n_bits >= 0 && n_bits <= n_word_bits);
        size_ += n_bits;
        if (static_cast<int64_t>(data_.size()) * n_word_bits < size_) {
            data_.push_back(0);
        }
        common::assert_or_throw(static_cast<int64_t>(data_.size()) * n_word_bits >= size_);
        store(size_ - n_bits, n_bits, value);
    }

    void pop_back(int64_t n_bits) {
        common::assert_or_throw(n_bits >= 0 && n_bits <= n_word_bits);
        common::assert_or_throw(size_ >= n_bits);
        store(size_ - n_bits, n_bits, 0);
        size_ -= n_bits;
    }
};
}  // namespace tcs::basic
