#pragma once

#include <cstdint>
#include <format>
#include <memory>
#include <source_location>
#include <stdexcept>
#include <string_view>
#include <tuple>

namespace tcs {
namespace linked_list {
inline void assert_or_throw(bool condition, std::string_view message = "empty message",
    const std::source_location& loc = std::source_location::current()) {
    if (!condition) [[unlikely]] {
        throw std::runtime_error(
            std::format("Assertion failed at {}:{}: {}", loc.file_name(), loc.line(), message));
    }
}

template <typename T>
struct LinkedList {
    struct NodeBase {
        NodeBase* next = nullptr;
        NodeBase* prev = nullptr;

        virtual ~NodeBase() = default;

        static void link(NodeBase* a, NodeBase* b) {
            a->next = b;
            b->prev = a;
        }
    };
    struct Node : NodeBase {
        T value;
    };

    std::unique_ptr<NodeBase> head;
    std::unique_ptr<NodeBase> tail;

    struct Iterator {
        using difference_type = int64_t;
        using value_type = T;
        using iterator_category = std::bidirectional_iterator_tag;
        using iterator_concept = std::bidirectional_iterator_tag;

        NodeBase* ptr;
        auto operator*(this auto&& self) { return static_cast<Node*>(self.ptr)->value; }
        auto operator->(this auto&& self) { return &static_cast<Node*>(self.ptr)->value; }
        Iterator& operator++() {
            ptr = ptr->next;
            return *this;
        }
        Iterator operator++(int) {
            Iterator tmp = *this;
            ++*this;
            return tmp;
        }
        Iterator& operator--() {
            ptr = ptr->prev;
            return *this;
        }
        Iterator operator--(int) {
            Iterator tmp = *this;
            --*this;
            return tmp;
        }
        bool operator==(const Iterator& other) const { return ptr == other.ptr; }
        bool operator!=(const Iterator& other) const { return ptr != other.ptr; }
    };

    LinkedList() : head(std::make_unique<NodeBase>()), tail(std::make_unique<NodeBase>()) {
        head->next = tail.get();
        tail->prev = head.get();
    }
    LinkedList(const LinkedList& other) = delete;
    LinkedList(LinkedList&& other) noexcept
        : head(std::move(other.head)), tail(std::move(other.tail)) {
        other.head = std::make_unique<NodeBase>();
        other.tail = std::make_unique<NodeBase>();
        other.head->next = other.tail.get();
        other.tail->prev = other.head.get();
    }
    LinkedList& operator=(const LinkedList& other) = delete;
    LinkedList& operator=(LinkedList&& other) noexcept {
        if (this != &other) {
            head = std::move(other.head);
            tail = std::move(other.tail);
            other.head = std::make_unique<NodeBase>();
            other.tail = std::make_unique<NodeBase>();
            other.head->next = other.tail.get();
            other.tail->prev = other.head.get();
        }
        return *this;
    }
    ~LinkedList() {
        while (!empty()) {
            erase(begin());
        }
    }

    Iterator begin() const { return Iterator{head->next}; }
    Iterator end() const { return Iterator{tail.get()}; }

    [[nodiscard]] bool empty() const { return head->next == tail.get(); }

    Iterator insert(Iterator it, const T& value) {
        auto* node = new Node;
        node->value = value;
        NodeBase::link(it.ptr->prev, node);
        NodeBase::link(node, it.ptr);
        return Iterator{node};
    }

    Iterator erase(Iterator it) {
        NodeBase* node = it.ptr;
        NodeBase* nxt = node->next;
        NodeBase::link(node->prev, nxt);
        delete node;
        return Iterator{nxt};
    }

    void push_back(const T& value) { insert(end(), value); }
    void push_front(const T& value) { insert(begin(), value); }
    void pop_back() { erase(std::prev(end())); }
    void pop_front() { erase(begin()); }

    int64_t size() const { return std::distance(begin(), end()); }
    static std::tuple<LinkedList, LinkedList> split(LinkedList list, Iterator it) {
        LinkedList right;
        if (it != list.end()) {
            auto begin_prev = std::prev(it);
            auto end_prev = std::prev(list.end());
            NodeBase::link(begin_prev.ptr, list.end().ptr);
            NodeBase::link(right.head.get(), it.ptr);
            NodeBase::link(end_prev.ptr, right.tail.get());
        }
        return std::make_tuple(std::move(list), std::move(right));
    }
    static LinkedList concat(LinkedList left, LinkedList right) {
        if (!right.empty()) {
            NodeBase::link(left.tail->prev, right.head->next);
            NodeBase::link(right.tail->prev, left.tail.get());
            NodeBase::link(right.head.get(), right.tail.get());
        }
        return left;
    }
};
}  // namespace linked_list
}  // namespace tcs
