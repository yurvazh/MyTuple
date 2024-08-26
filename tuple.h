//Created by Yury Vazhenin


#include <iostream>
#include <type_traits>
#define FWD(other) std::forward<decltype(other)>(other)

namespace detail {

    template <typename T>
    auto test(T x) -> std::true_type;

    template <typename T>
    auto test(...) -> std::false_type;
}  // namespace detail

template <typename T>
struct is_initialized_by_empty_list : decltype(detail::test<T>()) {};

template <typename... Types>
class Tuple;

template <typename... Types>
struct Ti;

template <typename T, typename Head, typename... Args>
constexpr int count_matches() {
    if constexpr (sizeof...(Args) == 0) {
        return static_cast<int>(std::is_same_v<T, Head>);
    } else {
        return static_cast<int>(std::is_same_v<T, Head>) + count_matches<T, Args...>();
    }
}

template <typename T, typename Head, typename... Args>
constexpr size_t find_place() {
    if constexpr (std::is_same_v<T, Head>) {
        return 0;
    } else {
        return find_place<T, Args...>() + 1;
    }
}

template <size_t N, typename... Args>
auto& get(Tuple<Args...>& t) {
    if constexpr (N == 0) {
        return t.head;
    } else {
        return FWD(get<N - 1>(t.tail));
    }
}

template <size_t N, typename... Args>
const auto& get(const Tuple<Args...>& t) {
    if constexpr (N == 0) {
        return t.head;
    } else {
        return FWD(get<N - 1>(t.tail));
    }
}

template <size_t N, typename... Args>
auto&& get(Tuple<Args...>&& t) {
    if constexpr (N == 0) {
        return FWD(t.head);
    } else {
        return FWD(get<N - 1>(std::move(t.tail)));
    }
}

template <size_t N, typename... Args>
const auto&& get(const Tuple<Args...>&& t) {
    if constexpr (N == 0) {
        return FWD(t.head);
    } else {
        return FWD(get<N - 1>(std::move(t.tail)));
    }
}

template <typename T, typename... Args>
requires(count_matches<T, Args...>() == 1) T& get(Tuple<Args...>& t) {
    return get<find_place<T, Args...>()>(t);
}

template <typename T, typename... Args>
requires(count_matches<T, Args...>() ==
         1) const T& get(const Tuple<Args...>& t) {
    return get<find_place<T, Args...>()>(t);
}

template <typename T, typename... Args>
requires(count_matches<T, Args...>() == 1) T&& get(Tuple<Args...>&& t) {
    return std::move(get<find_place<T, Args...>()>(std::move(t)));
}

template <typename T, typename... Args>
requires(count_matches<T, Args...>() ==
         1) const T&& get(const Tuple<Args...>&& t) {
    return std::move(get<find_place<T, Args...>()>(std::move(t)));
}

template <size_t I, typename... Args>
struct type_i;

template <size_t I, typename Head, typename... Args>
struct type_i<I, Head, Args...> {
    using right_type = typename type_i<I - 1, Args...>::right_type;
};

template <typename Head, typename... Args>
struct type_i<0, Head, Args...> {
    using right_type = Head;
};

template <size_t I, typename OtherTuple>
struct get_i {
    using other_type = decltype(get<I>(std::declval<OtherTuple>()));
};

template <size_t I, size_t N, typename OtherTuple, typename Head,
        typename... Args>
constexpr bool constructible_helper() {
    if constexpr (I == N) {
        return true;
    } else {
        return std::is_constructible_v<
                typename type_i<I, Head, Args...>::right_type,
                typename get_i<I, OtherTuple>::other_type> &&
               constructible_helper<I + 1, N, OtherTuple, Head, Args...>();
    }
}

template <size_t I, size_t N, typename OtherTuple, typename Head,
        typename... Args>
constexpr bool convertible_helper() {
    if constexpr (I == N) {
        return true;
    } else {
        return std::is_convertible_v<
                typename get_i<I, OtherTuple>::other_type,
                typename type_i<I, Head, Args...>::right_type> &&
               convertible_helper<I + 1, N, OtherTuple, Head, Args...>();
    }
}

template <typename Head, typename... Types>
class Tuple<Head, Types...> {
private:
    Head head;
    Tuple<Types...> tail;

public:
    template <typename = void>
    requires std::conjunction_v<
            std::is_default_constructible<Head>,
            std::is_default_constructible<
                    Types>...> explicit(!std::
    conjunction_v<
            is_initialized_by_empty_list<Head>,
            is_initialized_by_empty_list<Types>...>)
    Tuple()
            : head(), tail() {}

    template <typename = void>
    requires std::conjunction_v<
            std::is_copy_constructible<Head>,
            std::is_copy_constructible<
                    Types>...> explicit(!std::
    conjunction_v<
            std::is_convertible<const Head&, Head>,
            std::is_convertible<const Types&,
                    Types>...>)
    Tuple(const Head& head_, const Types&... ts)
            : head(head_), tail(ts...) {}

    template <typename FirstArg, typename... UTypes>
    requires(
            (sizeof...(UTypes) == sizeof...(Types)) &&
            std::conjunction_v<
                    std::is_constructible<Head, FirstArg>,
                    std::is_constructible<
                            Types,
                            UTypes>...>) explicit(!std::
    conjunction_v<
            std::is_convertible<FirstArg, Head>,
            std::is_convertible<UTypes,
                    Types>...>)
    Tuple(FirstArg&& first_arg, UTypes&&... other_args)
            : head(std::forward<FirstArg>(first_arg)),
              tail(std::forward<UTypes>(other_args)...) {}

    template <typename FirstArg, typename... UTypes>
    requires(sizeof...(UTypes) == sizeof...(Types)) &&
            (constructible_helper<0, (sizeof...(UTypes)) + 1,
                    const Tuple<FirstArg, UTypes...>&, Head,
                    Types...>()) &&
            ((sizeof...(Types) != 0) ||
             (!std::is_constructible_v<Head, const Tuple<FirstArg>&> &&
              !std::is_convertible_v<const Tuple<FirstArg>&, Head> &&
              !std::is_same_v<
                      Head,
                      FirstArg>)) explicit(!convertible_helper<0, (sizeof...(Types)) + 1,
            const Tuple<FirstArg,
                    UTypes...>&,
            Head, Types...>())
    Tuple(const Tuple<FirstArg, UTypes...>& other)
            : head(get<0>(other)),
              tail(other.tail) {}

    template <typename FirstArg, typename... UTypes>
    requires(sizeof...(UTypes) == sizeof...(Types)) &&
            (constructible_helper<0, (sizeof...(UTypes)) + 1,
                    Tuple<FirstArg, UTypes...>&&, Head, Types...>()) &&
            ((sizeof...(Types) != 0) ||
             (!std::is_constructible_v<Head, Tuple<FirstArg>&&> &&
              !std::is_convertible_v<Tuple<FirstArg>&&, Head> &&
              !std::is_same_v<Head, FirstArg>)) explicit(!convertible_helper<0, (sizeof...(Types)) + 1,
            Tuple<FirstArg, UTypes...>&&,
            Head, Types...>())
    Tuple(Tuple<FirstArg, UTypes...>&& other) noexcept(std::conjunction_v<std::is_nothrow_move_constructible<Head>,
            std::is_nothrow_move_constructible<Types>...>)
            : head(get<0>(std::move(other))),
              tail(std::move(other.tail)) {}

    template <typename T1, typename T2>
    requires(sizeof...(Types) == 1) &&
            std::is_constructible_v<Head, T1>&& std::is_constructible_v<
            Types..., T2> Tuple(const std::pair<T1, T2>& other)
            : head(other.first),
              tail(other.second) {}

    template <typename T1, typename T2>
    requires(sizeof...(Types) == 1) &&
            std::is_constructible_v<Head, T1>&& std::is_constructible_v<
            Types..., T2> Tuple(std::pair<T1, T2>&& other)
            : head(std::move(other.first)),
              tail(std::move(other.second)) {}

    Tuple(const Tuple& other) requires std::conjunction_v<
            std::is_copy_constructible<Head>, std::is_copy_constructible<Types>...>
            : head(other.head), tail(other.tail) {}

    Tuple(Tuple&& other) noexcept(std::conjunction_v<std::is_nothrow_move_constructible<Head>,
            std::is_nothrow_move_constructible<Types>...>)
            : head(std::move(other.head)), tail(std::move(other.tail)) {}

    Tuple& operator=(const Tuple& other) requires std::conjunction_v<
            std::is_copy_assignable<Head>, std::is_copy_assignable<Types>...> {
        if (this == &other) {
            return *this;
        }
        head = other.head;
        tail = other.tail;
        return *this;
    }

    Tuple& operator=(Tuple&& other)
    requires std::conjunction_v<
            std::is_move_assignable<Head>, std::is_move_assignable<Types>...> {
        if (this == &other) {
            return *this;
        }
        head = std::move(other.head);
        tail = std::move(other.tail);
        return *this;
    }

    template <typename OtherHead, typename... OtherTypes>
    requires((sizeof...(OtherTypes) == sizeof...(Types)) &&
             std::conjunction_v<std::is_assignable<Head&, const OtherHead&>,
                     std::is_assignable<Types&, const OtherTypes&>...>)
    Tuple&
    operator=(const Tuple<OtherHead, OtherTypes...>& other) {
        head = other.head;
        tail = other.tail;
        return *this;
    }

    template <typename OtherHead, typename... OtherTypes>
    requires((sizeof...(OtherTypes) == sizeof...(Types)) &&
             std::conjunction_v<std::is_assignable<Head&, OtherHead>,
                     std::is_assignable<Types&, OtherTypes>...>) Tuple&
    operator=(Tuple<OtherHead, OtherTypes...>&& other) {
        head = get<0>(std::move(other));
        tail = std::move(other.tail);
        return *this;
    }

    template <typename... Args>
    friend class Tuple;

    template <size_t N, typename... Args>
    friend auto& get(Tuple<Args...>&);

    template <size_t N, typename... Args>
    friend const auto& get(const Tuple<Args...>&);

    template <size_t N, typename... Args>
    friend auto&& get(Tuple<Args...>&&);

    template <size_t N, typename... Args>
    friend const auto&& get(const Tuple<Args...>&&);

    template <typename T, typename... Args>
    friend auto& get(Tuple<Args...>&);

    template <typename T, typename... Args>
    friend const auto& get(const Tuple<Args...>&);

    template <typename T, typename... Args>
    friend auto&& get(Tuple<Args...>&&);

    template <typename T, typename... Args>
    friend const auto&& get(const Tuple<Args...>&&);
};

template <typename T1, typename T2>
Tuple(const std::pair<T1, T2>&) -> Tuple<T1, T2>;

template <typename T1, typename T2>
Tuple(std::pair<T1, T2> &&) -> Tuple<T1, T2>;

template <>
class Tuple<> {
public:
    Tuple() = default;
    Tuple(const Tuple&) = default;
    Tuple(Tuple&&) noexcept = default;

    Tuple& operator=(const Tuple&) { return *this; }
    Tuple& operator=(Tuple&&) { return *this; }
};

template <typename... Args>
Tuple<std::decay_t<Args>...> makeTuple(Args&&... args) {
    return Tuple<std::decay_t<Args>...>(std::forward<Args>(args)...);
}

template <typename... Args>
Tuple<Args&...> tie(Args&... args) {
    return {args...};
}

template <typename... Args>
Tuple<Args&&...> forwardAsTuple(Args&&... args) {
    return {std::forward<Args>(args)...};
}

namespace tupleCatDetail {
    template <typename, typename>
    struct ConcatIndexSequence;

    template <size_t... I1, size_t... I2>
    struct ConcatIndexSequence<std::index_sequence<I1...>,
            std::index_sequence<I2...>> {
        using type = std::index_sequence<I1..., I2...>;
    };

    template <typename S1, typename S2>
    using ConcatIndexSequence_t = typename ConcatIndexSequence<S1, S2>::type;

    template <size_t N, size_t Count, size_t... Is>
    struct GenerateRepeatedIndexSequence
            : GenerateRepeatedIndexSequence<N, Count - 1, N, Is...> {};

    template <size_t N, size_t... Is>
    struct GenerateRepeatedIndexSequence<N, 0, Is...> {
        using type = std::index_sequence<Is...>;
    };

    template <size_t N, size_t Count>
    using GenerateRepeatedIndexSequence_t =
    typename GenerateRepeatedIndexSequence<N, Count>::type;

    template <typename... Args>
    struct sizeHelper;

    template <typename... Args>
    struct sizeHelper<Tuple<Args...>> {
        static const size_t count = sizeof...(Args);
    };

    template <typename... Other>
    struct ElemNumberSequence {
        using sequence = std::index_sequence<>;
    };

    template <typename Head, typename... Other>
    struct ElemNumberSequence<Head, Other...> {
        using sequence =
        ConcatIndexSequence_t<std::make_index_sequence<sizeHelper<Head>::count>,
                typename ElemNumberSequence<Other...>::sequence>;
    };

    template <typename... Tuples>
    using ElemNumberSequence_t = typename ElemNumberSequence<Tuples...>::sequence;

    template <size_t Index, typename... Tuples>
    struct TupleIndexSequence {
        using sequence = std::index_sequence<>;
    };

    template <size_t Index, typename Tuple, typename... Other>
    struct TupleIndexSequence<Index, Tuple, Other...> {
        using current =
        GenerateRepeatedIndexSequence_t<Index, sizeHelper<Tuple>::count>;
        using next = typename TupleIndexSequence<Index + 1, Other...>::sequence;
        using sequence = ConcatIndexSequence_t<current, next>;
    };

    template <typename... Tuples>
    using TupleIndexSequence_t =
    typename TupleIndexSequence<0, Tuples...>::sequence;
}  // namespace tupleCatDetail

template <typename TupleOfTuples, size_t... TupleIndex, size_t... ElemIndex>
auto forming_tuple(TupleOfTuples&& tuple_of_tuples,
                   std::index_sequence<TupleIndex...>,
                   std::index_sequence<ElemIndex...>) {
    return makeTuple(
            FWD(get<ElemIndex>(FWD(get<TupleIndex>(FWD(tuple_of_tuples)))))...);
}

template <typename... Tuples>
auto tupleCat(Tuples&&... tuples) {
    using TupleIndex =
    tupleCatDetail::TupleIndexSequence_t<std::decay_t<Tuples>...>;
    using ElemNumber =
    tupleCatDetail::ElemNumberSequence_t<std::decay_t<Tuples>...>;
    return forming_tuple(Tuple<Tuples&&...>(std::forward<Tuples>(tuples)...),
                         TupleIndex{}, ElemNumber{});
}
