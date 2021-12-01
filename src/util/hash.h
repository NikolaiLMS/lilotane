
#ifndef DOMPASCH_TREE_REXX_HASH_H
#define DOMPASCH_TREE_REXX_HASH_H

template <class T>
inline void hash_combine(std::size_t & s, const T & v)
{
  static robin_hood::hash<T> h;
  s ^= h(v) + 0x9e3779b9 + (s<< 6) + (s>> 2);
}

static unsigned const int primes [] = {2038072819, 2038073287,    2038073761,    2038074317,
        2038072823,    2038073321,    2038073767,    2038074319,
        2038072847,    2038073341,    2038073789,    2038074329,
        2038074751,    2038075231,    2038075751, 2038076267};

inline void hash_combine_commutative(std::size_t & s, const size_t & v)
{
  s ^= v * primes[std::abs((int(v)^3) & 15)];
}


#endif