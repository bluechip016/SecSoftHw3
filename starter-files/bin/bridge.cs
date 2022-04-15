// Dafny program bridge.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.5.0.40314
// Command Line Options: /Users/warmearthling/Desktop/SecSoftHw3/starter-files/bridge.dfy /verifyAllModules /compile:1 /spillTargetCode:1 /out:bin/bridge
// bridge.dfy


module Bridge {
  datatype Next_Car = A | B | Both | Neither

  datatype Traffic_Light = Red | Green

  datatype state = State(LightA: Traffic_Light, LightB: Traffic_Light, W_A: int, W_B: int, Cross_Counter: int)

  predicate method Valid(s: state)
    decreases s
  {
    if s.LightA == Green && s.LightB == Green then
      false
    else
      true
  }

  method Init() returns (s: state)
    ensures Valid(s)
    ensures s.LightA == Red && s.LightB == Red && s.W_A == 0 && s.W_B == 0 && s.Cross_Counter == 0
  {
    s := State(Red, Red, 0, 0, 0);
  }

  method Increment_W_A(s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases s
  {
    s' := s.(W_A := s.W_A + 1);
  }

  method Increment_W_B(s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases s
  {
    s' := s.(W_B := s.W_B + 1);
  }

  method Increment_Cross_Counter(s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases s
  {
    s' := s.(Cross_Counter := s.Cross_Counter + 1);
  }

  method Reset_Cross_Counter(s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases s
  {
    s' := s.(Cross_Counter := 0);
  }

  method Cross(s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases s
  {
    s' := s;
    if s.LightA.Green? {
      s' := s'.(W_A := s'.W_A - 1);
      s' := Increment_Cross_Counter(s');
    } else {
      s' := s'.(W_B := s'.W_B - 1);
      s' := Increment_Cross_Counter(s');
    }
  }

  method Switch_Lights(s: state) returns (s': state)
    requires Valid(s)
    requires !(s.LightA == Red && s.LightB == Red)
    ensures !(s.LightA == Green && s.LightB == Green)
    ensures Valid(s')
    decreases s
  {
    s' := s;
    if s'.LightA.Red? {
      s' := s'.(LightA := Green);
    } else {
      s' := s'.(LightA := Red);
    }
    if s'.LightB.Red? {
      s' := s'.(LightB := Green);
    } else {
      s' := s'.(LightB := Red);
    }
  }

  method Tick(next: Next_Car, s: state) returns (s': state)
    requires Valid(s)
    ensures Valid(s')
    decreases next, s
  {
    s' := s;
    match next {
      case {:split false} A() =>
        s' := Increment_W_A(s');
      case {:split false} B() =>
        s' := Increment_W_B(s');
      case {:split false} Both() =>
        s' := Increment_W_A(s');
        s' := Increment_W_B(s');
      case {:split false} Neither() =>
        s' := s';
    }
    if (s'.W_A == 0 || s'.W_B == 0) && !(s'.W_A == 0 && s'.W_B == 0) {
      s' := Reset_Cross_Counter(s');
      if s'.W_A > 0 {
        if s'.LightA.Red? {
          s' := s'.(LightA := Green, LightB := Red);
        }
        s' := s'.(W_A := s'.W_A - 1);
        s' := Increment_Cross_Counter(s');
      } else {
        if s'.LightB.Red? {
          s' := s'.(LightA := Red, LightB := Green);
        }
        s' := s'.(W_B := s'.W_B - 1);
        s' := Increment_Cross_Counter(s');
      }
    } else if s'.W_A > 0 || s'.W_B > 0 {
      if s'.LightA.Red? && s'.LightB.Red? {
        s' := s'.(LightA := Green);
        s' := s'.(W_A := s'.W_A - 1);
        s' := Increment_Cross_Counter(s');
      } else {
        if s'.Cross_Counter < 5 {
          s' := Cross(s');
        } else {
          s' := Switch_Lights(s');
          s' := Reset_Cross_Counter(s');
          s' := Cross(s');
        }
      }
    }
  }
}
")]

//-----------------------------------------------------------------------------
//
// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT
//
//-----------------------------------------------------------------------------

#if ISDAFNYRUNTIMELIB
using System; // for Func
using System.Numerics;
#endif

namespace DafnyAssembly {
  [AttributeUsage(AttributeTargets.Assembly)]
  public class DafnySourceAttribute : Attribute {
    public readonly string dafnySourceText;
    public DafnySourceAttribute(string txt) { dafnySourceText = txt; }
  }
}

namespace Dafny {
  using System.Collections.Generic;
  using System.Collections.Immutable;
  using System.Linq;

  public interface ISet<out T> {
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<ISet<T>> AllSubsets { get; }
    bool Contains<G>(G t);
    bool EqualsAux(ISet<object> other);
    ISet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class Set<T> : ISet<T> {
    readonly ImmutableHashSet<T> setImpl;
    readonly bool containsNull;
    Set(ImmutableHashSet<T> d, bool containsNull) {
      this.setImpl = d;
      this.containsNull = containsNull;
    }

    public static readonly ISet<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty, false);

    private static readonly TypeDescriptor<ISet<T>> _TYPE = new Dafny.TypeDescriptor<ISet<T>>(Empty);
    public static TypeDescriptor<ISet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISet<T> FromElements(params T[] values) {
      return FromCollection(values);
    }

    public static Set<T> FromISet(ISet<T> s) {
      return s as Set<T> ?? FromCollection(s.Elements);
    }

    public static Set<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public static ISet<T> FromCollectionPlusOne(IEnumerable<T> values, T oneMoreValue) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      var containsNull = false;
      if (oneMoreValue == null) {
        containsNull = true;
      } else {
        d.Add(oneMoreValue);
      }

      foreach (T t in values) {
        if (t == null) {
          containsNull = true;
        } else {
          d.Add(t);
        }
      }

      return new Set<T>(d.ToImmutable(), containsNull);
    }

    public ISet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISet<U> th) {
        return th;
      } else {
        var d = ImmutableHashSet<U>.Empty.ToBuilder();
        foreach (var t in this.setImpl) {
          var u = converter(t);
          d.Add(u);
        }

        return new Set<U>(d.ToImmutable(), this.containsNull);
      }
    }

    public int Count {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public long LongCount {
      get { return this.setImpl.Count + (containsNull ? 1 : 0); }
    }

    public IEnumerable<T> Elements {
      get {
        if (containsNull) {
          yield return default(T);
        }

        foreach (var t in this.setImpl) {
          yield return t;
        }
      }
    }

    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".
    /// </summary>
    public IEnumerable<ISet<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list, but don't include null
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          // yield both the subset without null and, if null is in the original set, the subset with null included
          var ihs = s.ToImmutable();
          yield return new Set<T>(ihs, false);
          if (containsNull) {
            yield return new Set<T>(ihs, true);
          }

          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }

          if (i == n) {
            // we have cycled through all the subsets
            break;
          }

          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }

    public bool Equals(ISet<T> other) {
      if (other == null || Count != other.Count) {
        return false;
      } else if (this == other) {
        return true;
      }

      foreach (var elmt in Elements) {
        if (!other.Contains(elmt)) {
          return false;
        }
      }

      return true;
    }

    public override bool Equals(object other) {
      if (other is ISet<T>) {
        return Equals((ISet<T>)other);
      }

      var th = this as ISet<object>;
      var oth = other as ISet<object>;
      if (th != null && oth != null) {
        // We'd like to obtain the more specific type parameter U for oth's type ISet<U>.
        // We do that by making a dynamically dispatched call, like:
        //     oth.Equals(this)
        // The hope is then that its comparison "this is ISet<U>" (that is, the first "if" test
        // above, but in the call "oth.Equals(this)") will be true and the non-virtual Equals
        // can be called. However, such a recursive call to "oth.Equals(this)" could turn
        // into infinite recursion. Therefore, we instead call "oth.EqualsAux(this)", which
        // performs the desired type test, but doesn't recurse any further.
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(ISet<object> other) {
      var s = other as ISet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (containsNull) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(default(T)) + 3);
      }

      foreach (var t in this.setImpl) {
        hashCode = hashCode * (Dafny.Helpers.GetHashCode(t) + 3);
      }

      return hashCode;
    }

    public override string ToString() {
      var s = "{";
      var sep = "";
      if (containsNull) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }

      foreach (var t in this.setImpl) {
        s += sep + Dafny.Helpers.ToString(t);
        sep = ", ";
      }

      return s + "}";
    }
    public static bool IsProperSubsetOf(ISet<T> th, ISet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(ISet<T> th, ISet<T> other) {
      if (other.Count < th.Count) {
        return false;
      }
      foreach (T t in th.Elements) {
        if (!other.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(ISet<T> th, ISet<T> other) {
      ISet<T> a, b;
      if (th.Count < other.Count) {
        a = th; b = other;
      } else {
        a = other; b = th;
      }
      foreach (T t in a.Elements) {
        if (b.Contains(t)) {
          return false;
        }
      }
      return true;
    }
    public bool Contains<G>(G t) {
      return t == null ? containsNull : t is T && this.setImpl.Contains((T)(object)t);
    }
    public static ISet<T> Union(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Union(b.setImpl), a.containsNull || b.containsNull);
    }
    public static ISet<T> Intersect(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Intersect(b.setImpl), a.containsNull && b.containsNull);
    }
    public static ISet<T> Difference(ISet<T> th, ISet<T> other) {
      var a = FromISet(th);
      var b = FromISet(other);
      return new Set<T>(a.setImpl.Except(b.setImpl), a.containsNull && !b.containsNull);
    }
  }

  public interface IMultiSet<out T> {
    bool IsEmpty { get; }
    int Count { get; }
    long LongCount { get; }
    IEnumerable<T> Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    bool Contains<G>(G t);
    BigInteger Select<G>(G t);
    IMultiSet<T> Update<G>(G t, BigInteger i);
    bool EqualsAux(IMultiSet<object> other);
    IMultiSet<U> DowncastClone<U>(Func<T, U> converter);
  }

  public class MultiSet<T> : IMultiSet<T> {
    readonly ImmutableDictionary<T, BigInteger> dict;
    readonly BigInteger occurrencesOfNull;  // stupidly, a Dictionary in .NET cannot use "null" as a key
    MultiSet(ImmutableDictionary<T, BigInteger>.Builder d, BigInteger occurrencesOfNull) {
      dict = d.ToImmutable();
      this.occurrencesOfNull = occurrencesOfNull;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, BigInteger>.Empty.ToBuilder(), BigInteger.Zero);

    private static readonly TypeDescriptor<IMultiSet<T>> _TYPE = new Dafny.TypeDescriptor<IMultiSet<T>>(Empty);
    public static TypeDescriptor<IMultiSet<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static MultiSet<T> FromIMultiSet(IMultiSet<T> s) {
      return s as MultiSet<T> ?? FromCollection(s.Elements);
    }
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t, out i)) {
            i = BigInteger.Zero;
          }
          d[t] = i + 1;
        }
      }
      return new MultiSet<T>(d, occurrencesOfNull);
    }

    public static MultiSet<T> FromCollection(IEnumerable<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }

    public static MultiSet<T> FromSeq(ISequence<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var occurrencesOfNull = BigInteger.Zero;
      foreach (T t in values.Elements) {
        if (t == null) {
          occurrencesOfNull++;
        } else {
          BigInteger i;
          if (!d.TryGetValue(t,
            out i)) {
            i = BigInteger.Zero;
          }

          d[t] = i + 1;
        }
      }

      return new MultiSet<T>(d,
        occurrencesOfNull);
    }
    public static MultiSet<T> FromSet(ISet<T> values) {
      var d = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      var containsNull = false;
      foreach (T t in values.Elements) {
        if (t == null) {
          containsNull = true;
        } else {
          d[t] = BigInteger.One;
        }
      }
      return new MultiSet<T>(d, containsNull ? BigInteger.One : BigInteger.Zero);
    }
    public IMultiSet<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is IMultiSet<U> th) {
        return th;
      } else {
        var d = ImmutableDictionary<U, BigInteger>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = converter(item.Key);
          d.Add(k, item.Value);
        }
        return new MultiSet<U>(d, this.occurrencesOfNull);
      }
    }

    public bool Equals(IMultiSet<T> other) {
      return IsSubsetOf(this, other) && IsSubsetOf(other, this);
    }
    public override bool Equals(object other) {
      if (other is IMultiSet<T>) {
        return Equals((IMultiSet<T>)other);
      }
      var th = this as IMultiSet<object>;
      var oth = other as IMultiSet<object>;
      if (th != null && oth != null) {
        // See comment in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }

    public bool EqualsAux(IMultiSet<object> other) {
      var s = other as IMultiSet<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (occurrencesOfNull > 0) {
        var key = Dafny.Helpers.GetHashCode(default(T));
        key = (key << 3) | (key >> 29) ^ occurrencesOfNull.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
        s += sep + Dafny.Helpers.ToString(default(T));
        sep = ", ";
      }
      foreach (var kv in dict) {
        var t = Dafny.Helpers.ToString(kv.Key);
        for (var i = BigInteger.Zero; i < kv.Value; i++) {
          s += sep + t;
          sep = ", ";
        }
      }
      return s + "}";
    }
    public static bool IsProperSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      return th.Count < other.Count && IsSubsetOf(th, other);
    }
    public static bool IsSubsetOf(IMultiSet<T> th, IMultiSet<T> other) {
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      if (b.occurrencesOfNull < a.occurrencesOfNull) {
        return false;
      }
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          if (b.dict[t] < a.dict[t]) {
            return false;
          }
        } else {
          if (a.dict[t] != BigInteger.Zero) {
            return false;
          }
        }
      }
      return true;
    }
    public static bool IsDisjointFrom(IMultiSet<T> th, IMultiSet<T> other) {
      foreach (T t in th.UniqueElements) {
        if (other.Contains(t)) {
          return false;
        }
      }
      return true;
    }

    public bool Contains<G>(G t) {
      return Select(t) != 0;
    }
    public BigInteger Select<G>(G t) {
      if (t == null) {
        return occurrencesOfNull;
      }
      BigInteger m;
      if (t is T && dict.TryGetValue((T)(object)t, out m)) {
        return m;
      } else {
        return BigInteger.Zero;
      }
    }
    public IMultiSet<T> Update<G>(G t, BigInteger i) {
      if (Select(t) == i) {
        return this;
      } else if (t == null) {
        var r = dict.ToBuilder();
        return new MultiSet<T>(r, i);
      } else {
        var r = dict.ToBuilder();
        r[(T)(object)t] = i;
        return new MultiSet<T>(r, occurrencesOfNull);
      }
    }
    public static IMultiSet<T> Union(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return other;
      } else if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + a.dict[t];
      }
      foreach (T t in b.dict.Keys) {
        BigInteger i;
        if (!r.TryGetValue(t, out i)) {
          i = BigInteger.Zero;
        }
        r[t] = i + b.dict[t];
      }
      return new MultiSet<T>(r, a.occurrencesOfNull + b.occurrencesOfNull);
    }
    public static IMultiSet<T> Intersect(IMultiSet<T> th, IMultiSet<T> other) {
      if (th.IsEmpty) {
        return th;
      } else if (other.IsEmpty) {
        return other;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t] < b.dict[t] ? a.dict[t] : b.dict[t]);
        }
      }
      return new MultiSet<T>(r, a.occurrencesOfNull < b.occurrencesOfNull ? a.occurrencesOfNull : b.occurrencesOfNull);
    }
    public static IMultiSet<T> Difference(IMultiSet<T> th, IMultiSet<T> other) { // \result == this - other
      if (other.IsEmpty) {
        return th;
      }
      var a = FromIMultiSet(th);
      var b = FromIMultiSet(other);
      var r = ImmutableDictionary<T, BigInteger>.Empty.ToBuilder();
      foreach (T t in a.dict.Keys) {
        if (!b.dict.ContainsKey(t)) {
          r.Add(t, a.dict[t]);
        } else if (b.dict[t] < a.dict[t]) {
          r.Add(t, a.dict[t] - b.dict[t]);
        }
      }
      return new MultiSet<T>(r, b.occurrencesOfNull < a.occurrencesOfNull ? a.occurrencesOfNull - b.occurrencesOfNull : BigInteger.Zero);
    }

    public bool IsEmpty { get { return occurrencesOfNull == 0 && dict.IsEmpty; } }

    public int Count {
      get { return (int)ElementCount(); }
    }
    public long LongCount {
      get { return (long)ElementCount(); }
    }
    private BigInteger ElementCount() {
      // This is inefficient
      var c = occurrencesOfNull;
      foreach (var item in dict) {
        c += item.Value;
      }
      return c;
    }

    public IEnumerable<T> Elements {
      get {
        for (var i = BigInteger.Zero; i < occurrencesOfNull; i++) {
          yield return default(T);
        }
        foreach (var item in dict) {
          for (var i = BigInteger.Zero; i < item.Value; i++) {
            yield return item.Key;
          }
        }
      }
    }

    public IEnumerable<T> UniqueElements {
      get {
        if (!occurrencesOfNull.IsZero) {
          yield return default(T);
        }
        foreach (var key in dict.Keys) {
          if (dict[key] != 0) {
            yield return key;
          }
        }
      }
    }
  }

  public interface IMap<out U, out V> {
    int Count { get; }
    long LongCount { get; }
    ISet<U> Keys { get; }
    ISet<V> Values { get; }
    IEnumerable<IPair<U, V>> ItemEnumerable { get; }
    bool Contains<G>(G t);
    /// <summary>
    /// Returns "true" iff "this is IMap<object, object>" and "this" equals "other".
    /// </summary>
    bool EqualsObjObj(IMap<object, object> other);
    IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter);
  }

  public class Map<U, V> : IMap<U, V> {
    readonly ImmutableDictionary<U, V> dict;
    readonly bool hasNullKey;  // true when "null" is a key of the Map
    readonly V nullValue;  // if "hasNullKey", the value that "null" maps to

    private Map(ImmutableDictionary<U, V>.Builder d, bool hasNullKey, V nullValue) {
      dict = d.ToImmutable();
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty.ToBuilder(), false, default(V));

    private Map(ImmutableDictionary<U, V> d, bool hasNullKey, V nullValue) {
      dict = d;
      this.hasNullKey = hasNullKey;
      this.nullValue = nullValue;
    }

    private static readonly TypeDescriptor<IMap<U, V>> _TYPE = new Dafny.TypeDescriptor<IMap<U, V>>(Empty);
    public static TypeDescriptor<IMap<U, V>> _TypeDescriptor() {
      return _TYPE;
    }

    public static Map<U, V> FromElements(params IPair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromCollection(IEnumerable<IPair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      var hasNullKey = false;
      var nullValue = default(V);
      foreach (var p in values) {
        if (p.Car == null) {
          hasNullKey = true;
          nullValue = p.Cdr;
        } else {
          d[p.Car] = p.Cdr;
        }
      }
      return new Map<U, V>(d, hasNullKey, nullValue);
    }
    public static Map<U, V> FromIMap(IMap<U, V> m) {
      return m as Map<U, V> ?? FromCollection(m.ItemEnumerable);
    }
    public IMap<UU, VV> DowncastClone<UU, VV>(Func<U, UU> keyConverter, Func<V, VV> valueConverter) {
      if (this is IMap<UU, VV> th) {
        return th;
      } else {
        var d = ImmutableDictionary<UU, VV>.Empty.ToBuilder();
        foreach (var item in this.dict) {
          var k = keyConverter(item.Key);
          var v = valueConverter(item.Value);
          d.Add(k, v);
        }
        return new Map<UU, VV>(d, this.hasNullKey, (VV)(object)this.nullValue);
      }
    }
    public int Count {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }
    public long LongCount {
      get { return dict.Count + (hasNullKey ? 1 : 0); }
    }

    public bool Equals(IMap<U, V> other) {
      if (other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      if (hasNullKey) {
        if (!other.Contains(default(U)) || !object.Equals(nullValue, Select(other, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Select(other, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public bool EqualsObjObj(IMap<object, object> other) {
      if (!(this is IMap<object, object>) || other == null || LongCount != other.LongCount) {
        return false;
      } else if (this == other) {
        return true;
      }
      var oth = Map<object, object>.FromIMap(other);
      if (hasNullKey) {
        if (!oth.Contains(default(U)) || !object.Equals(nullValue, Map<object, object>.Select(oth, default(U)))) {
          return false;
        }
      }
      foreach (var item in dict) {
        if (!other.Contains(item.Key) || !object.Equals(item.Value, Map<object, object>.Select(oth, item.Key))) {
          return false;
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      // See comment in Set.Equals
      var m = other as IMap<U, V>;
      if (m != null) {
        return Equals(m);
      }
      var imapoo = other as IMap<object, object>;
      if (imapoo != null) {
        return EqualsObjObj(imapoo);
      } else {
        return false;
      }
    }

    public override int GetHashCode() {
      var hashCode = 1;
      if (hasNullKey) {
        var key = Dafny.Helpers.GetHashCode(default(U));
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(nullValue);
        hashCode = hashCode * (key + 3);
      }
      foreach (var kv in dict) {
        var key = Dafny.Helpers.GetHashCode(kv.Key);
        key = (key << 3) | (key >> 29) ^ Dafny.Helpers.GetHashCode(kv.Value);
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      if (hasNullKey) {
        s += sep + Dafny.Helpers.ToString(default(U)) + " := " + Dafny.Helpers.ToString(nullValue);
        sep = ", ";
      }
      foreach (var kv in dict) {
        s += sep + Dafny.Helpers.ToString(kv.Key) + " := " + Dafny.Helpers.ToString(kv.Value);
        sep = ", ";
      }
      return s + "]";
    }
    public bool Contains<G>(G u) {
      return u == null ? hasNullKey : u is U && dict.ContainsKey((U)(object)u);
    }
    public static V Select(IMap<U, V> th, U index) {
      // the following will throw an exception if "index" in not a key of the map
      var m = FromIMap(th);
      return index == null && m.hasNullKey ? m.nullValue : m.dict[index];
    }
    public static IMap<U, V> Update(IMap<U, V> th, U index, V val) {
      var m = FromIMap(th);
      var d = m.dict.ToBuilder();
      if (index == null) {
        return new Map<U, V>(d, true, val);
      } else {
        d[index] = val;
        return new Map<U, V>(d, m.hasNullKey, m.nullValue);
      }
    }

    public static IMap<U, V> Merge(IMap<U, V> th, IMap<U, V> other) {
      var a = FromIMap(th);
      var b = FromIMap(other);
      ImmutableDictionary<U, V> d = a.dict.SetItems(b.dict);
      return new Map<U, V>(d, a.hasNullKey || b.hasNullKey, b.hasNullKey ? b.nullValue : a.nullValue);
    }

    public static IMap<U, V> Subtract(IMap<U, V> th, ISet<U> keys) {
      var a = FromIMap(th);
      ImmutableDictionary<U, V> d = a.dict.RemoveRange(keys.Elements);
      return new Map<U, V>(d, a.hasNullKey && !keys.Contains<object>(null), a.nullValue);
    }

    public ISet<U> Keys {
      get {
        if (hasNullKey) {
          return Dafny.Set<U>.FromCollectionPlusOne(dict.Keys, default(U));
        } else {
          return Dafny.Set<U>.FromCollection(dict.Keys);
        }
      }
    }
    public ISet<V> Values {
      get {
        if (hasNullKey) {
          return Dafny.Set<V>.FromCollectionPlusOne(dict.Values, nullValue);
        } else {
          return Dafny.Set<V>.FromCollection(dict.Values);
        }
      }
    }

    public IEnumerable<IPair<U, V>> ItemEnumerable {
      get {
        if (hasNullKey) {
          yield return new Pair<U, V>(default(U), nullValue);
        }
        foreach (KeyValuePair<U, V> kvp in dict) {
          yield return new Pair<U, V>(kvp.Key, kvp.Value);
        }
      }
    }

    public static ISet<_System._ITuple2<U, V>> Items(IMap<U, V> m) {
      var result = new HashSet<_System._ITuple2<U, V>>();
      foreach (var item in m.ItemEnumerable) {
        result.Add(_System.Tuple2<U, V>.create(item.Car, item.Cdr));
      }
      return Dafny.Set<_System._ITuple2<U, V>>.FromCollection(result);
    }
  }

  public interface ISequence<out T> {
    long LongCount { get; }
    int Count { get; }
    T[] Elements { get; }
    IEnumerable<T> UniqueElements { get; }
    T Select(ulong index);
    T Select(long index);
    T Select(uint index);
    T Select(int index);
    T Select(BigInteger index);
    bool Contains<G>(G g);
    ISequence<T> Take(long m);
    ISequence<T> Take(ulong n);
    ISequence<T> Take(BigInteger n);
    ISequence<T> Drop(long m);
    ISequence<T> Drop(ulong n);
    ISequence<T> Drop(BigInteger n);
    ISequence<T> Subsequence(long lo, long hi);
    ISequence<T> Subsequence(long lo, ulong hi);
    ISequence<T> Subsequence(long lo, BigInteger hi);
    ISequence<T> Subsequence(ulong lo, long hi);
    ISequence<T> Subsequence(ulong lo, ulong hi);
    ISequence<T> Subsequence(ulong lo, BigInteger hi);
    ISequence<T> Subsequence(BigInteger lo, long hi);
    ISequence<T> Subsequence(BigInteger lo, ulong hi);
    ISequence<T> Subsequence(BigInteger lo, BigInteger hi);
    bool EqualsAux(ISequence<object> other);
    ISequence<U> DowncastClone<U>(Func<T, U> converter);
  }

  public abstract class Sequence<T> : ISequence<T> {
    public static readonly ISequence<T> Empty = new ArraySequence<T>(new T[0]);

    private static readonly TypeDescriptor<ISequence<T>> _TYPE = new Dafny.TypeDescriptor<ISequence<T>>(Empty);
    public static TypeDescriptor<ISequence<T>> _TypeDescriptor() {
      return _TYPE;
    }

    public static ISequence<T> Create(BigInteger length, System.Func<BigInteger, T> init) {
      var len = (int)length;
      var values = new T[len];
      for (int i = 0; i < len; i++) {
        values[i] = init(new BigInteger(i));
      }
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromArray(T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<T> FromElements(params T[] values) {
      return new ArraySequence<T>(values);
    }
    public static ISequence<char> FromString(string s) {
      return new ArraySequence<char>(s.ToCharArray());
    }
    public ISequence<U> DowncastClone<U>(Func<T, U> converter) {
      if (this is ISequence<U> th) {
        return th;
      } else {
        var values = new U[this.LongCount];
        for (long i = 0; i < this.LongCount; i++) {
          var val = converter(this.Select(i));
          values[i] = val;
        }
        return new ArraySequence<U>(values);
      }
    }
    public static ISequence<T> Update(ISequence<T> sequence, long index, T t) {
      T[] tmp = (T[])sequence.Elements.Clone();
      tmp[index] = t;
      return new ArraySequence<T>(tmp);
    }
    public static ISequence<T> Update(ISequence<T> sequence, ulong index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static ISequence<T> Update(ISequence<T> sequence, BigInteger index, T t) {
      return Update(sequence, (long)index, t);
    }
    public static bool EqualUntil(ISequence<T> left, ISequence<T> right, int n) {
      T[] leftElmts = left.Elements, rightElmts = right.Elements;
      for (int i = 0; i < n; i++) {
        if (!object.Equals(leftElmts[i], rightElmts[i])) {
          return false;
        }
      }
      return true;
    }
    public static bool IsPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n <= right.Elements.Length && EqualUntil(left, right, n);
    }
    public static bool IsProperPrefixOf(ISequence<T> left, ISequence<T> right) {
      int n = left.Elements.Length;
      return n < right.Elements.Length && EqualUntil(left, right, n);
    }
    public static ISequence<T> Concat(ISequence<T> left, ISequence<T> right) {
      if (left.Count == 0) {
        return right;
      }
      if (right.Count == 0) {
        return left;
      }
      return new ConcatSequence<T>(left, right);
    }
    // Make Count a public abstract instead of LongCount, since the "array size is limited to a total of 4 billion
    // elements, and to a maximum index of 0X7FEFFFFF". Therefore, as a protection, limit this to int32.
    // https://docs.microsoft.com/en-us/dotnet/api/system.array
    public abstract int Count { get; }
    public long LongCount {
      get { return Count; }
    }
    // ImmutableElements cannot be public in the interface since ImmutableArray<T> leads to a
    // "covariant type T occurs in invariant position" error. There do not appear to be interfaces for ImmutableArray<T>
    // that resolve this.
    protected abstract ImmutableArray<T> ImmutableElements { get; }

    public T[] Elements {
      get { return ImmutableElements.ToArray(); }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromCollection(ImmutableElements);
        return st.Elements;
      }
    }

    public T Select(ulong index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(long index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(uint index) {
      return ImmutableElements[checked((int)index)];
    }
    public T Select(int index) {
      return ImmutableElements[index];
    }
    public T Select(BigInteger index) {
      return ImmutableElements[(int)index];
    }
    public bool Equals(ISequence<T> other) {
      int n = ImmutableElements.Length;
      return n == other.Elements.Length && EqualUntil(this, other, n);
    }
    public override bool Equals(object other) {
      if (other is ISequence<T>) {
        return Equals((ISequence<T>)other);
      }
      var th = this as ISequence<object>;
      var oth = other as ISequence<object>;
      if (th != null && oth != null) {
        // see explanation in Set.Equals
        return oth.EqualsAux(th);
      } else {
        return false;
      }
    }
    public bool EqualsAux(ISequence<object> other) {
      var s = other as ISequence<T>;
      if (s != null) {
        return Equals(s);
      } else {
        return false;
      }
    }
    public override int GetHashCode() {
      ImmutableArray<T> elmts = ImmutableElements;
      // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
      if (elmts.IsDefaultOrEmpty) {
        return 0;
      }

      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ Dafny.Helpers.GetHashCode(elmts[i]);
      }
      return hashCode;
    }
    public override string ToString() {
      // This is required because (ImmutableElements is ImmutableArray<char>) is not a valid type check
      var typeCheckTmp = new T[0];
      ImmutableArray<T> elmts = ImmutableElements;
      if (typeCheckTmp is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + Dafny.Helpers.ToString(t);
          sep = ", ";
        }
        return s + "]";
      }
    }
    public bool Contains<G>(G g) {
      if (g == null || g is T) {
        var t = (T)(object)g;
        return ImmutableElements.Contains(t);
      }
      return false;
    }
    public ISequence<T> Take(long m) {
      if (ImmutableElements.Length == m) {
        return this;
      }

      int length = checked((int)m);
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(0, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public ISequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public ISequence<T> Drop(long m) {
      int startingElement = checked((int)m);
      if (startingElement == 0) {
        return this;
      }

      int length = ImmutableElements.Length - startingElement;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingElement, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public ISequence<T> Drop(BigInteger n) {
      if (n.IsZero) {
        return this;
      }

      return Drop((long)n);
    }
    public ISequence<T> Subsequence(long lo, long hi) {
      if (lo == 0 && hi == ImmutableElements.Length) {
        return this;
      }
      int startingIndex = checked((int)lo);
      int endingIndex = checked((int)hi);
      var length = endingIndex - startingIndex;
      T[] tmp = new T[length];
      ImmutableElements.CopyTo(startingIndex, tmp, 0, length);
      return new ArraySequence<T>(tmp);
    }
    public ISequence<T> Subsequence(long lo, ulong hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(long lo, BigInteger hi) {
      return Subsequence(lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(ulong lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(ulong lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, long hi) {
      return Subsequence((long)lo, hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, ulong hi) {
      return Subsequence((long)lo, (long)hi);
    }
    public ISequence<T> Subsequence(BigInteger lo, BigInteger hi) {
      return Subsequence((long)lo, (long)hi);
    }
  }

  internal class ArraySequence<T> : Sequence<T> {
    private readonly ImmutableArray<T> elmts;

    internal ArraySequence(ImmutableArray<T> ee) {
      elmts = ee;
    }
    internal ArraySequence(T[] ee) {
      elmts = ImmutableArray.Create<T>(ee);
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        return elmts;
      }
    }
    public override int Count {
      get {
        return elmts.Length;
      }
    }
  }

  internal class ConcatSequence<T> : Sequence<T> {
    // INVARIANT: Either left != null, right != null, and elmts's underlying array == null or
    // left == null, right == null, and elmts's underlying array != null
    private volatile ISequence<T> left, right;
    private ImmutableArray<T> elmts;
    private readonly int count;

    internal ConcatSequence(ISequence<T> left, ISequence<T> right) {
      this.left = left;
      this.right = right;
      this.count = left.Count + right.Count;
    }

    protected override ImmutableArray<T> ImmutableElements {
      get {
        // IsDefault returns true if the underlying array is a null reference
        // https://devblogs.microsoft.com/dotnet/please-welcome-immutablearrayt/
        if (elmts.IsDefault) {
          elmts = ComputeElements();
          // We don't need the original sequences anymore; let them be
          // garbage-collected
          left = null;
          right = null;
        }
        return elmts;
      }
    }

    public override int Count {
      get {
        return count;
      }
    }

    private ImmutableArray<T> ComputeElements() {
      // Traverse the tree formed by all descendants which are ConcatSequences
      var ansBuilder = ImmutableArray.CreateBuilder<T>();
      var toVisit = new Stack<ISequence<T>>();
      var (leftBuffer, rightBuffer) = (left, right);
      if (left == null || right == null) {
        // elmts can't be .IsDefault while either left, or right are null
        return elmts;
      }
      toVisit.Push(rightBuffer);
      toVisit.Push(leftBuffer);

      while (toVisit.Count != 0) {
        var seq = toVisit.Pop();
        if (seq is ConcatSequence<T> cs && cs.elmts.IsDefault) {
          (leftBuffer, rightBuffer) = (cs.left, cs.right);
          if (cs.left == null || cs.right == null) {
            // !cs.elmts.IsDefault, due to concurrent enumeration
            toVisit.Push(cs);
          } else {
            toVisit.Push(rightBuffer);
            toVisit.Push(leftBuffer);
          }
        } else {
          var array = seq.Elements;
          ansBuilder.AddRange(array);
        }
      }
      return ansBuilder.ToImmutable();
    }
  }

  public interface IPair<out A, out B> {
    A Car { get; }
    B Cdr { get; }
  }

  public class Pair<A, B> : IPair<A, B> {
    private A car;
    private B cdr;
    public A Car { get { return car; } }
    public B Cdr { get { return cdr; } }
    public Pair(A a, B b) {
      this.car = a;
      this.cdr = b;
    }
  }

  public class TypeDescriptor<T> {
    private readonly T initValue;
    public TypeDescriptor(T initValue) {
      this.initValue = initValue;
    }
    public T Default() {
      return initValue;
    }
  }

  public partial class Helpers {
    public static int GetHashCode<G>(G g) {
      return g == null ? 1001 : g.GetHashCode();
    }

    public static int ToIntChecked(BigInteger i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(long i, string msg) {
      if (i > Int32.MaxValue || i < Int32.MinValue) {
        if (msg == null) {
          msg = "value out of range for a 32-bit int";
        }

        throw new HaltException(msg + ": " + i);
      }
      return (int)i;
    }
    public static int ToIntChecked(int i, string msg) {
      return i;
    }

    public static string ToString<G>(G g) {
      if (g == null) {
        return "null";
      } else if (g is bool) {
        return (bool)(object)g ? "true" : "false";  // capitalize boolean literals like in Dafny
      } else {
        return g.ToString();
      }
    }
    public static void Print<G>(G g) {
      System.Console.Write(ToString(g));
    }

    public static readonly TypeDescriptor<bool> BOOL = new TypeDescriptor<bool>(false);
    public static readonly TypeDescriptor<char> CHAR = new TypeDescriptor<char>('D');  // See CharType.DefaultValue in Dafny source code
    public static readonly TypeDescriptor<BigInteger> INT = new TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static readonly TypeDescriptor<BigRational> REAL = new TypeDescriptor<BigRational>(BigRational.ZERO);
    public static readonly TypeDescriptor<byte> UINT8 = new TypeDescriptor<byte>(0);
    public static readonly TypeDescriptor<ushort> UINT16 = new TypeDescriptor<ushort>(0);
    public static readonly TypeDescriptor<uint> UINT32 = new TypeDescriptor<uint>(0);
    public static readonly TypeDescriptor<ulong> UINT64 = new TypeDescriptor<ulong>(0);

    public static TypeDescriptor<T> NULL<T>() where T : class {
      return new TypeDescriptor<T>(null);
    }

    public static TypeDescriptor<A[]> ARRAY<A>() {
      return new TypeDescriptor<A[]>(new A[0]);
    }

    public static bool Quantifier<T>(IEnumerable<T> vals, bool frall, System.Predicate<T> pred) {
      foreach (var u in vals) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public static IEnumerable<bool> AllBooleans() {
      yield return false;
      yield return true;
    }
    public static IEnumerable<char> AllChars() {
      for (int i = 0; i < 0x10000; i++) {
        yield return (char)i;
      }
    }
    public static IEnumerable<BigInteger> AllIntegers() {
      yield return new BigInteger(0);
      for (var j = new BigInteger(1); ; j++) {
        yield return j;
        yield return -j;
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true;) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    public static IEnumerable<T> SingleValue<T>(T e) {
      yield return e;
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }

    public static U CastConverter<T, U>(T t) {
      return (U)(object)t;
    }

    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new ArraySequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it is possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u) {
      return u;
    }

    public static U Let<T, U>(T t, Func<T, U> f) {
      return f(t);
    }

    public static A Id<A>(A a) {
      return a;
    }

    public static void WithHaltHandling(Action action) {
      try {
        action();
      } catch (HaltException e) {
        Console.WriteLine("[Program halted] " + e.Message);
      }
    }
  }

  public class BigOrdinal {
    public static bool IsLimit(BigInteger ord) {
      return ord == 0;
    }
    public static bool IsSucc(BigInteger ord) {
      return 0 < ord;
    }
    public static BigInteger Offset(BigInteger ord) {
      return ord;
    }
    public static bool IsNat(BigInteger ord) {
      return true;  // at run time, every ORDINAL is a natural number
    }
  }

  public struct BigRational {
    public static readonly BigRational ZERO = new BigRational(0);

    // We need to deal with the special case "num == 0 && den == 0", because
    // that's what C#'s default struct constructor will produce for BigRational. :(
    // To deal with it, we ignore "den" when "num" is 0.
    BigInteger num, den;  // invariant 1 <= den || (num == 0 && den == 0)
    public override string ToString() {
      int log10;
      if (num.IsZero || den.IsOne) {
        return string.Format("{0}.0", num);
      } else if (IsPowerOf10(den, out log10)) {
        string sign;
        string digits;
        if (num.Sign < 0) {
          sign = "-"; digits = (-num).ToString();
        } else {
          sign = ""; digits = num.ToString();
        }
        if (log10 < digits.Length) {
          var n = digits.Length - log10;
          return string.Format("{0}{1}.{2}", sign, digits.Substring(0, n), digits.Substring(n));
        } else {
          return string.Format("{0}0.{1}{2}", sign, new string('0', log10 - digits.Length), digits);
        }
      } else {
        return string.Format("({0}.0 / {1}.0)", num, den);
      }
    }
    public bool IsPowerOf10(BigInteger x, out int log10) {
      log10 = 0;
      if (x.IsZero) {
        return false;
      }
      while (true) {  // invariant: x != 0 && x * 10^log10 == old(x)
        if (x.IsOne) {
          return true;
        } else if (x % 10 == 0) {
          log10++;
          x /= 10;
        } else {
          return false;
        }
      }
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (num.IsZero || den.IsOne) {
        return num;
      } else if (0 < num.Sign) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      if (a.num.IsZero) {
        aa = a.num;
        bb = b.num;
        dd = b.den;
      } else if (b.num.IsZero) {
        aa = a.num;
        dd = a.den;
        bb = b.num;
      } else {
        var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
        var xx = a.den / gcd;
        var yy = b.den / gcd;
        // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
        aa = a.num * yy;
        bb = b.num * xx;
        dd = a.den * yy;
      }
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public int Sign {
      get {
        return num.Sign;
      }
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return a.CompareTo(b) > 0;
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return a.CompareTo(b) >= 0;
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num.Sign) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }

  public class HaltException : Exception {
    public HaltException(object message) : base(message.ToString()) {
    }
  }
}

namespace @_System {
  public interface _ITuple2<out T0, out T1> {
    T0 dtor__0 { get; }
    T1 dtor__1 { get; }
  }

  public class Tuple2<T0, T1> : _ITuple2<T0, T1> {
    public readonly T0 _0;
    public readonly T1 _1;
    public Tuple2(T0 _0, T1 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple2<T0, T1>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int)hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple2<T0, T1> Default(T0 _default_T0, T1 _default_T1) {
      return create(_default_T0, _default_T1);
    }
    public static Dafny.TypeDescriptor<_System._ITuple2<T0, T1>> _TypeDescriptor(Dafny.TypeDescriptor<T0> _td_T0, Dafny.TypeDescriptor<T1> _td_T1) {
      return new Dafny.TypeDescriptor<_System._ITuple2<T0, T1>>(_System.Tuple2<T0, T1>.Default(_td_T0.Default(), _td_T1.Default()));
    }
    public static _ITuple2<T0, T1> create(T0 _0, T1 _1) {
      return new Tuple2<T0, T1>(_0, _1);
    }
    public T0 dtor__0 {
      get {
        return this._0;
      }
    }
    public T1 dtor__1 {
      get {
        return this._1;
      }
    }
  }

} // end of namespace _System
namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace Bridge_Compile {

  public interface _INext__Car {
    bool is_A { get; }
    bool is_B { get; }
    bool is_Both { get; }
    bool is_Neither { get; }
    _INext__Car DowncastClone();
  }
  public abstract class Next__Car : _INext__Car {
    public Next__Car() { }
    private static readonly _INext__Car theDefault = create_A();
    public static _INext__Car Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Bridge_Compile._INext__Car> _TYPE = new Dafny.TypeDescriptor<Bridge_Compile._INext__Car>(Bridge_Compile.Next__Car.Default());
    public static Dafny.TypeDescriptor<Bridge_Compile._INext__Car> _TypeDescriptor() {
      return _TYPE;
    }
    public static _INext__Car create_A() {
      return new Next__Car_A();
    }
    public static _INext__Car create_B() {
      return new Next__Car_B();
    }
    public static _INext__Car create_Both() {
      return new Next__Car_Both();
    }
    public static _INext__Car create_Neither() {
      return new Next__Car_Neither();
    }
    public bool is_A { get { return this is Next__Car_A; } }
    public bool is_B { get { return this is Next__Car_B; } }
    public bool is_Both { get { return this is Next__Car_Both; } }
    public bool is_Neither { get { return this is Next__Car_Neither; } }
    public static System.Collections.Generic.IEnumerable<_INext__Car> AllSingletonConstructors {
      get {
        yield return Next__Car.create_A();
        yield return Next__Car.create_B();
        yield return Next__Car.create_Both();
        yield return Next__Car.create_Neither();
      }
    }
    public abstract _INext__Car DowncastClone();
  }
  public class Next__Car_A : Next__Car {
    public Next__Car_A() {
    }
    public override _INext__Car DowncastClone() {
      if (this is _INext__Car dt) { return dt; }
      return new Next__Car_A();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Next__Car_A;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Next_Car.A";
      return s;
    }
  }
  public class Next__Car_B : Next__Car {
    public Next__Car_B() {
    }
    public override _INext__Car DowncastClone() {
      if (this is _INext__Car dt) { return dt; }
      return new Next__Car_B();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Next__Car_B;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Next_Car.B";
      return s;
    }
  }
  public class Next__Car_Both : Next__Car {
    public Next__Car_Both() {
    }
    public override _INext__Car DowncastClone() {
      if (this is _INext__Car dt) { return dt; }
      return new Next__Car_Both();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Next__Car_Both;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Next_Car.Both";
      return s;
    }
  }
  public class Next__Car_Neither : Next__Car {
    public Next__Car_Neither() {
    }
    public override _INext__Car DowncastClone() {
      if (this is _INext__Car dt) { return dt; }
      return new Next__Car_Neither();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Next__Car_Neither;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Next_Car.Neither";
      return s;
    }
  }

  public interface _ITraffic__Light {
    bool is_Red { get; }
    bool is_Green { get; }
    _ITraffic__Light DowncastClone();
  }
  public abstract class Traffic__Light : _ITraffic__Light {
    public Traffic__Light() { }
    private static readonly _ITraffic__Light theDefault = create_Red();
    public static _ITraffic__Light Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Bridge_Compile._ITraffic__Light> _TYPE = new Dafny.TypeDescriptor<Bridge_Compile._ITraffic__Light>(Bridge_Compile.Traffic__Light.Default());
    public static Dafny.TypeDescriptor<Bridge_Compile._ITraffic__Light> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITraffic__Light create_Red() {
      return new Traffic__Light_Red();
    }
    public static _ITraffic__Light create_Green() {
      return new Traffic__Light_Green();
    }
    public bool is_Red { get { return this is Traffic__Light_Red; } }
    public bool is_Green { get { return this is Traffic__Light_Green; } }
    public static System.Collections.Generic.IEnumerable<_ITraffic__Light> AllSingletonConstructors {
      get {
        yield return Traffic__Light.create_Red();
        yield return Traffic__Light.create_Green();
      }
    }
    public abstract _ITraffic__Light DowncastClone();
  }
  public class Traffic__Light_Red : Traffic__Light {
    public Traffic__Light_Red() {
    }
    public override _ITraffic__Light DowncastClone() {
      if (this is _ITraffic__Light dt) { return dt; }
      return new Traffic__Light_Red();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Traffic__Light_Red;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Traffic_Light.Red";
      return s;
    }
  }
  public class Traffic__Light_Green : Traffic__Light {
    public Traffic__Light_Green() {
    }
    public override _ITraffic__Light DowncastClone() {
      if (this is _ITraffic__Light dt) { return dt; }
      return new Traffic__Light_Green();
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.Traffic__Light_Green;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.Traffic_Light.Green";
      return s;
    }
  }

  public interface _Istate {
    bool is_State { get; }
    Bridge_Compile._ITraffic__Light dtor_LightA { get; }
    Bridge_Compile._ITraffic__Light dtor_LightB { get; }
    BigInteger dtor_W__A { get; }
    BigInteger dtor_W__B { get; }
    BigInteger dtor_Cross__Counter { get; }
    _Istate DowncastClone();
  }
  public class state : _Istate {
    public readonly Bridge_Compile._ITraffic__Light LightA;
    public readonly Bridge_Compile._ITraffic__Light LightB;
    public readonly BigInteger W__A;
    public readonly BigInteger W__B;
    public readonly BigInteger Cross__Counter;
    public state(Bridge_Compile._ITraffic__Light LightA, Bridge_Compile._ITraffic__Light LightB, BigInteger W__A, BigInteger W__B, BigInteger Cross__Counter) {
      this.LightA = LightA;
      this.LightB = LightB;
      this.W__A = W__A;
      this.W__B = W__B;
      this.Cross__Counter = Cross__Counter;
    }
    public _Istate DowncastClone() {
      if (this is _Istate dt) { return dt; }
      return new state(LightA, LightB, W__A, W__B, Cross__Counter);
    }
    public override bool Equals(object other) {
      var oth = other as Bridge_Compile.state;
      return oth != null && object.Equals(this.LightA, oth.LightA) && object.Equals(this.LightB, oth.LightB) && this.W__A == oth.W__A && this.W__B == oth.W__B && this.Cross__Counter == oth.Cross__Counter;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.LightA));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.LightB));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.W__A));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.W__B));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.Cross__Counter));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Bridge_Compile.state.State";
      s += "(";
      s += Dafny.Helpers.ToString(this.LightA);
      s += ", ";
      s += Dafny.Helpers.ToString(this.LightB);
      s += ", ";
      s += Dafny.Helpers.ToString(this.W__A);
      s += ", ";
      s += Dafny.Helpers.ToString(this.W__B);
      s += ", ";
      s += Dafny.Helpers.ToString(this.Cross__Counter);
      s += ")";
      return s;
    }
    private static readonly _Istate theDefault = create(Bridge_Compile.Traffic__Light.Default(), Bridge_Compile.Traffic__Light.Default(), BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
    public static _Istate Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Bridge_Compile._Istate> _TYPE = new Dafny.TypeDescriptor<Bridge_Compile._Istate>(Bridge_Compile.state.Default());
    public static Dafny.TypeDescriptor<Bridge_Compile._Istate> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Istate create(Bridge_Compile._ITraffic__Light LightA, Bridge_Compile._ITraffic__Light LightB, BigInteger W__A, BigInteger W__B, BigInteger Cross__Counter) {
      return new state(LightA, LightB, W__A, W__B, Cross__Counter);
    }
    public bool is_State { get { return true; } }
    public Bridge_Compile._ITraffic__Light dtor_LightA {
      get {
        return this.LightA;
      }
    }
    public Bridge_Compile._ITraffic__Light dtor_LightB {
      get {
        return this.LightB;
      }
    }
    public BigInteger dtor_W__A {
      get {
        return this.W__A;
      }
    }
    public BigInteger dtor_W__B {
      get {
        return this.W__B;
      }
    }
    public BigInteger dtor_Cross__Counter {
      get {
        return this.Cross__Counter;
      }
    }
  }

  public partial class __default {
    public static bool Valid(Bridge_Compile._Istate s) {
      if ((object.Equals((s).dtor_LightA, Bridge_Compile.Traffic__Light.create_Green())) && (object.Equals((s).dtor_LightB, Bridge_Compile.Traffic__Light.create_Green()))) {
        return false;
      } else {
        return true;
      }
    }
    public static Bridge_Compile._Istate Init()
    {
      Bridge_Compile._Istate s = Bridge_Compile.state.Default();
      s = Bridge_Compile.state.create(Bridge_Compile.Traffic__Light.create_Red(), Bridge_Compile.Traffic__Light.create_Red(), BigInteger.Zero, BigInteger.Zero, BigInteger.Zero);
      return s;
    }
    public static Bridge_Compile._Istate Increment__W__A(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s, _pat_let0_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let0_0, _123_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((s).dtor_W__A) + (BigInteger.One), _pat_let1_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let1_0, _124_dt__update_hW__A_h0 => Bridge_Compile.state.create((_123_dt__update__tmp_h0).dtor_LightA, (_123_dt__update__tmp_h0).dtor_LightB, _124_dt__update_hW__A_h0, (_123_dt__update__tmp_h0).dtor_W__B, (_123_dt__update__tmp_h0).dtor_Cross__Counter)))));
      return s_k;
    }
    public static Bridge_Compile._Istate Increment__W__B(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s, _pat_let2_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let2_0, _125_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((s).dtor_W__B) + (BigInteger.One), _pat_let3_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let3_0, _126_dt__update_hW__B_h0 => Bridge_Compile.state.create((_125_dt__update__tmp_h0).dtor_LightA, (_125_dt__update__tmp_h0).dtor_LightB, (_125_dt__update__tmp_h0).dtor_W__A, _126_dt__update_hW__B_h0, (_125_dt__update__tmp_h0).dtor_Cross__Counter)))));
      return s_k;
    }
    public static Bridge_Compile._Istate Increment__Cross__Counter(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s, _pat_let4_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let4_0, _127_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((s).dtor_Cross__Counter) + (BigInteger.One), _pat_let5_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let5_0, _128_dt__update_hCross__Counter_h0 => Bridge_Compile.state.create((_127_dt__update__tmp_h0).dtor_LightA, (_127_dt__update__tmp_h0).dtor_LightB, (_127_dt__update__tmp_h0).dtor_W__A, (_127_dt__update__tmp_h0).dtor_W__B, _128_dt__update_hCross__Counter_h0)))));
      return s_k;
    }
    public static Bridge_Compile._Istate Reset__Cross__Counter(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s, _pat_let6_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let6_0, _129_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(BigInteger.Zero, _pat_let7_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let7_0, _130_dt__update_hCross__Counter_h0 => Bridge_Compile.state.create((_129_dt__update__tmp_h0).dtor_LightA, (_129_dt__update__tmp_h0).dtor_LightB, (_129_dt__update__tmp_h0).dtor_W__A, (_129_dt__update__tmp_h0).dtor_W__B, _130_dt__update_hCross__Counter_h0)))));
      return s_k;
    }
    public static Bridge_Compile._Istate Cross(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = s;
      if (((s).dtor_LightA).is_Green) {
        var _pat_let_tv10 = s_k;
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let8_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let8_0, _131_dt__update__tmp_h0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((_pat_let_tv10).dtor_W__A) - (BigInteger.One), _pat_let9_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let9_0, _132_dt__update_hW__A_h0 => Bridge_Compile.state.create((_131_dt__update__tmp_h0).dtor_LightA, (_131_dt__update__tmp_h0).dtor_LightB, _132_dt__update_hW__A_h0, (_131_dt__update__tmp_h0).dtor_W__B, (_131_dt__update__tmp_h0).dtor_Cross__Counter)))));
        Bridge_Compile._Istate _out0;
        _out0 = Bridge_Compile.__default.Increment__Cross__Counter(s_k);
        s_k = _out0;
      } else {
        var _pat_let_tv13 = s_k;
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let11_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let11_0, _133_dt__update__tmp_h1 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((_pat_let_tv13).dtor_W__B) - (BigInteger.One), _pat_let12_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let12_0, _134_dt__update_hW__B_h0 => Bridge_Compile.state.create((_133_dt__update__tmp_h1).dtor_LightA, (_133_dt__update__tmp_h1).dtor_LightB, (_133_dt__update__tmp_h1).dtor_W__A, _134_dt__update_hW__B_h0, (_133_dt__update__tmp_h1).dtor_Cross__Counter)))));
        Bridge_Compile._Istate _out1;
        _out1 = Bridge_Compile.__default.Increment__Cross__Counter(s_k);
        s_k = _out1;
      }
      return s_k;
    }
    public static Bridge_Compile._Istate Switch__Lights(Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = s;
      if (((s_k).dtor_LightA).is_Red) {
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let14_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let14_0, _135_dt__update__tmp_h0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Green(), _pat_let15_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let15_0, _136_dt__update_hLightA_h0 => Bridge_Compile.state.create(_136_dt__update_hLightA_h0, (_135_dt__update__tmp_h0).dtor_LightB, (_135_dt__update__tmp_h0).dtor_W__A, (_135_dt__update__tmp_h0).dtor_W__B, (_135_dt__update__tmp_h0).dtor_Cross__Counter)))));
      } else {
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let16_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let16_0, _137_dt__update__tmp_h1 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Red(), _pat_let17_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let17_0, _138_dt__update_hLightA_h1 => Bridge_Compile.state.create(_138_dt__update_hLightA_h1, (_137_dt__update__tmp_h1).dtor_LightB, (_137_dt__update__tmp_h1).dtor_W__A, (_137_dt__update__tmp_h1).dtor_W__B, (_137_dt__update__tmp_h1).dtor_Cross__Counter)))));
      }
      if (((s_k).dtor_LightB).is_Red) {
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let18_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let18_0, _139_dt__update__tmp_h2 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Green(), _pat_let19_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let19_0, _140_dt__update_hLightB_h0 => Bridge_Compile.state.create((_139_dt__update__tmp_h2).dtor_LightA, _140_dt__update_hLightB_h0, (_139_dt__update__tmp_h2).dtor_W__A, (_139_dt__update__tmp_h2).dtor_W__B, (_139_dt__update__tmp_h2).dtor_Cross__Counter)))));
      } else {
        s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let20_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let20_0, _141_dt__update__tmp_h3 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Red(), _pat_let21_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let21_0, _142_dt__update_hLightB_h1 => Bridge_Compile.state.create((_141_dt__update__tmp_h3).dtor_LightA, _142_dt__update_hLightB_h1, (_141_dt__update__tmp_h3).dtor_W__A, (_141_dt__update__tmp_h3).dtor_W__B, (_141_dt__update__tmp_h3).dtor_Cross__Counter)))));
      }
      return s_k;
    }
    public static Bridge_Compile._Istate Tick(Bridge_Compile._INext__Car next, Bridge_Compile._Istate s)
    {
      Bridge_Compile._Istate s_k = Bridge_Compile.state.Default();
      s_k = s;
      Bridge_Compile._INext__Car _source0 = next;
      if (_source0.is_A) {
        Bridge_Compile._Istate _out2;
        _out2 = Bridge_Compile.__default.Increment__W__A(s_k);
        s_k = _out2;
      } else if (_source0.is_B) {
        Bridge_Compile._Istate _out3;
        _out3 = Bridge_Compile.__default.Increment__W__B(s_k);
        s_k = _out3;
      } else if (_source0.is_Both) {
        Bridge_Compile._Istate _out4;
        _out4 = Bridge_Compile.__default.Increment__W__A(s_k);
        s_k = _out4;
        Bridge_Compile._Istate _out5;
        _out5 = Bridge_Compile.__default.Increment__W__B(s_k);
        s_k = _out5;
      } else {
        s_k = s_k;
      }
      if (((((s_k).dtor_W__A).Sign == 0) || (((s_k).dtor_W__B).Sign == 0)) && (!((((s_k).dtor_W__A).Sign == 0) && (((s_k).dtor_W__B).Sign == 0)))) {
        Bridge_Compile._Istate _out6;
        _out6 = Bridge_Compile.__default.Reset__Cross__Counter(s_k);
        s_k = _out6;
        if (((s_k).dtor_W__A).Sign == 1) {
          if (((s_k).dtor_LightA).is_Red) {
            s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let22_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let22_0, _143_dt__update__tmp_h0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Red(), _pat_let23_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let23_0, _144_dt__update_hLightB_h0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Green(), _pat_let24_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let24_0, _145_dt__update_hLightA_h0 => Bridge_Compile.state.create(_145_dt__update_hLightA_h0, _144_dt__update_hLightB_h0, (_143_dt__update__tmp_h0).dtor_W__A, (_143_dt__update__tmp_h0).dtor_W__B, (_143_dt__update__tmp_h0).dtor_Cross__Counter)))))));
          }
          var _pat_let_tv27 = s_k;
          s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let25_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let25_0, _146_dt__update__tmp_h1 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((_pat_let_tv27).dtor_W__A) - (BigInteger.One), _pat_let26_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let26_0, _147_dt__update_hW__A_h0 => Bridge_Compile.state.create((_146_dt__update__tmp_h1).dtor_LightA, (_146_dt__update__tmp_h1).dtor_LightB, _147_dt__update_hW__A_h0, (_146_dt__update__tmp_h1).dtor_W__B, (_146_dt__update__tmp_h1).dtor_Cross__Counter)))));
          Bridge_Compile._Istate _out7;
          _out7 = Bridge_Compile.__default.Increment__Cross__Counter(s_k);
          s_k = _out7;
        } else {
          if (((s_k).dtor_LightB).is_Red) {
            s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let28_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let28_0, _148_dt__update__tmp_h2 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Green(), _pat_let29_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let29_0, _149_dt__update_hLightB_h1 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Red(), _pat_let30_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let30_0, _150_dt__update_hLightA_h1 => Bridge_Compile.state.create(_150_dt__update_hLightA_h1, _149_dt__update_hLightB_h1, (_148_dt__update__tmp_h2).dtor_W__A, (_148_dt__update__tmp_h2).dtor_W__B, (_148_dt__update__tmp_h2).dtor_Cross__Counter)))))));
          }
          var _pat_let_tv33 = s_k;
          s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let31_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let31_0, _151_dt__update__tmp_h3 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((_pat_let_tv33).dtor_W__B) - (BigInteger.One), _pat_let32_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let32_0, _152_dt__update_hW__B_h0 => Bridge_Compile.state.create((_151_dt__update__tmp_h3).dtor_LightA, (_151_dt__update__tmp_h3).dtor_LightB, (_151_dt__update__tmp_h3).dtor_W__A, _152_dt__update_hW__B_h0, (_151_dt__update__tmp_h3).dtor_Cross__Counter)))));
          Bridge_Compile._Istate _out8;
          _out8 = Bridge_Compile.__default.Increment__Cross__Counter(s_k);
          s_k = _out8;
        }
      } else if ((((s_k).dtor_W__A).Sign == 1) || (((s_k).dtor_W__B).Sign == 1)) {
        if ((((s_k).dtor_LightA).is_Red) && (((s_k).dtor_LightB).is_Red)) {
          s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let34_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let34_0, _153_dt__update__tmp_h4 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(Bridge_Compile.Traffic__Light.create_Green(), _pat_let35_0 => Dafny.Helpers.Let<Bridge_Compile._ITraffic__Light, Bridge_Compile._Istate>(_pat_let35_0, _154_dt__update_hLightA_h2 => Bridge_Compile.state.create(_154_dt__update_hLightA_h2, (_153_dt__update__tmp_h4).dtor_LightB, (_153_dt__update__tmp_h4).dtor_W__A, (_153_dt__update__tmp_h4).dtor_W__B, (_153_dt__update__tmp_h4).dtor_Cross__Counter)))));
          var _pat_let_tv38 = s_k;
          s_k = Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(s_k, _pat_let36_0 => Dafny.Helpers.Let<Bridge_Compile._Istate, Bridge_Compile._Istate>(_pat_let36_0, _155_dt__update__tmp_h5 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(((_pat_let_tv38).dtor_W__A) - (BigInteger.One), _pat_let37_0 => Dafny.Helpers.Let<BigInteger, Bridge_Compile._Istate>(_pat_let37_0, _156_dt__update_hW__A_h1 => Bridge_Compile.state.create((_155_dt__update__tmp_h5).dtor_LightA, (_155_dt__update__tmp_h5).dtor_LightB, _156_dt__update_hW__A_h1, (_155_dt__update__tmp_h5).dtor_W__B, (_155_dt__update__tmp_h5).dtor_Cross__Counter)))));
          Bridge_Compile._Istate _out9;
          _out9 = Bridge_Compile.__default.Increment__Cross__Counter(s_k);
          s_k = _out9;
        } else {
          if (((s_k).dtor_Cross__Counter) < (new BigInteger(5))) {
            Bridge_Compile._Istate _out10;
            _out10 = Bridge_Compile.__default.Cross(s_k);
            s_k = _out10;
          } else {
            Bridge_Compile._Istate _out11;
            _out11 = Bridge_Compile.__default.Switch__Lights(s_k);
            s_k = _out11;
            Bridge_Compile._Istate _out12;
            _out12 = Bridge_Compile.__default.Reset__Cross__Counter(s_k);
            s_k = _out12;
            Bridge_Compile._Istate _out13;
            _out13 = Bridge_Compile.__default.Cross(s_k);
            s_k = _out13;
          }
        }
      }
      return s_k;
    }
  }
} // end of namespace Bridge_Compile
namespace _module {

} // end of namespace _module
