module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.EvenTwisted.Triality.Inputs
public import Theory.Representation.CharacteristicTwoIrreducibleRank.InnerInvolutions
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.OddExponent
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage

/-!
# No outer involutions at odd triality exponent

For `q = 2^n` with `n` odd, the genuine carrier's coefficient automorphism
group has odd order `3*n`. Coverage by inner and coefficient automorphisms
therefore makes every automorphism of square one inner. Perfectness lifts
this assertion through the component's actual central quotient.

Over any characteristic-two coefficient field, irreducibility on the
component eliminates centralizing involutions and makes its center's square
map bijective. Correcting an inner representative by a central square root
then places the original ambient involution in the component. Thus the
outer displacement bound is vacuous for odd `n`, including `q = 2`.

Source: Guralnick--Malle, *Classification of 2F-modules, II*, Lemma 8.6,
internal pp.56--57; the automorphism description is GLS3 §2.5.
-/

public section

open Subgroup Representation

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality

universe u v

variable {H : Type u} [Group H] [Finite H] (N : Subgroup H) [N.Normal]
  [Group.IsPerfect N]

/-- Every actual ambient involution lies in the component at odd exponent;
no assumption on its central cover or on absolute component irreducibility is used. -/
theorem square_one_mem_of_odd {E W : Type v} [Field E] [CharP E 2]
    [AddCommGroup W] [Module E W] (σ : Representation E H W)
    [IsIrreducible (σ.comp N.subtype)] (hσ : Function.Injective σ)
    (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N))
    {t : H} (ht : t ^ 2 = 1) : t ∈ N := by
  obtain ⟨e⟩ := (_root_.Triality.Standard.isTrialityGroupAt_binary_iff
    (N ⧸ center N) n hn).mp hmodel
  let tN : normalizer (N : Set H) := ⟨t, by rw [normalizer_eq_top]; trivial⟩
  let a : MulAut N := N.normalizerMonoidHom tN
  let b := MulAut.centralQuotientAction e a
  have ha : a ^ 2 = 1 := by
    rw [← map_pow, show tN ^ 2 = 1 from Subtype.ext ht, map_one]
  have hb : b ^ (2 ^ 1) = 1 := by
    change (MulAut.centralQuotientAction e a) ^ (2 ^ 1) = 1
    rw [pow_one, ← map_pow, ha, map_one]
  have hinner := _root_.Triality.Standard.EvenInvolutionGeometry.inner_of_odd_exponent
    n hn hodd b hb (_root_.Triality.Standard.OuterOdd.Coverage.binary_inner_coefficient n hn b)
  have hi : ∃ x : N, a = MulAut.conj x :=
    (MulAut.centralQuotientAction_inner_iff e a).mp hinner
  exact CharacteristicTwoIrreducible.involution_mem_of_inner σ N hσ tN ht hi

/-- The proper-extension premise is discharged at every odd exponent. -/
theorem outerInvolutionBound_of_odd (n : ℕ) (hn : 0 < n) (hodd : Odd n)
    (hmodel : _root_.Triality.Standard.IsTrialityGroupAt (2 ^ n) (N ⧸ center N)) :
    OuterInvolutionBound.{u, v} H N n := by
  intro E W _ _ _ _ _ _ _ σ _ hirr hσ t htN ht2
  let : IsIrreducible (σ.comp N.subtype) := hirr
  exact (htN (square_one_mem_of_odd N σ hσ n hn hodd hmodel ht2)).elim

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.EvenTwisted.Triality
