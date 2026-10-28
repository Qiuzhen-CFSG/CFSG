module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.Residual
public import Theory.SpecificGroups.Held.LocalPairs.Transport
public import Theory.SpecificGroups.Held.Automorphisms.Reduction
public import Mathlib.GroupTheory.IndexNormal

/-!
# Reducing Held interval normalizers to inner calculations

A Frattini argument controls the full automorphism normalizer of a subgroup
normalized by a Sylow two-subgroup: it suffices to control its inner
normalizer and the full normalizer of that Sylow subgroup. Subgroups of
relative index at most two meet the required relative normality condition.

One genuinely outer actor preserving the pair, together with control of
the inner Sylow normalizer, controls its full normalizer using the bound
of two on the full permutation-normalizer quotient. Pair-preserving actors
preserve the embedded O²(RS); the two-core is not substituted for this residual.

These are conditional reductions. The concrete inner normalizers and
existence of an outer pair actor remain separate obligations. Inner
self-normalization is sufficient but unnecessary: the interval calculation
at S already controls its inner normalizer. In particular the unrestricted
PairInput-only interval claim is not asserted.

Sources: the Frattini argument in Aschbacher–Smith, printed pp.747–748,
and the full outer-group bound in GLS3, Table 5.3p. The application is the
additional Held case retained in the invariant-three sieve at printed p.511.
-/

public section

open Subgroup
open scoped Pointwise

namespace Held.LocalPairs.PairCoverage.IntervalNormalizer

/-- Adjust an automorphism by an inner normalizer element so that it also
preserves S, using Sylow conjugacy inside the normalizer of U. -/
theorem automorphismNormalizer_le_of_inner_and_sylow (S : Sylow 2 Held.He) (U X : Subgroup Held.He)
    (hSU : (S : Subgroup Held.He) ≤ normalizer (U : Set Held.He))
    (hinner : normalizer (U : Set Held.He) ≤ normalizer (X : Set Held.He))
    (hS : automorphismNormalizer S ≤ automorphismNormalizer X) :
    automorphismNormalizer U ≤ automorphismNormalizer X := by
  intro a ha
  have haU : U.map a.toMonoidHom = U := ha
  have haN : (normalizer (U : Set Held.He)).map a.toMonoidHom =
      normalizer (U : Set Held.He) := by
    rw [map_equiv_normalizer_eq, haU]
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  have hS'U : (S' : Subgroup Held.He) ≤ normalizer (U : Set Held.He) := by
    change (S : Subgroup Held.He).map a.toMonoidHom ≤ _
    rw [← haN]
    exact map_mono hSU
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (normalizer (U : Set Held.He))
    (S'.subtype hS'U) (S.subtype hSU)
  rw [Sylow.smul_subtype] at hg
  have he : (g : Held.He) • S' = S := Sylow.subtype_injective hg
  have hga : MulAut.conj (g : Held.He) * a ∈ automorphismNormalizer S := by
    change (S : Subgroup Held.He).map
      (MulAut.conj (g : Held.He) * a).toMonoidHom = _
    have hm := congrArg (fun T : Sylow 2 Held.He => (T : Subgroup Held.He)) he
    change ((S : Subgroup Held.He).map a.toMonoidHom).map
      (MulAut.conj (g : Held.He)).toMonoidHom = _ at hm
    rw [map_map] at hm
    exact hm
  have hgX : MulAut.conj (g : Held.He) ∈ automorphismNormalizer X :=
    mem_normalizer_iff_map_conj_eq.mp (hinner g.property)
  have hh := (automorphismNormalizer X).mul_mem
    ((automorphismNormalizer X).inv_mem hgX) (hS hga)
  simpa only [inv_mul_cancel_left] using hh

private theorem normalized_of_index (S U : Subgroup Held.He) (hUS : U ≤ S)
    (hindex : U.relIndex S ≤ 2) : S ≤ normalizer (U : Set Held.He) := by
  have hpos : 0 < (U.subgroupOf S).index := Nat.pos_of_ne_zero
    (U.subgroupOf S).index_ne_zero_of_finite
  have hidx : (U.subgroupOf S).index = 1 ∨ (U.subgroupOf S).index = 2 := by
    change (U.subgroupOf S).index ≤ 2 at hindex
    omega
  have hnormal : (U.subgroupOf S).Normal := hidx.elim
    (normal_of_index_eq_one) (normal_of_index_eq_two)
  exact (normal_subgroupOf_iff_le_normalizer hUS).mp hnormal

/-- A single outer actor and control of the inner normalizer exhaust the
full Sylow normalizer, since the genuine outer quotient has order at most two. -/
theorem automorphismNormalizer_sylow_le_of_inner_and_outer
    (S : Sylow 2 Held.He) (X : Subgroup Held.He)
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hinner : normalizer (S : Set Held.He) ≤ normalizer (X : Set Held.He))
    (a : MulAut Held.He) (haS : a ∈ automorphismNormalizer S)
    (haX : a ∈ automorphismNormalizer X) (hout : a ∉ MulAut.innerSubgroup Held.He) :
    automorphismNormalizer S ≤ automorphismNormalizer X := by
  have hcard : (MulAut.innerSubgroup Held.He).index ≤ 2 :=
    (Nat.card_le_card_of_surjective _
      (normalizerOuterAction_surjective Held.permutationGroup hrealize)).trans hbound
  have htwo : (MulAut.innerSubgroup Held.He).index = 2 := by
    have hpos := (MulAut.innerSubgroup Held.He).index_ne_zero_of_finite
    have hone : (MulAut.innerSubgroup Held.He).index ≠ 1 := by
      intro he
      exact hout ((index_eq_one.mp he).symm ▸ mem_top a)
    omega
  have hin : ∀ b ∈ automorphismNormalizer S, b ∈ MulAut.innerSubgroup Held.He →
      b ∈ automorphismNormalizer X := by
    rintro b hb ⟨g, rfl⟩
    have hg : g ∈ normalizer (S : Set Held.He) := mem_normalizer_iff_map_conj_eq.mpr hb
    exact mem_normalizer_iff_map_conj_eq.mp (hinner hg)
  intro b hb
  by_cases hbi : b ∈ MulAut.innerSubgroup Held.He
  · exact hin b hb hbi
  have hba : b * a⁻¹ ∈ MulAut.innerSubgroup Held.He := by
    rw [mul_mem_iff_of_index_two htwo, inv_mem_iff]
    exact iff_of_false hbi hout
  have hbaX := hin (b * a⁻¹)
    ((automorphismNormalizer S).mul_mem hb ((automorphismNormalizer S).inv_mem haS)) hba
  simpa only [inv_mul_cancel_right] using (automorphismNormalizer X).mul_mem hbaX haX

/-- Inner self-normalization is one sufficient way to control the inner
Sylow normalizer; it is not required by the general reduction. -/
theorem automorphismNormalizer_sylow_le_of_outer (S : Sylow 2 Held.He) (X : Subgroup Held.He)
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (hself : normalizer (S : Set Held.He) = (S : Subgroup Held.He))
    (hSX : (S : Subgroup Held.He) ≤ normalizer (X : Set Held.He))
    (a : MulAut Held.He) (haS : a ∈ automorphismNormalizer S)
    (haX : a ∈ automorphismNormalizer X) (hout : a ∉ MulAut.innerSubgroup Held.He) :
    automorphismNormalizer S ≤ automorphismNormalizer X := by
  apply automorphismNormalizer_sylow_le_of_inner_and_outer S X hrealize hbound
    (hself ▸ hSX) a haS haX hout

/-- The whole pair product normalizes its relative residual. -/
theorem pairProduct_le_normalizer_residual (S R : Subgroup Held.He) :
    R ⊔ S ≤ normalizer (residual S R : Set Held.He) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact automorphismNormalizer_join_le S R
    (mem_normalizer_iff_map_conj_eq.mp ((R ⊔ S).le_normalizer hg))

/-- A genuinely outer pair-preserving permutation controls the full
Sylow normalizer once its inner normalizer is controlled. -/
theorem automorphismNormalizer_sylow_le_of_inner_and_outer_pair
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (hinner : normalizer (S : Set Held.He) ≤ normalizer (residual S R : Set Held.He))
    (a : permutationPairStabilizer S R) (hout : a.val.val ∉ Held.permutationGroup) :
    automorphismNormalizer S ≤ automorphismNormalizer (residual S R) := by
  apply automorphismNormalizer_sylow_le_of_inner_and_outer S (residual S R)
    hrealize hbound hinner
    (Held.permutationGroup.normalizerMonoidHom a.val) a.property.1
  · apply automorphismNormalizer_join_le S R
    change (R ⊔ (S : Subgroup Held.He)).map
      (Held.permutationGroup.normalizerMonoidHom a.val).toMonoidHom = _
    have haR : R.map (Held.permutationGroup.normalizerMonoidHom a.val).toMonoidHom = R :=
      a.property.2
    have haS : (S : Subgroup Held.He).map
        (Held.permutationGroup.normalizerMonoidHom a.val).toMonoidHom = S := a.property.1
    rw [Subgroup.map_sup, haR, haS]
  · exact fun hin => hout ((normalizerAction_mem_inner_iff a.val).mp hin)

/-- The self-normalizing special case of the outer-pair reduction. -/
theorem automorphismNormalizer_sylow_le_of_outer_pair
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R : Subgroup Held.He)
    (hself : normalizer (S : Set Held.He) = (S : Subgroup Held.He))
    (a : permutationPairStabilizer S R) (hout : a.val.val ∉ Held.permutationGroup) :
    automorphismNormalizer S ≤ automorphismNormalizer (residual S R) := by
  apply automorphismNormalizer_sylow_le_of_inner_and_outer_pair hrealize hbound S R
    _ a hout
  rw [hself]
  exact le_sup_right.trans (pairProduct_le_normalizer_residual S R)

/-- Frattini and the outer pair actor reduce an interval normalizer to two
inner normalizers. The calculation at S needs no self-normalizer equality. -/
theorem automorphismNormalizer_interval_le_of_inner_and_outer_pair
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R R2 : Subgroup Held.He)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2)
    (hinnerS : normalizer (S : Set Held.He) ≤ normalizer (residual S R : Set Held.He))
    (hinnerR2 : normalizer (R2 : Set Held.He) ≤ normalizer (residual S R : Set Held.He))
    (a : permutationPairStabilizer S R) (hout : a.val.val ∉ Held.permutationGroup) :
    automorphismNormalizer R2 ≤ automorphismNormalizer (residual S R) := by
  exact automorphismNormalizer_le_of_inner_and_sylow S R2 (residual S R)
    (normalized_of_index S R2 hR2S hindex) hinnerR2
    (automorphismNormalizer_sylow_le_of_inner_and_outer_pair hrealize hbound S R hinnerS a hout)

/-- Only the inner normalizer of the particular interval subgroup remains
after an outer pair actor and inner Sylow self-normalization are supplied.
The lower two-core bound is needed by that inner calculation, not by Frattini. -/
theorem automorphismNormalizer_interval_le_of_outer_pair
    (hrealize : Function.Surjective Held.permutationGroup.normalizerMonoidHom)
    (hbound : Nat.card Held.PermutationNormalizerQuotient ≤ 2)
    (S : Sylow 2 Held.He) (R R2 : Subgroup Held.He)
    (hself : normalizer (S : Set Held.He) = (S : Subgroup Held.He))
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2)
    (hinner : normalizer (R2 : Set Held.He) ≤ normalizer (residual S R : Set Held.He))
    (a : permutationPairStabilizer S R) (hout : a.val.val ∉ Held.permutationGroup) :
    automorphismNormalizer R2 ≤ automorphismNormalizer (residual S R) := by
  exact automorphismNormalizer_le_of_inner_and_sylow S R2 (residual S R)
    (normalized_of_index S R2 hR2S hindex) hinner
    (automorphismNormalizer_sylow_le_of_outer_pair hrealize hbound S R hself a hout)

/-- Transport a complete interval calculation through an actual automorphism.
The lower bound is the transported two-core of the residual, and the
relative index is preserved by the same injective map. -/
theorem automorphismNormalizer_interval_le_of_map (S R : Subgroup Held.He) (e : MulAut Held.He)
    (h : ∀ U : Subgroup Held.He,
      twoCore (S.map e.toMonoidHom) (R.map e.toMonoidHom) ≤ U →
      U ≤ S.map e.toMonoidHom → U.relIndex (S.map e.toMonoidHom) ≤ 2 →
        automorphismNormalizer U ≤
          automorphismNormalizer (residual (S.map e.toMonoidHom) (R.map e.toMonoidHom)))
    (R2 : Subgroup Held.He) (hQR2 : twoCore S R ≤ R2)
    (hR2S : R2 ≤ S) (hindex : R2.relIndex S ≤ 2) :
    automorphismNormalizer R2 ≤ automorphismNormalizer (residual S R) := by
  apply automorphismNormalizer_le_of_map e R2 (residual S R)
  rw [residual_map]
  apply h (R2.map e.toMonoidHom)
  · rw [← twoCore_map]
    exact map_mono hQR2
  · exact map_mono hR2S
  · simpa only [relIndex_map_map_of_injective (f := e.toMonoidHom) R2 S e.injective]
      using hindex

end Held.LocalPairs.PairCoverage.IntervalNormalizer
