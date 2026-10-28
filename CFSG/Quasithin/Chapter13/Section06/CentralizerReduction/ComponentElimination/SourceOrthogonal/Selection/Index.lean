module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Residual
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank

/-!
# The ambient prime-to-three index of the rank-four component

The source component K is represented inside Gᵥ, with normality relative
to Gᵥ. Its actual SL₄(2) two-core quotient has three-rank at least two,
trivial center and a two-group outer group. The proved centerless argument
of A.3.18 therefore gives index prime to three, without assuming either
that index or the ambient residual equality.

The residual theorem applies this calculation to the literal subgroup of
Gᵥ. Establishing that K is the containing ambient C-component and constructing
its intrinsic SL₄(2) quotient remain source obligations; an isomorphism
for the action image K⁺ alone does not supply them.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.18, printed pp.51–52, and 13.6.23(1), printed p.933.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection BinaryLinear.OuterCyclic Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem outer_four_isTwoGroup : IsPGroup 2 (MulAut.Outer SL(4, ZMod 2)) := by
  have hh : IsPGroup 2 (MulAut.Outer (LinearGroup 4)) := by
    intro x
    refine ⟨1, ?_⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup (LinearGroup 4)) x
    let q := QuotientGroup.mk' (MulAut.innerSubgroup (LinearGroup 4))
    obtain ⟨g, rfl | rfl⟩ := inner_graph (Or.inl rfl) a
    · have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
      change (q (MulAut.conj g)) ^ (2 ^ 1) = 1
      rw [hi, one_pow]
    · have hi : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
      change (q (graphLinear 4 * MulAut.conj g)) ^ (2 ^ 1) = 1
      rw [map_mul, hi, mul_one, pow_one, ← map_pow, graphLinear_sq, map_one]
  exact hh.of_equiv (MulAut.outerCongr (slEquivLinear 4)).symm

/-- The centerless case of A.3.18, with every binary-model premise discharged. -/
theorem relative_component_index_coprime
    (K T : Subgroup G) (v : G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hC : (K.subgroupOf (Gv v)).IsCComponent)
    (hn : Gv v ≤ normalizer (K : Set G))
    (e : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (hr : primeRank 3 (Gv v) ≤ 2) :
    Nat.Coprime 3 (K.subgroupOf (Gv v)).index := by
  let B := K.subgroupOf (Gv v)
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hK.1).mpr hn
  let f : B ≃* K := subgroupOfEquivOfLe hK.1
  let eq : B ⧸ pCore 2 B ≃* SL(4, ZMod 2) :=
    (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).trans e
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : eq x ∈ center SL(4, ZMod 2) := (centerCongr eq ⟨x, hx⟩).property
    rw [binary_center_eq_bot (by decide : 0 < 4), mem_bot] at hh
    exact eq.map_eq_one_iff.mp hh
  have hq : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    rw [primeRank_congr 3 eq]
    exact BinaryLinear.SmallCubicRank.four
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (B ⧸ pCore 2 B))) := by
    rw [Nat.card_congr (MulAut.outerCongr eq).toEquiv]
    obtain ⟨n, hn⟩ := outer_four_isTwoGroup.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  exact cComponent_index_coprime_three_of_quotient B hC hz hq hr ho

/-- Assertion 13.6.23(1) from the actual ambient component comparison and
intrinsic quotient. Neither relative subnormality nor the index is assumed. -/
theorem component_eq_primeToResidual_of_ambient_component
    (K T : Subgroup G) (v : G)
    (hK : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hC : (K.subgroupOf (Gv v)).IsCComponent)
    (hn : Gv v ≤ normalizer (K : Set G))
    (e : K ⧸ pCore 2 K ≃* SL(4, ZMod 2))
    (hr : primeRank 3 (Gv v) ≤ 2) :
    K = (primeToResidual 3 (Gv v)).map (Gv v).subtype :=
  component_eq_primeToResidual T K v hK e hC.subnormal
    (relative_component_index_coprime K T v hK hC hn e hr)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
