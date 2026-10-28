module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup

/-!
# The S₃ alternative of the cubic classification deduction

An S₃ group has exactly one subgroup of order three, since an index-two
subgroup is its alternating subgroup. That uniqueness makes the cubic
characteristic in the normal offender subgroup, hence normal in D.
Its moved space lies in the supplied two-dimensional S₃ moved space;
the general faithful cubic lower bound gives equality.

Source: Aschbacher–Smith B.5.6(2), printed p.105, as used in
13.6.10, printed p.928. The other B.5.6 branches are not asserted here.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
variable {D : Type*} [Group D]
private theorem s3_unique (e : D ≃* Equiv.Perm (Fin 3)) (A B : Subgroup D)
    (ha : Nat.card A = 3) (hb : Nat.card B = 3) : A = B := by
  apply map_injective (f := e.toMonoidHom) e.injective
  have hd : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  have ai : (A.map e.toMonoidHom).index = 2 := by
    rw [index_map_of_bijective e.bijective]
    have := A.index_mul_card
    rw [ha, hd] at this
    omega
  have bi : (B.map e.toMonoidHom).index = 2 := by
    rw [index_map_of_bijective e.bijective]
    have := B.index_mul_card
    rw [hb, hd] at this
    omega
  exact (Equiv.Perm.eq_alternatingGroup_of_index_eq_two ai).trans
    (Equiv.Perm.eq_alternatingGroup_of_index_eq_two bi).symm
private theorem normal_s3 (J A : Subgroup D) [J.Normal] (hle : A ≤ J)
    (hcard : Nat.card A = 3) (e : J ≃* Equiv.Perm (Fin 3)) : A.Normal := by
  let B := A.subgroupOf J
  have hc : Nat.card B = 3 := (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hcard
  have hchar : B.Characteristic := characteristic_iff_map_eq.mpr (by
    intro f
    exact s3_unique e _ B ((card_map_of_injective f.injective).trans hc) hc)
  let := hchar
  have hn : (B.map J.subtype).Normal := ConjAct.normal_of_characteristic_of_normal
  simpa only [B, map_subgroupOf_eq_of_le hle] using hn

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)

omit [FiniteDimensional (ZMod 2) W] in
/-- The cubic is normal in the original ambient group in B.5.6(2). -/
theorem symmetricThree_normal {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SymmetricThreeCase (offenderRepresentation ρ)) : A.Normal :=
  normal_s3 (offenderSubgroup ρ) A h.le_offender h.card hc.equiv

/-- Both required bounds, on the original action and ambient normalizer. -/
theorem symmetricThree_bounds {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : SymmetricThreeCase (offenderRepresentation ρ)) :
    Module.finrank (ZMod 2) (moved ρ A) = 2 ∧ (normalizer (A : Set D)).index ≤ 2 := by
  have hle : moved ρ A ≤ moved (offenderRepresentation ρ) ⊤ := by
    change subspaceCommutator ρ ⊤ A ≤ subspaceCommutator (offenderRepresentation ρ) ⊤ ⊤
    rw [← marked_commutator ρ A h.le_offender ⊤]
    apply Submodule.span_mono
    rintro _ ⟨a, _, v, hv, rfl⟩
    exact ⟨a, Subgroup.mem_top _, v, hv, rfl⟩
  have hu := Submodule.finrank_mono hle
  rw [hc.dimension] at hu
  refine ⟨le_antisymm hu h.two_le_moved, ?_⟩
  rw [normalizer_eq_top_iff.mpr (symmetricThree_normal ρ h hc), index_top]
  decide

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
