module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import Theory.Representation.BinaryPermutation.EightGeometry

/-!
# A nonsingular point in a large original subgroup

An actual subgroup A of the original V embeds linearly in the marked
six-space when C_V(L) is trivial. If every element of A were singular,
the nondegenerate polar form would bound its dimension by three, hence
its order by eight. Thus any larger original subgroup contains a
nonsingular point. No HS or ambient centralizer hypothesis is needed.

Source: the weight-four/rank-three geometry in Aschbacher--Smith 12.6.20,
printed pp.828--829.
-/

public noncomputable section
open Subgroup BinaryPermutation
open BinaryPermutation.TerminalOrthogonal.Eight
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {L V : Subgroup G} [IsElementaryAbelian 2 V]
variable {hn : L ≤ normalizer (V : Set G)}

/-- A subgroup of the unchanged full module with more than eight elements
contains a nonsingular point for the original action marking. -/
theorem OrthogonalMarking.exists_nonsingular_of_card_gt_eight
    (D : OrthogonalMarking L V hn) (hZ : ZV L V = ⊥)
    (A : Subgroup G) (hAV : A ≤ V) (hcard : 8 < Nat.card A) :
    ∃ u : V, D.Nonsingular u ∧ (u : G) ∈ A := by
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAV
  let f : Additive A →ₗ[ZMod 2] natural (Fin 8) :=
    (D.fullLinearCoordinates hZ).toLinearMap.comp
      ((inclusion hAV).toAdditive.toZModLinearMap 2)
  have hf : Function.Injective f := by
    intro a b he
    have hab := (D.fullLinearCoordinates hZ).injective he
    exact Additive.toMul.injective ((inclusion_injective hAV)
      (congrArg Additive.toMul hab))
  by_contra hnone
  have hs : ∀ x ∈ f.range, form x = 0 := by
    rintro _ ⟨a,rfl⟩
    apply not_ne_iff.mp
    intro ha
    apply hnone
    refine ⟨inclusion hAV a.toMul,?_,a.toMul.property⟩
    exact (D.fullCoordinates_nonsingular_iff hZ _).mp ha
  have hd := EightGeometry.finrank_singular_le f.range hs
  rw [LinearMap.finrank_range_of_inj hf] at hd
  have hc : Nat.card A ≤ 8 := by
    rw [←Nat.card_congr (Additive.toMul : Additive A ≃ A),
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide) hd
  omega

end CFSG.Quasithin.Chapter12.Section06
