module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.QuotientTools
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Coordinates
/-!
# Full movement by the first tensor actor

Source: Aschbacher–Smith, proof of Lemma 14.4.10, printed p.1010,
combined manuscript of 1 March 2004: [Ũ,X₁] = Ũ.

The marked cubic of the S₃ factor belongs to the actual star image of X₁.
Every tensor is a cubic displacement. Lift its displacement preimage to U
and the cubic actor to X₁; the literal conjugation compatibility then puts
every central-quotient element in the image of [U,X₁].

Extraspeciality and normalization force Z(U) into this nontrivial commutator,
so [U,X₁] = U and U ≤ X₁. These conclusions require only the specified action
coordinates and extraspeciality, not a chief-factor or family certificate.
The quotient plane moved from V₂ and its containment in E are separate
calculations needed to finish X₁ ∈ Y.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {G : Type*} [Group G] [Finite G]

namespace CaseFiveCoordinates
variable {D : Subgroup Five} {hAD : AltFive ≤ D}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {H U : Subgroup G} (c : CaseFiveCoordinates hAD (V := V) H U)

include c

open scoped commutatorElement

/-- The whole literal U/Z(U) is moved by X₁. -/
theorem first_moves_centralQuotient : tilde U (movedSpace U (first H)) = ⊤ := by
  obtain ⟨h, hh, hqa⟩ := c.marked_cubic_mem_star_first
  let z (y : U ⧸ center U) := (c.space y).toAdd
  apply top_unique
  intro y _
  obtain ⟨u, hu⟩ := c.quotientMap_surjective
    (Multiplicative.ofAdd (sourceTensorAction c.constituent (InvertedCubicTensor.cubic, 1) (z y)))
  let v : U := ⟨(h : G) * u * (h : G)⁻¹,
    le_normalizer_iff.mp c.H_normalizes_U h h.property u u.property⟩
  have ha : c.actor (QuotientGroup.mk' (pCore 2 H) h) = (InvertedCubicTensor.cubic, 1) := by
    rw [hqa, c.actor.apply_symm_apply]
  have hv : c.quotientMap v = Multiplicative.ofAdd
      (sourceTensorAction c.constituent (InvertedCubicTensor.cubic, 1)
        (c.quotientMap u).toAdd) := by
    have he := c.equivariant h u
    rw [ha] at he
    exact he
  have hm : ((v * u⁻¹ : U) : G) ∈ movedSpace U (first H) := by
    change ⁅(h : G), (u : G)⁆ ∈ ⁅U, first H⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hh u.property
  refine mem_map.mpr ⟨v * u⁻¹, hm, ?_⟩
  apply c.space.injective
  change c.quotientMap (v * u⁻¹) = c.space y
  rw [map_mul, map_inv, hv, hu]
  change Multiplicative.ofAdd
    (sourceTensorAction c.constituent (InvertedCubicTensor.cubic, 1)
      (sourceTensorAction c.constituent (InvertedCubicTensor.cubic, 1) (z y)) -
        sourceTensorAction c.constituent (InvertedCubicTensor.cubic, 1) (z y)) = c.space y
  rw [sourceTensor_cubic_displacement]
  rfl

/-- The central kernel lifts full quotient movement to [U,X₁] = U. -/
theorem commutator_first_eq [IsExtraspecial 2 U] : movedSpace U (first H) = U := by
  have hMU : movedSpace U (first H) ≤ U :=
    le_normalizer_iff_commutator_le_left.mp ((first_le H).trans c.H_normalizes_U)
  have hn : U ≤ normalizer (first H : Set G) :=
    c.U_le_H.trans (first_T_normalized (H := H) (T := H) le_rfl)
  have hne : tilde U (movedSpace U (first H)) ≠ ⊥ := by
    rw [c.first_moves_centralQuotient]
    let _ := IsExtraspecial.quotient_nontrivial 2 U
    exact top_ne_bot
  have hz := extraspecial_center_le_commutator_of_image_ne_bot U U (first H) le_rfl
    (show center U ≤ U.subgroupOf U by simp only [subgroupOf_self, le_top]) hn
    (QuotientGroup.mk' (center U)) hne
  have hfull : (movedSpace U (first H)).subgroupOf U = ⊤ := by
    have he := congrArg (fun B : Subgroup (U ⧸ center U) =>
      B.comap (QuotientGroup.mk' (center U))) c.first_moves_centralQuotient
    change (((movedSpace U (first H)).subgroupOf U).map (QuotientGroup.mk' (center U))).comap
      (QuotientGroup.mk' (center U)) = _ at he
    rw [comap_map_eq_self (by simpa only [QuotientGroup.ker_mk', movedSpace] using hz),
      comap_top] at he
    exact he
  exact le_antisymm hMU (subgroupOf_eq_top.mp hfull)

/-- The actual first residual contains the whole extraspecial subgroup. -/
theorem U_le_first [IsExtraspecial 2 U] : U ≤ first H := by
  rw [← c.commutator_first_eq]
  exact le_normalizer_iff_commutator_le_right.mp
    (c.U_le_H.trans (first_T_normalized (H := H) (T := H) le_rfl))

end CaseFiveCoordinates

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor

end
