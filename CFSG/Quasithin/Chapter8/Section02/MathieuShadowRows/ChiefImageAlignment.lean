module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.Kernel

/-!
# Comparing the literal chief action images

The reduced image kernel lies in the solvable canonical core of a minimal
parabolic, so a nontrivial irreducible FF image detects solvability of its
original group. Equal kernels also give an equivalence of the actual images
which commutes with the original maps and preserves every subgroup image.
This supplies actor transport for 3.1.9(6), without identifying modules.
Source: Aschbacher--Smith, B.6.9 and 3.1.9, pp.115--116 and 577--578.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterB
universe u
variable {H W W' : Type u} [Group H] [Finite H]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [AddCommGroup W'] [Module (ZMod 2) W'] [FiniteDimensional (ZMod 2) W']

/-- An equivalence between two literal chief-action images, preserving the
original maps and all subgroup images. -/
structure LiteralChiefActionEquiv
    (ρ : Representation (ZMod 2) H W) (σ : Representation (ZMod 2) H W') where
  equiv : actionImage ρ ≃* actionImage σ
  map_action : ∀ x, equiv (actionHom ρ x) = actionHom σ x
  map_subgroup : ∀ A : Subgroup H,
    (actionSubgroup ρ A).map equiv.toMonoidHom = actionSubgroup σ A

/-- An irreducible faithful-image action of a minimal parabolic is solvable
exactly when the original parabolic is solvable. -/
theorem chief_image_solvable_iff
    (S : Sylow 2 H) (hp : IsMinimalParabolicOver S ⊤)
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hff : IsFFModule (imageRepresentation ρ)) :
    Group.IsSolvable (actionImage ρ) ↔ Group.IsSolvable H := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  constructor
  · intro hs
    have hn : q.ker ≠ ⊤ := by
      intro he
      obtain ⟨A,hA⟩ := hff
      obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
      obtain ⟨x,hx⟩ := hq (a : actionImage ρ)
      apply ha
      apply Subtype.ext
      change (a : actionImage ρ) = 1
      rw [←hx]
      exact (show x ∈ q.ker from he ▸ mem_top x)
    have hk := (minimalParabolic_reduced_image S hp q hq
      (irreducible_image_twoCore_eq_bot ρ) hn).1
    let := minimalParabolic_core_solvable S hp
    let : Group.IsSolvable q.ker :=
      Group.isSolvable_of_isSolvable_injective (inclusion_injective hk)
    let := hs
    let : Group.IsSolvable (H ⧸ q.ker) := Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective q hq).symm.surjective
    exact (Group.isSolvable_iff_subgroup_quotient q.ker).mpr
      ⟨inferInstance, inferInstance⟩
  · intro hs
    let := hs
    exact Group.isSolvable_of_surjective (f := q) hq

omit [Finite H] [FiniteDimensional (ZMod 2) W] [FiniteDimensional (ZMod 2) W'] in
/-- Two irreducible actions with the same kernel have a quotient equivalence
preserving the original actions. -/
theorem chief_equiv_of_kernel_eq
    (ρ : Representation (ZMod 2) H W)
    (σ : Representation (ZMod 2) H W')
    (hker : (actionHom ρ).ker = (actionHom σ).ker) :
    Nonempty (LiteralChiefActionEquiv ρ σ) := by
  let eρ := QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
    ρ.asGroupHom.rangeRestrict_surjective
  let eσ := QuotientGroup.quotientKerEquivOfSurjective (actionHom σ)
    σ.asGroupHom.rangeRestrict_surjective
  let e := (eρ.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)).trans eσ
  have he (x : H) : e (actionHom ρ x) = actionHom σ x := by
    have hp : eρ.symm (actionHom ρ x) = QuotientGroup.mk x := by
      apply eρ.injective
      calc
        eρ (eρ.symm (actionHom ρ x)) = actionHom ρ x := Equiv.apply_symm_apply _ _
        _ = eρ (QuotientGroup.mk x) := by
          simp [eρ, QuotientGroup.quotientKerEquivOfSurjective,
            QuotientGroup.kerLift_mk]
    change eσ (QuotientGroup.quotientMulEquivOfEq hker
      (eρ.symm (actionHom ρ x))) = actionHom σ x
    rw [hp]
    simp [eσ, QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.kerLift_mk]
  have hsub (A : Subgroup H) :
      (actionSubgroup ρ A).map e.toMonoidHom = actionSubgroup σ A := by
    change (A.map (actionHom ρ)).map e.toMonoidHom = A.map (actionHom σ)
    rw [map_map]
    congr 1
    exact MonoidHom.ext he
  exact ⟨⟨e, he, hsub⟩⟩

end CFSG.Quasithin.Chapter8.MathieuShadowRows
