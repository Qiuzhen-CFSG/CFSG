module
public import Theory.GroupTheory.ExtraspecialSquare
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.SpecificGroups.ClassicalOrthogonal.BinarySixCoordinates
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport

/-!
# Plus coordinates for an extraspecial group of order 128

An elementary subgroup of order sixteen has an image of order at least eight
in the actual central quotient. The minus six-space has no singular subspace
of dimension three, so the square form is of plus type. Transporting the
existing square action through this isometry gives the original automorphism
action in the split orthogonal group, with exactly the inner automorphisms
as kernel. The coordinates retain the square values and the action on P/Z(P).
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup
namespace Theory.GroupTheory.ExtraspecialSquare
variable (P : Type*) [Group P] [Finite P] [IsExtraspecial 2 P]

/-- An elementary subgroup of order sixteen forces the actual square form
of an extraspecial group of order 128 to have plus type. -/
theorem plus_six_coordinates (hP : Nat.card P = 128)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) :
    Nonempty ((form P).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2))) := by
  let S := imageSpace P A
  have hScard : Nat.card S = Nat.card (A.map (QuotientGroup.mk' (center P))) := by
    exact Nat.card_congr {
      toFun := fun v => ⟨v.val.toMul,v.property⟩
      invFun := fun v => ⟨Additive.ofMul v.val,v.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hkernel : Nat.card (A ⊓ center P : Subgroup P) ≤ 2 :=
    (card_le_of_le (show A ⊓ center P ≤ center P from inf_le_right)).trans_eq
      (IsExtraspecial.center_order_p 2 P)
  have hsize : 16 ≤ 2 * Nat.card S := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map
      A (QuotientGroup.mk' (center P))
    rw [QuotientGroup.ker_mk',←hScard,hA] at hh
    exact hh ▸ Nat.mul_le_mul_right (Nat.card S) hkernel
  have hdim : 3 ≤ Module.finrank (ZMod 2) S := by
    by_contra! hl
    have hc : Nat.card S ≤ 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      change 2 ^ Module.finrank (ZMod 2) S ≤ 2^2
      exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
    omega
  have hd : Module.finrank (ZMod 2) (Space P) = 6 :=
    space_finrank P 6 (by simpa using hP)
  rcases QuadraticForm.BinarySixCoordinates.classify (form P)
      (polar_nondegenerate P) hd with hp | hm
  · exact hp
  · obtain ⟨e⟩ := hm
    let W := S.map e.toLinearEquiv.toLinearMap
    have hs : ∀ v ∈ W, ClassicalOrthogonal.Minus.form (ZMod 2) 2 1 v = 0 := by
      rintro v ⟨u,hu,rfl⟩
      rw [←ClassicalOrthogonal.Minus.BinarySixObstruction.naturalForm_eq]
      exact (e.map_app u).trans (imageSpace_singular P A u hu)
    have hb := ClassicalOrthogonal.Minus.singular_finrank_le (ZMod 2) 2 1
      (by decide : ∀ t : ZMod 2, t^2+t ≠ 1) W hs
    have he : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) S :=
      e.toLinearEquiv.finrank_map_eq S
    have hb' : Module.finrank (ZMod 2) S ≤ 2 := he.symm.trans_le hb
    omega

/-- The same plus isometry transports the actual central-quotient action;
its full kernel consists precisely of the inner automorphisms. -/
theorem plus_six_automorphism_action (hP : Nat.card P = 128)
    (A : Subgroup P) [IsElementaryAbelian 2 A] (hA : Nat.card A = 16) :
    ∃ e : (form P).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)),
      ∃ f : MulAut P →* Atlas.Order20160A8.O_DPlus 3 (ZMod 2),
        f.ker = (MulAut.conj : P →* MulAut P).range ∧
        ∀ (a : MulAut P) (v : P ⧸ center P),
          (f a).val (e (Additive.ofMul v)) =
            e (Additive.ofMul (quotientAut (center P) a v)) := by
  obtain ⟨e⟩ := plus_six_coordinates P hP A hA
  have heq : (ClassicalOrthogonal.formD 3 (ZMod 2)).isometrySubgroup =
      quadraticIsometrySubgroup (ClassicalOrthogonal.formD 3 (ZMod 2)) := by
    ext g
    exact (QuadraticMap.mem_isometrySubgroup _ g).trans
      (mem_quadraticIsometrySubgroup _ g).symm
  let j := e.isometrySubgroupCongr.trans (MulEquiv.subgroupCongr heq)
  let f := j.toMonoidHom.comp (isometryAction P)
  have hk : f.ker = (quotientAut (center P)).ker := by
    ext a
    change j (isometryAction P a) = 1 ↔ quotientAut (center P) a = 1
    rw [j.map_eq_one_iff,isometryAction_eq_one_iff]
  refine ⟨e,f,hk.trans (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p := 2)),?_⟩
  intro a v
  change (e.isometrySubgroupCongr (isometryAction P a)).val (e (Additive.ofMul v)) = _
  rw [e.isometrySubgroupCongr_intertwines,isometryAction_apply]

end Theory.GroupTheory.ExtraspecialSquare
