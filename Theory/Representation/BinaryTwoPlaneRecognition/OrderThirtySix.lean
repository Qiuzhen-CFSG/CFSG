module

public import Theory.Representation.BinaryTwoPlaneRecognition
public import Theory.Representation.BinaryOffender.CubicRatio.Equivariant
public import Theory.Representation.BinaryOffender.RankOneNormalClosure


/-!
# An order-36 actor exhausts two permuted binary planes above ratio one

Complementary binary planes carry the orthogonal sum of their unique
anisotropic quadratic forms. Preserving their union embeds the faithful
actor in the actual isometry group of order 72. A subgroup of order 36
therefore exhausts the actor unless the actor is the full isometry group.
The latter contains an involution acting as a transvection on just one
plane. Its rank-one displacement gives an offender and cubic ratio at most
one, excluding that case under the strict lower ratio bound.

The coordinate embedding and action intertwining remain literal throughout.
Source: Aschbacher--Smith D.2.22, printed p.189.
-/

public section

open Subgroup OrthogonalFourBinary Theory.AlgebraicGroup
namespace Representation.BinaryTwoPlaneRecognition

private theorem form_eq_one_iff_axes : ∀ x : Space,
    form x = 1 ↔ x ≠ 0 ∧ (x.1 = 0 ∨ x.2 = 0) := by
  decide +kernel

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Union preservation gives the actual orthogonal embedding without an order premise. -/
theorem exists_isometry_embedding (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ)
    (A B : Submodule (ZMod 2) V) (hAB : IsCompl A B)
    (hA : Module.finrank (ZMod 2) A = 2) (hB : Module.finrank (ZMod 2) B = 2)
    (hunion : ∀ g v, (ρ g v ∈ A ∨ ρ g v ∈ B) ↔ (v ∈ A ∨ v ∈ B)) :
    ∃ (c : V ≃ₗ[ZMod 2] Space) (f : G →* TerminalLines.IsometryGroup),
      Function.Injective f ∧ ∀ g v, c (ρ g v) = (f g).val (c v) := by
  let a : A ≃ₗ[ZMod 2] Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) A hA).equivFun.trans (LinearEquiv.finTwoArrow _ _)
  let b : B ≃ₗ[ZMod 2] Plane :=
    (Module.finBasisOfFinrankEq (ZMod 2) B hB).equivFun.trans (LinearEquiv.finTwoArrow _ _)
  let c : V ≃ₗ[ZMod 2] Space :=
    (Submodule.prodEquivOfIsCompl A B hAB).symm.trans (a.prodCongr b)
  have hcA (v : V) : (c v).1 = 0 ↔ v ∈ B := by
    change a (((Submodule.prodEquivOfIsCompl A B hAB).symm v).1) = 0 ↔ _
    rw [a.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero]
  have hcB (v : V) : (c v).2 = 0 ↔ v ∈ A := by
    change b (((Submodule.prodEquivOfIsCompl A B hAB).symm v).2) = 0 ↔ _
    rw [b.map_eq_zero_iff, Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero]
  have hform (v : V) : form (c v) = 1 ↔ v ≠ 0 ∧ (v ∈ A ∨ v ∈ B) := by
    rw [form_eq_one_iff_axes, hcA, hcB, c.map_ne_zero_iff, or_comm]
  have hpres (g : G) (v : V) : form (c (ρ g v)) = form (c v) := by
    apply (by decide +kernel : ∀ x y : ZMod 2, (x = 1 ↔ y = 1) → x = y)
    rw [hform, hform, hunion]
    exact and_congr_left (fun _ => not_congr
      ⟨fun h => GoldschmidtONan.action_injective g (h.trans (map_zero (ρ g)).symm),
        fun h => h ▸ map_zero (ρ g)⟩)
  let φ : G →* (Space ≃ₗ[ZMod 2] Space) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Space).toMonoidHom.comp
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom.comp ρ.asGroupHom)
  have hφ (g : G) (w : Space) : φ g w = c (ρ g (c.symm w)) := rfl
  let f : G →* TerminalLines.IsometryGroup := φ.codRestrict _ (by
    intro g
    apply (mem_quadraticIsometrySubgroup form _).mpr
    intro w
    rw [hφ, hpres, c.apply_symm_apply])
  have hfi : Function.Injective f := by
    intro g h he
    apply hf
    apply LinearMap.ext
    intro v
    have hh := congrArg (fun z : TerminalLines.IsometryGroup => z.val (c v)) he
    change φ g (c v) = φ h (c v) at hh
    rw [hφ, hφ, c.symm_apply_apply] at hh
    exact c.injective hh
  refine ⟨c, f, hfi, fun g v => ?_⟩
  change c (ρ g v) = φ g (c v)
  rw [hφ, c.symm_apply_apply]


open Representation.BinaryOffender
open TerminalLines

private def modelAction : Representation (ZMod 2) IsometryGroup Space where
  toFun g := g.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

private def firstReflection : IsometryGroup :=
  ⟨(LinearEquiv.prodComm F F F).prodCongr (LinearEquiv.refl F Plane), by
    apply (mem_quadraticIsometrySubgroup form _).mpr
    intro v
    change planeForm ((LinearEquiv.prodComm F F F) v.1) + planeForm v.2 =
      planeForm v.1 + planeForm v.2
    rw [planeForm_preserved]⟩

private theorem firstReflection_square : firstReflection ^ 2 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  rintro ⟨⟨a,b⟩,c⟩
  rfl

private theorem firstReflection_ne_one : firstReflection ≠ 1 := by
  intro he
  have hh := congrArg (fun a : IsometryGroup => a.val ((1,0),(0,0))) he
  have hh' := congrArg (fun v : Space => v.1.1) hh
  exact zero_ne_one hh'

private theorem modelAction_cubicRatio_le_one : cubicRatio modelAction ≤ 1 := by
  have hc : Nat.card (fixedSpace modelAction (zpowers firstReflection)) = 8 := by
    let e : fixedSpace modelAction (zpowers firstReflection) ≃
        {v : Space // firstReflection.val v = v} :=
      (_root_.Equiv.refl Space).subtypeEquiv (fun v => mem_fixedSpace_zpowers_iff _ _ _)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card]
    decide +kernel
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace modelAction (zpowers firstReflection))
  rw [Nat.card_zmod, hc] at hpow
  have hdim : Module.finrank (ZMod 2) (fixedSpace modelAction (zpowers firstReflection)) = 3 := by
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hpow.symm
  have hcodim := fixedCodim_add_finrank modelAction (zpowers firstReflection)
  have hSpace : Module.finrank (ZMod 2) Space = 4 := by simp [Space, Plane, F]
  have hr : Module.finrank (ZMod 2) (LinearMap.range (modelAction firstReflection - LinearMap.id)) ≤ 1 := by
    rw [←fixedCodim_zpowers_eq_displacement_rank]
    omega
  apply (isFFModule_iff_cubicRatio_le_one modelAction).mp
  exact ⟨zpowers firstReflection,(bestOffender_of_involution_displacement_le_one modelAction
    firstReflection firstReflection_square firstReflection_ne_one hr).isOffender modelAction⟩

variable [Finite G]

/-- No proper overgroup of an order-36 subgroup has cubic ratio above one. -/
theorem eq_top_of_card_thirty_six (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ)
    (A B : Submodule (ZMod 2) V) (hAB : IsCompl A B)
    (hA : Module.finrank (ZMod 2) A = 2) (hB : Module.finrank (ZMod 2) B = 2)
    (hunion : ∀ g v, (ρ g v ∈ A ∨ ρ g v ∈ B) ↔ (v ∈ A ∨ v ∈ B))
    (L : Subgroup G) (hL : Nat.card L = 36) (hlow : 1 < cubicRatio ρ) : L = ⊤ := by
  obtain ⟨c,f,hfi,hc⟩ := exists_isometry_embedding ρ hf A B hAB hA hB hunion
  have hbound : Nat.card G ≤ 72 :=
    (Nat.card_le_card_of_injective f hfi).trans_eq isometryGroup_card
  have hd : 36 ∣ Nat.card G := hL ▸ L.card_subgroup_dvd_card
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 36 ∨ Nat.card G = 72 := by
    obtain ⟨k,hk⟩ := hd
    omega
  rcases hcases with he | he
  · exact L.eq_top_of_card_eq (hL.trans he.symm)
  have hbij : Function.Bijective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hfi,he.trans isometryGroup_card.symm⟩
  let e : G ≃* IsometryGroup := MulEquiv.ofBijective f hbij
  have heq : ∀ g v, c.symm (modelAction g v) = ρ (e.symm g) (c.symm v) := by
    intro g v
    apply c.injective
    rw [c.apply_symm_apply,hc,c.apply_symm_apply]
    change g.val v = (e (e.symm g)).val v
    rw [e.apply_symm_apply]
  have hh := cubicRatio_le_nat_of_equivariant modelAction ρ e.symm.toMonoidHom
    e.symm.injective c.symm heq 1 (by simpa using modelAction_cubicRatio_le_one)
  exact (not_le_of_gt hlow (by simpa using hh)).elim

end Representation.BinaryTwoPlaneRecognition
