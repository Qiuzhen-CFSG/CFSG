module

public import Theory.GroupAction.BinaryFiveMarkedParabolic
public import Theory.GroupAction.BinaryFixedLineQuotient

/-!
# Full parabolic recognition at a marked four in an elementary group of order 32

The literal automorphisms stabilizing the marked four form the binary 2+3
parabolic. A subgroup containing its full radical and a nontrivial perfect
subgroup equals this stabilizer if it induces every automorphism of the four.
The hypotheses retain the original subgroup and its pointwise action.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace MulAut
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

/-- Full radical, a nontrivial perfect subgroup, and full action on the marked
four recognize its entire stabilizer among automorphisms of the original group. -/
theorem elementary_five_marked_parabolic
    (hE : Nat.card E = 32) (H : Subgroup E) (hH : Nat.card H = 4)
    (M J : Subgroup (MulAut E)) [Group.IsPerfect J]
    (hJ : J ≠ ⊥) (hJM : J ≤ M)
    (hM : ∀ a ∈ M, ∀ x : E, a x ∈ H ↔ x ∈ H)
    (hR : ∀ a : MulAut E,
      (∀ x ∈ H, a x = x) → (∀ x : E, a x * x⁻¹ ∈ H) → a ∈ M)
    (hres : ∀ f : MulAut H, ∃ a ∈ M, ∀ x : H, a x = (f x : E)) :
    ∀ a : MulAut E, a ∈ M ↔ ∀ x : E, a x ∈ H ↔ x ∈ H := by
  let W : Submodule (ZMod 2) (Additive E) :=
    AddSubgroup.toZModSubmodule 2 H.toAddSubgroup
  let e : MulAut E ≃* BinaryLinear.GL (Additive E) := BinaryFixedLine.linearAutEquiv
  let w : Additive H ≃+ W :=
    { toFun x := ⟨Additive.ofMul x.toMul.val, x.toMul.property⟩
      invFun x := Additive.ofMul ⟨x.val.toMul, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hWcard : Nat.card W = 4 := (Nat.card_congr w.toEquiv).symm.trans hH
  have hEdim : Module.finrank (ZMod 2) (Additive E) = 5 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hh
    simpa only [Nat.card_zmod,hE] using hh.symm
  have hWdim : Module.finrank (ZMod 2) W = 2 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    simpa only [Nat.card_zmod,hWcard] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)).symm
  let ι : M →* BinaryLinear.parabolic W :=
    (e.toMonoidHom.comp M.subtype).codRestrict _ (fun a => hM a.val a.property)
  have hι : Function.Injective ι := by
    intro a b hab
    apply Subtype.ext
    apply e.injective
    exact congrArg Subtype.val hab
  let j : J →* BinaryLinear.parabolic W := ι.comp (inclusion hJM)
  have hj : Function.Injective j := hι.comp (inclusion_injective hJM)
  let M' := ι.range
  let J' := j.range
  let : Group.IsPerfect J' := Group.IsPerfect.range j
  have hJ' : J' ≠ ⊥ := by
    intro he
    apply hJ
    apply (eq_bot_iff_forall J).mpr
    intro a ha
    have hz : j ⟨a,ha⟩ ∈ J' := ⟨⟨a,ha⟩,rfl⟩
    rw [he] at hz
    exact congrArg Subtype.val (hj ((show j ⟨a,ha⟩ = 1 from hz).trans (map_one j).symm))
  have hJM' : J' ≤ M' := by
    rintro _ ⟨a,rfl⟩
    exact ⟨inclusion hJM a,rfl⟩
  have hR' : (BinaryLinear.radical W).subgroupOf (BinaryLinear.parabolic W) ≤ M' := by
    intro g hg
    let a := e.symm g.val
    have ha : a ∈ M := by
      apply hR
      · intro x hx
        have hh := hg.1 (Additive.ofMul x) hx
        change g.val (Additive.ofMul x) = Additive.ofMul x at hh
        have hea : e a = g.val := e.apply_symm_apply g.val
        rw [← hea] at hh
        exact congrArg Additive.toMul hh
      · intro x
        have hh := hg.2 (Additive.ofMul x)
        change g.val (Additive.ofMul x) - Additive.ofMul x ∈ W at hh
        have hea : e a = g.val := e.apply_symm_apply g.val
        rw [← hea] at hh
        change a x / x ∈ H at hh
        simpa only [div_eq_mul_inv] using hh
    refine ⟨⟨a,ha⟩,?_⟩
    exact Subtype.ext (e.apply_symm_apply g.val)
  have hres' : Function.Surjective
      ((BinaryLinear.SmallParabolicLevi.subspaceAction W).comp M'.subtype) := by
    intro f
    let fH : MulAut H := MulEquiv.toAdditive.symm ((w.trans f.toAddEquiv).trans w.symm)
    obtain ⟨a,ha,haf⟩ := hres fH
    refine ⟨⟨ι ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩⟩,?_⟩
    ext x
    have hx := haf (w.symm x).toMul
    exact congrArg Additive.ofMul hx
  have htop : M' = ⊤ :=
    BinaryLinear.parabolic_eq_top_of_perfect_subgroup_of_subspaceAction_surjective
      W hEdim hWdim M' J' hJ' hJM' hR' hres'
  intro a
  constructor
  · exact hM a
  · intro ha
    have hp : e a ∈ BinaryLinear.parabolic W := ha
    have hm : (⟨e a,hp⟩ : BinaryLinear.parabolic W) ∈ M' := htop ▸ mem_top _
    obtain ⟨m,hm⟩ := hm
    have he : e m.val = e a := congrArg Subtype.val hm
    exact e.injective he ▸ m.property

end MulAut
