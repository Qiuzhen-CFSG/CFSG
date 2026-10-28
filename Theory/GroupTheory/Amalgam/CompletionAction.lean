module
public import Theory.GroupTheory.Amalgam.AutomorphismGroup
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Universal

/-!
# Descent of compatible amalgam actions to a marked completion

An action on an amalgam induces homomorphisms out of its universal completion.
If these homomorphisms kill the kernel of a faithful marked completion, they
descend to automorphisms of that completion. Generation proves the action law;
endpoint injectivity proves faithfulness. An actor conjugating both endpoints
by the same middle element descends to that literal inner automorphism.

This is the group-theoretic descent used in Delgado--Goldschmidt--Stellmacher,
*Groups and Graphs* (1985), (15.2), printed p.227. Kernel preservation is an
explicit geometric premise, not a consequence of abstract local recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace Theory.GroupTheory.RankTwoAmalgam.CompletionAction
variable {X : Type*} [Group X]

private theorem completion_hom_ext {A D C Y : Type*}
    [Group A] [Group D] [Group C] [Group Y]
    {α : RankTwoAmalgam A D C} (c : FaithfulCompletion α (G := X))
    {f g : X →* Y} (hl : ∀ x, f (c.left x) = g (c.left x))
    (hr : ∀ x, f (c.right x) = g (c.right x)) : f = g := by
  have ht : (⊤ : Subgroup X) ≤ f.eqLocus g := by
    rw [← c.generated]
    exact sup_le (by rintro _ ⟨x,rfl⟩; exact hl x)
      (by rintro _ ⟨x,rfl⟩; exact hr x)
  ext x
  exact ht (mem_top x)

universe u
variable {L B R : Type u} {K : Type*} [Group L] [Group B] [Group R] [Group K]
  {α : RankTwoAmalgam L B R}
  (a : K →* Iso α α) (c : FaithfulCompletion α (G := X))

/-- The action preserves the relations of the specified marked completion. -/
@[expose] def PreservesCompletionKernel : Prop :=
  ∀ b : K,
    (Universal.lift α c).ker ≤
      (Universal.lift α
        (c.comapIso (a b))).ker

variable (hk : PreservesCompletionKernel a c)

@[expose] def descendedEnd (b : K) : X →* X :=
  (QuotientGroup.lift _
    (Universal.lift α (c.comapIso (a b)))
    (hk b)).comp
    (QuotientGroup.quotientKerEquivOfSurjective _
      (Universal.lift_surjective α c)).symm.toMonoidHom

theorem descendedEnd_lift (b : K) (x : α.Universal) :
    descendedEnd a c hk b (Universal.lift α c x) =
      Universal.lift α (c.comapIso (a b)) x := by
  change (QuotientGroup.lift (Universal.lift α c).ker
    (Universal.lift α (c.comapIso (a b))) (hk b))
    ((QuotientGroup.quotientKerEquivOfSurjective _
      (Universal.lift_surjective α c)).symm
      (Universal.lift α c x)) = _
  rw [show (Universal.lift α c x) =
    (QuotientGroup.quotientKerEquivOfSurjective _
      (Universal.lift_surjective α c)) (QuotientGroup.mk x) from rfl,
    MulEquiv.symm_apply_apply]
  rfl

@[simp] theorem descendedEnd_left (b : K)
    (x : L) :
    descendedEnd a c hk b (c.left x) = c.left ((a b).left x) := by
  simpa only [Universal.lift_left, FaithfulCompletion.comapIso, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using descendedEnd_lift a c hk b (Universal.left _ x)

@[simp] theorem descendedEnd_right (b : K)
    (x : R) :
    descendedEnd a c hk b (c.right x) = c.right ((a b).right x) := by
  simpa only [Universal.lift_right, FaithfulCompletion.comapIso, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom] using descendedEnd_lift a c hk b (Universal.right _ x)

theorem descendedEnd_one : descendedEnd a c hk 1 = MonoidHom.id X := by
  apply completion_hom_ext c <;> intro x
  · rw [descendedEnd_left, map_one]; rfl
  · rw [descendedEnd_right, map_one]; rfl

theorem descendedEnd_mul (b d : K) :
    descendedEnd a c hk (b*d) = (descendedEnd a c hk b).comp (descendedEnd a c hk d) := by
  apply completion_hom_ext c <;> intro x
  · simp only [descendedEnd_left, MonoidHom.comp_apply, map_mul, Iso.mul_left,
      MulAut.mul_apply]
  · simp only [descendedEnd_right, MonoidHom.comp_apply, map_mul, Iso.mul_right,
      MulAut.mul_apply]

/-- The action on the marked completion, constructed by descent of its
literal universal map. -/
@[expose] def completionAction : K →* MulAut X where
  toFun b := {
    toFun := descendedEnd a c hk b
    invFun := descendedEnd a c hk b⁻¹
    left_inv x := by
      have he := DFunLike.congr_fun (descendedEnd_mul a c hk b⁻¹ b) x
      rw [inv_mul_cancel, descendedEnd_one] at he
      exact he.symm
    right_inv x := by
      have he := DFunLike.congr_fun (descendedEnd_mul a c hk b b⁻¹) x
      rw [mul_inv_cancel, descendedEnd_one] at he
      exact he.symm
    map_mul' := map_mul (descendedEnd a c hk b) }
  map_one' := by ext x; exact DFunLike.congr_fun (descendedEnd_one a c hk) x
  map_mul' b d := by ext x; exact DFunLike.congr_fun (descendedEnd_mul a c hk b d) x

@[simp] theorem completionAction_left (b : K)
    (x : L) :
    completionAction a c hk b (c.left x) = c.left ((a b).left x) :=
  by
    change descendedEnd a c hk b (c.left x) = _
    exact descendedEnd_left a c hk b x

@[simp] theorem completionAction_right (b : K)
    (x : R) :
    completionAction a c hk b (c.right x) = c.right ((a b).right x) :=
  by
    change descendedEnd a c hk b (c.right x) = _
    exact descendedEnd_right a c hk b x

theorem completionAction_injective (ha : Function.Injective a) :
    Function.Injective (completionAction a c hk) := by
  intro b d he
  apply ha
  apply Iso.ext
  · apply MulEquiv.ext
    intro x
    apply c.left_injective
    simpa only [completionAction_left] using
      congrArg (fun f : MulAut X => f (c.left x)) he
  · apply MulEquiv.ext
    intro x
    apply c.middle_injective
    change c.left (α.left ((a b).middle x)) = c.left (α.left ((a d).middle x))
    rw [← (a b).left_commutes, ← (a d).left_commutes]
    simpa only [completionAction_left] using
      congrArg (fun f : MulAut X => f (c.left (α.left x))) he
  · apply MulEquiv.ext
    intro x
    apply c.right_injective
    simpa only [completionAction_right] using
      congrArg (fun f : MulAut X => f (c.right x)) he

/-- An actor inducing conjugation by the same middle element on both
endpoints descends to that inner automorphism of the completion. -/
theorem completionAction_eq_conj (b : K) (d : B)
    (hl : ∀ x : L, (a b).left x = α.left d * x * (α.left d)⁻¹)
    (hr : ∀ x : R, (a b).right x = α.right d * x * (α.right d)⁻¹) :
    completionAction a c hk b = MulAut.conj (c.middle d) := by
  apply MulEquiv.toMonoidHom_injective
  apply completion_hom_ext c
  · intro x
    change completionAction a c hk b (c.left x) = c.middle d * c.left x * (c.middle d)⁻¹
    rw [completionAction_left, hl, map_mul, map_mul, map_inv]
    rfl
  · intro x
    change completionAction a c hk b (c.right x) = c.middle d * c.right x * (c.middle d)⁻¹
    rw [completionAction_right, hr, map_mul, map_mul, map_inv]
    rw [show c.middle d = c.right (α.right d) from DFunLike.congr_fun c.compatible d]

end Theory.GroupTheory.RankTwoAmalgam.CompletionAction
