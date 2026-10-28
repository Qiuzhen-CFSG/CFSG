module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.Certificates
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.Words
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.BlockData

/-!
# The actual involution and centralizing words in Suz

Disjoint-cycle certificates identify the numerical maps with the fixed ATLAS
generators. The checked word equalities then prove that the candidate is an
involution and both displayed words centralize it. Their actions on the 27
pairs are the two literal generators of `BlockGroup`.
No class label, group order, presentation, or ambient simplicity is used.
Source: ATLAS SuzG1-p1782B0; GLS3 Table 5.3o; Aschbacher--Smith A.2.19.
-/

public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection
-- Comparing the original carrier exposes its 870-cycle generator definition.
set_option maxRecDepth 2048
set_option Elab.async false
open Tables Checks
open Sporadic.Fischer.Fi22.KernelCertificate

private theorem numerical_facts (x : Fin 1782) :
    wMap x = aMap (bMap (aMap (bMap (aMap (bMap (bMap x)))))) ∧
    zMap x = (wMap^[6]) x ∧
    uMap x = bMap (aMap (bMap (aMap x))) ∧
    vMap x = aMap (bMap (aMap (bMap (bMap
      (aMap (bMap (aMap (bMap (bMap (aMap (bMap x))))))))))) ∧
    uMap (uiMap x) = x ∧ vMap (viMap x) = x ∧
    cMap x = uMap (zMap (uiMap (zMap (uMap x)))) ∧
    dMap x = vMap (zMap (viMap (zMap (vMap
      (zMap (viMap (zMap (vMap x)))))))) ∧
    zMap (zMap x) = x ∧
    cMap (zMap x) = zMap (cMap x) ∧
    dMap (zMap x) = zMap (dMap x) := by
  have h := all_points x
  have hx : Fin.ofNat 1782 x.val = x := by simp
  simp only [pointCheck, if_pos x.isLt, hx, Bool.and_eq_true] at h
  simpa only [wordCheck, Bool.and_eq_true, beq_iff_eq, and_assoc] using h.2

private theorem generator_fixed (x : Fin 1782) :
    (supportA.testBit x.val = false → aMap x = x) ∧
    (supportB.testBit x.val = false → bMap x = x) := by
  have h := all_points x
  have hx : Fin.ofNat 1782 x.val = x := by simp
  simp only [pointCheck, if_pos x.isLt, hx, Bool.and_eq_true,
    Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨fun ha => h.1.1.resolve_left (by simp [ha]),
    fun hb => h.1.2.resolve_left (by simp [hb])⟩

theorem generatorA_apply (x : Fin 1782) : generatorA x = aMap x := by
  apply CycleCheck.inverse_prod_eq cyclesA aMap nodupA
  · simpa only [List.all_eq_true, decide_eq_true_eq] using cycleA
  · intro y hy
    rw [supportA_eq] at hy
    exact (generator_fixed y).1 hy

theorem generatorB_apply (x : Fin 1782) : generatorB x = bMap x := by
  apply CycleCheck.inverse_prod_eq cyclesB bMap nodupB
  · simpa only [List.all_eq_true, decide_eq_true_eq] using cycleB
  · intro y hy
    rw [supportB_eq] at hy
    exact (generator_fixed y).2 hy

private theorem eval_mul {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    {g h : G} {A B : X → X}
    (ha : ∀ x, f g x = A x) (hb : ∀ x, f h x = B x) :
    ∀ x, f (g * h) x = A (B x) := by
  intro x
  rw [map_mul, Equiv.Perm.mul_apply, ha, hb]

private theorem a_apply (x : Fin 1782) : inclusion a x = aMap x :=
  (congrArg (fun p : Equiv.Perm (Fin 1782) => p x) inclusion_a).trans (generatorA_apply x)
private theorem b_apply (x : Fin 1782) : inclusion b x = bMap x :=
  (congrArg (fun p : Equiv.Perm (Fin 1782) => p x) inclusion_b).trans (generatorB_apply x)

private theorem eval_sq {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    {g : G} {A : X → X} (ha : ∀ x, f g x = A x) :
    ∀ x, f (g ^ 2) x = A (A x) := by
  simpa only [pow_two] using eval_mul f ha ha

private theorem eval_pow {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    {g : G} {A : X → X} (ha : ∀ x, f g x = A x) (n : Nat) :
    ∀ x, f (g ^ n) x = (A^[n]) x := by
  have hfun : (f g : X → X) = A := funext ha
  simp only [map_pow, Equiv.Perm.coe_pow, hfun, implies_true]

private theorem eval_inv {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    {g : G} {A B : X → X} (ha : ∀ x, f g x = A x)
    (hb : ∀ x, A (B x) = x) : ∀ x, f g⁻¹ x = B x := by
  intro x
  apply (f g).injective
  rw [map_inv]
  change f g ((f g).symm x) = f g (B x)
  rw [Equiv.apply_symm_apply, ha, hb]

theorem word_apply (x : Fin 1782) : inclusion word x = wMap x := by
  unfold word
  exact (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion
    (eval_mul inclusion (eval_mul inclusion a_apply b_apply) a_apply) b_apply)
      a_apply) (eval_sq inclusion b_apply) x).trans (numerical_facts x).1.symm

theorem involution_apply (x : Fin 1782) : inclusion involution x = zMap x := by
  unfold involution
  exact (eval_pow inclusion word_apply 6 x).trans (numerical_facts x).2.1.symm

theorem u_apply (x : Fin 1782) : inclusion u x = uMap x := by
  unfold u
  exact ((eval_mul inclusion (eval_mul inclusion (eval_mul inclusion b_apply a_apply) b_apply) a_apply) x).trans (numerical_facts x).2.2.1.symm

theorem v_apply (x : Fin 1782) : inclusion v x = vMap x := by
  unfold v
  exact ((eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion a_apply b_apply) a_apply) (eval_sq inclusion b_apply)) a_apply) b_apply) a_apply) (eval_sq inclusion b_apply)) a_apply) b_apply) x).trans (numerical_facts x).2.2.2.1.symm

private theorem u_inv_apply (x : Fin 1782) : inclusion u⁻¹ x = uiMap x :=
  eval_inv inclusion u_apply (fun y => (numerical_facts y).2.2.2.2.1) x

private theorem v_inv_apply (x : Fin 1782) : inclusion v⁻¹ x = viMap x :=
  eval_inv inclusion v_apply (fun y => (numerical_facts y).2.2.2.2.2.1) x

theorem c_apply (x : Fin 1782) : inclusion c x = cMap x := by
  unfold c
  exact (eval_mul inclusion u_apply (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion involution_apply u_inv_apply) involution_apply) u_apply) x).trans
    (numerical_facts x).2.2.2.2.2.2.1.symm

theorem d_apply (x : Fin 1782) : inclusion d x = dMap x := by
  unfold d
  exact (eval_mul inclusion v_apply (eval_sq inclusion
    (eval_mul inclusion (eval_mul inclusion (eval_mul inclusion involution_apply v_inv_apply) involution_apply) v_apply)) x).trans
    (numerical_facts x).2.2.2.2.2.2.2.1.symm

private theorem sq_one_of_eval {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) {g : G} {A : X → X}
    (ha : ∀ x, f g x = A x) (haa : ∀ x, A (A x) = x) : g ^ 2 = 1 := by
  apply hf
  apply Equiv.ext
  intro x
  rw [eval_sq f ha, haa, map_one, Equiv.Perm.one_apply]

private theorem commute_of_eval {G X : Type*} [Group G] (f : G →* Equiv.Perm X)
    (hf : Function.Injective f) {g h : G} {A B : X → X}
    (ha : ∀ x, f g x = A x) (hb : ∀ x, f h x = B x)
    (hc : ∀ x, A (B x) = B (A x)) : g * h = h * g := by
  apply hf
  apply Equiv.ext
  intro x
  exact (eval_mul f ha hb x).trans ((hc x).trans (eval_mul f hb ha x).symm)

theorem involution_sq : involution ^ 2 = 1 :=
  sq_one_of_eval inclusion inclusion_injective involution_apply
    (fun x => (numerical_facts x).2.2.2.2.2.2.2.2.1)

theorem involution_ne_one : involution ≠ 1 := by
  intro h
  have he := congrArg (fun g : Carrier => inclusion g 0) h
  rw [involution_apply, map_one, Equiv.Perm.one_apply] at he
  have hmove : zMap 0 ≠ (0 : Fin 1782) := by decide +kernel
  exact hmove he

theorem involution_order : orderOf involution = 2 :=
  orderOf_eq_prime involution_sq involution_ne_one

theorem c_commutes : c * involution = involution * c :=
  commute_of_eval inclusion inclusion_injective c_apply involution_apply
    (fun x => (numerical_facts x).2.2.2.2.2.2.2.2.2.1)

theorem d_commutes : d * involution = involution * d :=
  commute_of_eval inclusion inclusion_injective d_apply involution_apply
    (fun x => (numerical_facts x).2.2.2.2.2.2.2.2.2.2)

theorem c_point (i : Fin 27) : (point i).image (inclusion c) = point (blockC i) := by
  have he : (inclusion c : Fin 1782 → Fin 1782) = cMap := funext c_apply
  rw [he]
  exact cMap_point i

theorem d_point (i : Fin 27) : (point i).image (inclusion d) = point (blockD i) := by
  have he : (inclusion d : Fin 1782 → Fin 1782) = dMap := funext d_apply
  rw [he]
  exact dMap_point i

end Sporadic.LeechRelated.Suz.CentralizerSection
