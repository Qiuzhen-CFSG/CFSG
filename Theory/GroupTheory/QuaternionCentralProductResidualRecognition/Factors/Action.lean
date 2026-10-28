module

public import Theory.SpecificGroups.SL2.BinaryTetrahedral

/-!
# Conjugacy of cubic quaternion actions

Every nonidentity automorphism of Q8 with cube one is conjugate to the
standard binary tetrahedral action. Automorphisms are encoded by the images
of the two quaternion generators; finite tables check the conjugacy identity.
The encoding follows `Theory.GroupTheory.SpecificGroups.QuaternionEightAut`.
This supplies the factor recognition used in Aschbacher–Smith 14.2.21,
printed p.988 (PDF p.1005).
-/

namespace Subgroup.QuaternionCubicAction
open QuaternionGroup GLS3.Chapter5.SchurPresentation
private abbrev Q := QuaternionGroup 2
private def goodPair (p : Q × Q) : Prop :=
  p.1 ^ 2 = a 2 ∧ p.2 ^ 2 = a 2 ∧ p.1 * p.2 ≠ p.2 * p.1
private instance : DecidablePred goodPair := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private abbrev Pairs := {p : Q × Q // goodPair p}
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
set_option maxRecDepth 10000 in
private theorem pair_map_spec : ∀ p : Pairs,
    Function.Bijective (pairMap p.val) ∧
    (∀ x y : Q, pairMap p.val (x*y)=pairMap p.val x * pairMap p.val y) ∧
    pairMap p.val (a 1)=p.val.1 ∧ pairMap p.val (xa 0)=p.val.2 := by
  decide
private noncomputable def pairAut (p : Pairs) : MulAut Q :=
  MulEquiv.ofBijective
    ({ toFun := pairMap p.val
       map_one' := by change p.val.1^0=1; exact pow_zero _
       map_mul' := (pair_map_spec p).2.1 } : Q →* Q)
    (pair_map_spec p).1

private theorem square_of_square_ne_one : ∀ x : Q, x^2 ≠ 1 → x^2=a 2 := by decide
private def autPair (e : MulAut Q) : Pairs := by
  refine ⟨(e (a 1),e (xa 0)),?_,?_,?_⟩
  · apply square_of_square_ne_one
    intro h
    have hi : (a 1 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · apply square_of_square_ne_one
    intro h
    have hi : (xa 0 : Q)^2 ≠ 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_pow,map_one] using h
  · intro h
    have hi : (a 1 : Q)*xa 0 ≠ xa 0*a 1 := by decide
    apply hi
    apply e.injective
    simpa only [map_mul] using h
private noncomputable def autEquivPairs : MulAut Q ≃ Pairs where
  toFun := autPair
  invFun := pairAut
  left_inv e := by
    apply MulEquiv.ext
    intro x
    cases x with
    | a i =>
      change (e (a 1))^i.val=e (a i)
      rw [←map_pow,a_one_pow,ZMod.natCast_zmod_val]
    | xa i =>
      change e (xa 0)*(e (a 1))^i.val=e (xa i)
      rw [←map_pow,←map_mul,a_one_pow,ZMod.natCast_zmod_val,xa_mul_a,zero_add]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (pair_map_spec p).2.2.1
    · exact (pair_map_spec p).2.2.2

private theorem pair_conjugacy : ∀ p : Pairs,
    (∀ x : Q, pairMap p.val (pairMap p.val (pairMap p.val x)) = x) →
    (∃ x : Q, pairMap p.val x ≠ x) →
    ∃ w : Pairs, ∀ x : Q,
      pairMap w.val (pairMap p.val x) = q8Cycle (pairMap w.val x) := by
  decide

/-- A nontrivial cubic quaternion action admits the standard coordinates. -/
public theorem exists_coordinates (a : MulAut (QuaternionGroup 2))
    (ha : a ^ 3 = 1) (hne : a ≠ 1) :
    ∃ e : MulAut (QuaternionGroup 2), MulAut.congr e a = q8Cycle := by
  have hp (x : Q) : pairMap (autPair a).val x = a x :=
    DFunLike.congr_fun (autEquivPairs.left_inv a) x
  have hc (x : Q) : pairMap (autPair a).val
      (pairMap (autPair a).val (pairMap (autPair a).val x)) = x := by
    simpa only [hp] using (show a (a (a x)) = x from DFunLike.congr_fun ha x)
  have hn : ∃ x : Q, pairMap (autPair a).val x ≠ x := by
    by_contra! h
    apply hne
    ext x
    exact (hp x).symm.trans (h x)
  obtain ⟨w, hw⟩ := pair_conjugacy (autPair a) hc hn
  refine ⟨pairAut w, ?_⟩
  ext x
  change pairAut w (a ((pairAut w).symm x)) = q8Cycle x
  have h := hw ((pairAut w).symm x)
  simp only [hp] at h
  change pairAut w (a ((pairAut w).symm x)) =
    q8Cycle (pairAut w ((pairAut w).symm x)) at h
  simpa only [MulEquiv.apply_symm_apply] using h

end Subgroup.QuaternionCubicAction
