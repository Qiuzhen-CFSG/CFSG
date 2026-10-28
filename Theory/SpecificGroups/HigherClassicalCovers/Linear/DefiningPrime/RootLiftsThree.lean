module

public import Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.LocalSection
public import Theory.GroupTheory.CentralExtensionSwap
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Compatible degree-four root lifts over the three-element field

For each root, choose a determinant-one sign diagonal that inverts it.
The commutator of lifts of that diagonal and a root element has the same
root image, since `-2a = a`. Commutativity of the diagonal matrices makes
these choices equivariant under the whole sign torus. Cyclic root groups
have abelian preimages, giving additivity of the chosen lifts.

A sign diagonal separates distant roots sharing an endpoint. Complementary
disjoint roots instead admit an even double transposition that exchanges
them with coefficient unchanged. The central-extension swapping lemma,
followed by the coefficient alternatives `0`, `1`, `-1`, proves their
commutation. Finally a sign diagonal inverts the chain commutator and its
prescribed lift; their central difference has order dividing both two and
three, so the exact chain relation holds.

The final application supplies the defining-prime exclusion for arbitrary
finite perfect central covers of PSL₄ over this field. This is the ternary
input to Aschbacher–Smith I.1.1 and I.1.4(1), printed pp.407–408 of
`refs/quasithin.pdf`, citing GLS III §6.1. The construction adapts the root
lifting argument of Steinberg §§6–7 (`refs/KGroup/GLS3/Chapter2St1.tex`,
Theorem 10, steps (2)–(8)); that theorem's field-size hypothesis does not
cover order three, so the sign and swapping arguments are proved here.
-/

public section

open scoped MatrixGroups commutatorElement
open Theory.SpecificGroups.LinearHigher
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsThree
variable {F : Type*} [Field F]

private def sign (i j k : Fin 4) : F := if k = i ∨ k = j then -1 else 1

private def torus (i j : Fin 4) (hij : i ≠ j) : SL(4, F) :=
  ⟨Matrix.diagonal (sign i j), by
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.det_diagonal, Fin.prod_univ_succ, sign]⟩

private theorem sign_sq (i j k : Fin 4) : sign (F := F) i j k * sign i j k = 1 := by
  unfold sign
  split <;> simp

private theorem torus_conj (i j : Fin 4) (hij : i ≠ j) (r : Root 4) (a : F) :
    torus i j hij * matrixRoot r a * (torus i j hij)⁻¹ =
      matrixRoot r (sign i j r.val.1 * sign i j r.val.2 * a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change Matrix.diagonal (sign i j) * (1 + Matrix.single r.val.1 r.val.2 a) =
    (1 + Matrix.single r.val.1 r.val.2 (sign i j r.val.1 * sign i j r.val.2 * a)) *
      Matrix.diagonal (sign i j)
  ext k l
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.add_apply,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hk : k = r.val.1
  · subst k
    by_cases hl : l = r.val.2
    · subst l
      simp [r.property, mul_left_comm, mul_comm, sign_sq]
    · by_cases he : r.val.1 = l <;> simp [hl, he, eq_comm]
  · by_cases he : k = l
    · subst l
      simp [Ne.symm hk]
    · simp [Ne.symm hk, he]

private theorem torus_commute (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) :
    Commute (torus (F := F) i j hij) (torus k l hkl) := by
  apply Subtype.ext
  change Matrix.diagonal (sign i j) * Matrix.diagonal (sign k l) =
    Matrix.diagonal (sign k l) * Matrix.diagonal (sign i j)
  simp [Matrix.diagonal_mul_diagonal, mul_comm]

private theorem fourth (i j k : Fin 4) : ∃ l : Fin 4, l ≠ i ∧ l ≠ j ∧ l ≠ k := by
  revert i j k
  decide

private def permutation (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1) : SL(4, F) :=
  ⟨σ.permMatrix F, by simp [hσ]⟩

private theorem permutation_conj (σ : Equiv.Perm (Fin 4)) (hσ : Equiv.Perm.sign σ = 1)
    (r : Root 4) (a : F) :
    permutation σ hσ * matrixRoot r a * (permutation σ hσ)⁻¹ =
      matrixRoot (root (σ.symm r.val.1) (σ.symm r.val.2)
        (fun h => r.property (σ.symm.injective h))) a := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change σ.toPEquiv.toMatrix * (1 + Matrix.single r.val.1 r.val.2 a) =
    (1 + Matrix.single (σ.symm r.val.1) (σ.symm r.val.2) a) * σ.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  ext k l
  simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.single_apply,
    Equiv.eq_symm_apply, eq_comm]

/-- The actual even permutation exchanges complementary root groups. -/
private theorem swap_roots (r s : Root 4) (h₁ : r.val.1 ≠ s.val.1) (h₂ : r.val.2 ≠ s.val.2)
    (h₃ : r.val.1 ≠ s.val.2) (h₄ : r.val.2 ≠ s.val.1) :
    ∃ t : PSL(4, F), (∀ a, t * projectiveRoot r a * t⁻¹ = projectiveRoot s a) ∧
      ∀ a, t * projectiveRoot s a * t⁻¹ = projectiveRoot r a := by
  let σ := Equiv.swap r.val.1 s.val.1 * Equiv.swap r.val.2 s.val.2
  have hσ : Equiv.Perm.sign σ = 1 := by
    simp [σ, Equiv.Perm.sign_swap h₁, Equiv.Perm.sign_swap h₂]
  have hri : σ.symm r.val.1 = s.val.1 := by
    simp [σ, Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne,
      h₄.symm, s.property]
  have hrj : σ.symm r.val.2 = s.val.2 := by
    simp [σ, Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne,
      h₄, r.property.symm]
  have hsi : σ.symm s.val.1 = r.val.1 := by
    simp [σ, Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne,
      h₃, r.property]
  have hsj : σ.symm s.val.2 = r.val.2 := by
    simp [σ, Equiv.Perm.mul_def, Equiv.swap_apply_of_ne_of_ne,
      s.property.symm, h₃.symm]
  refine ⟨QuotientGroup.mk (permutation (F := F) σ hσ), ?_, ?_⟩
  · intro a
    have h := congrArg (QuotientGroup.mk' (Subgroup.center SL(4, F)))
      (permutation_conj σ hσ r a)
    have hr : root (σ.symm r.val.1) (σ.symm r.val.2)
        (fun h => r.property (σ.symm.injective h)) = s := Subtype.ext (Prod.ext hri hrj)
    rw [hr] at h
    exact h
  · intro a
    have h := congrArg (QuotientGroup.mk' (Subgroup.center SL(4, F)))
      (permutation_conj σ hσ s a)
    have hs : root (σ.symm s.val.1) (σ.symm s.val.2)
        (fun h => s.property (σ.symm.injective h)) = r := Subtype.ext (Prod.ext hsi hsj)
    rw [hs] at h
    exact h

private def projectiveTorus (i j : Fin 4) (hij : i ≠ j) : PSL(4, F) :=
  QuotientGroup.mk (torus i j hij)

private theorem projectiveTorus_conj (i j : Fin 4) (hij : i ≠ j) (r : Root 4) (a : F) :
    projectiveTorus i j hij * projectiveRoot r a * (projectiveTorus i j hij)⁻¹ =
      projectiveRoot r (sign i j r.val.1 * sign i j r.val.2 * a) := by
  exact congrArg (QuotientGroup.mk' (Subgroup.center SL(4, F))) (torus_conj i j hij r a)

private theorem projectiveTorus_commute (i j k l : Fin 4) (hij : i ≠ j) (hkl : k ≠ l) :
    Commute (projectiveTorus (F := F) i j hij) (projectiveTorus k l hkl) :=
  (torus_commute i j k l hij hkl).map (QuotientGroup.mk' (Subgroup.center SL(4, F)))

private noncomputable def auxiliary (r : Root 4) : Fin 4 := (fourth r.val.1 r.val.2 r.val.2).choose
private theorem auxiliary_left (r : Root 4) : auxiliary r ≠ r.val.1 :=
  (fourth r.val.1 r.val.2 r.val.2).choose_spec.1
private theorem auxiliary_right (r : Root 4) : auxiliary r ≠ r.val.2 :=
  (fourth r.val.1 r.val.2 r.val.2).choose_spec.2.1

private noncomputable def rootTorus (r : Root 4) : PSL(4, F) :=
  projectiveTorus r.val.1 (auxiliary r) (auxiliary_left r).symm

private theorem rootTorus_conj (r : Root 4) (a : F) :
    rootTorus r * projectiveRoot r a * (rootTorus r)⁻¹ = projectiveRoot r (-a) := by
  rw [rootTorus, projectiveTorus_conj]
  simp [sign, r.property.symm, (auxiliary_right r).symm]

private theorem triple_signs (i j k : Fin 4) (hij : i ≠ j) (_hjk : j ≠ k) (hik : i ≠ k) :
    ∃ l : Fin 4, i ≠ l ∧
      sign (F := F) i l i = -1 ∧ sign (F := F) i l j = 1 ∧ sign (F := F) i l k = 1 := by
  obtain ⟨l, hli, hlj, hlk⟩ := fourth i j k
  exact ⟨l, hli.symm, by simp [sign], by simp [sign, hij.symm, hlj.symm],
    by simp [sign, hik.symm, hlk.symm]⟩

private theorem shared_separator (r s : Root 4) (hne : r ≠ s)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1)
    (hshared : r.val.1 = s.val.1 ∨ r.val.2 = s.val.2) :
    ∃ (i j : Fin 4) (_hij : i ≠ j),
      sign (F := F) i j r.val.1 * sign i j r.val.2 = -1 ∧
      sign (F := F) i j s.val.1 * sign i j s.val.2 = 1 := by
  rcases hshared with hl | hr
  · have hrr : r.val.2 ≠ s.val.2 := fun h => hne (Subtype.ext (Prod.ext hl h))
    obtain ⟨l, hli, hi, hj, hk⟩ := triple_signs (F := F) r.val.2 r.val.1 s.val.2
      r.property.symm hsr.symm hrr
    refine ⟨r.val.2, l, hli, ?_, ?_⟩
    · rw [hj, hi, one_mul]
    · rw [← hl, hj, hk, one_mul]
  · have hrr : r.val.1 ≠ s.val.1 := fun h => hne (Subtype.ext (Prod.ext h hr))
    obtain ⟨l, hli, hi, hj, hk⟩ := triple_signs (F := F) r.val.1 r.val.2 s.val.1
      r.property hrs hrr
    refine ⟨r.val.1, l, hli, ?_, ?_⟩
    · rw [hi, hj, mul_one]
    · rw [← hr, hj, hk, mul_one]

section Extension
variable {E G : Type*} [Group E] [Group G]
variable (f : E →* G) (hc : f.ker ≤ Subgroup.center E)
include hc

private theorem commute_signed {x y a b : E} (hxy : Commute x y)
    (ha : f a = 1 ∨ f a = f x ∨ f a = (f x)⁻¹)
    (hb : f b = 1 ∨ f b = f y ∨ f b = (f y)⁻¹) : Commute a b := by
  rcases ha with ha | ha | ha
  · exact (Subgroup.mem_center_iff.mp (hc (by simpa only [MonoidHom.mem_ker] using ha)) b).symm
  all_goals rcases hb with hb | hb | hb
  · exact Subgroup.mem_center_iff.mp (hc (by simpa only [MonoidHom.mem_ker] using hb)) a
  · apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hc ha hb]
    exact hxy.commutator_eq
  · apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hc ha (hb.trans (map_inv f y).symm)]
    exact hxy.inv_right.commutator_eq
  · exact Subgroup.mem_center_iff.mp (hc (by simpa only [MonoidHom.mem_ker] using hb)) a
  · apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hc (ha.trans (map_inv f x).symm) hb]
    exact hxy.inv_left.commutator_eq
  · apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hc (ha.trans (map_inv f x).symm)
      (hb.trans (map_inv f y).symm)]
    exact hxy.inv_left.inv_right.commutator_eq

/-- An odd central kernel makes simultaneously inverted lifts unique. -/
private theorem equal_inverted [Finite E] (hk : Nat.card f.ker = 3) (t x y : E)
    (hxy : f x = f y) (htx : t * x * t⁻¹ = x⁻¹) (hty : t * y * t⁻¹ = y⁻¹) : x = y := by
  let z := x * y⁻¹
  have hz : z ∈ f.ker := by simp [z, MonoidHom.mem_ker, hxy]
  have hzc := hc hz
  have hcomm : Commute x y := by
    change x * y = y*x
    have hh := (Subgroup.mem_center_iff.mp hzc y).symm
    change (x * y⁻¹)*y = y*(x * y⁻¹) at hh
    have hh' := congrArg (· * y) hh
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh'
  have ht : t * z * t⁻¹ = z := by
    rw [Subgroup.mem_center_iff.mp hzc t, mul_inv_cancel_right]
  have hi : t * z * t⁻¹ = z⁻¹ := by
    change MulAut.conj t (x * y⁻¹) = (x * y⁻¹)⁻¹
    rw [map_mul, map_inv]
    change (t * x * t⁻¹) * (t * y * t⁻¹)⁻¹ = _
    rw [htx, hty, inv_inv, mul_inv_rev, inv_inv]
    exact hcomm.inv_left.eq
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two, ht.symm.trans hi, inv_mul_eq_one]
    exact ht.symm.trans hi
  have hz3 : z ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z, hz⟩ : f.ker))
    rw [hk] at hh
    exact congrArg Subtype.val hh
  have hone : z = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 3) (orderOf_dvd_of_pow_eq_one hz2)
      (orderOf_dvd_of_pow_eq_one hz3))
  exact mul_inv_eq_one.mp hone
end Extension

section FieldThree
variable [Finite F] (hF : Nat.card F = 3)
include hF

private theorem three_eq_zero : (3 : F) = 0 := by
  let := Fintype.ofFinite F
  simpa only [← Nat.card_eq_fintype_card, hF, Nat.cast_ofNat] using Nat.cast_card_eq_zero F

private theorem scalar_cases (a : F) : a = 0 ∨ a = 1 ∨ a = -1 := by
  let := Fintype.ofFinite F
  have hp : a ^ 3 = a := by
    simpa only [← Nat.card_eq_fintype_card, hF] using FiniteField.pow_card a
  have h : a * (a - 1) * (a + 1) = 0 := by
    linear_combination hp
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h))

private theorem root_cube (r : Root 4) (a : F) : projectiveRoot r a ^ 3 = 1 := by
  have ha : a + a+a = 0 := by linear_combination a * three_eq_zero hF
  rw [show 3 = 2 + 1 from rfl, pow_succ, pow_two, projectiveRoot_relations.add,
    projectiveRoot_relations.add, ha, projectiveRoot_relations.zero]

variable {E : Type*} [Group E] (f : E →* PSL(4, F))
    (hf : Function.Surjective f) (hc : f.ker ≤ Subgroup.center E)

private noncomputable def preimage (g : PSL(4, F)) : E := (hf g).choose
omit hF [Finite F] in
private theorem preimage_map (g : PSL(4, F)) : f (preimage f hf g) = g := (hf g).choose_spec

private theorem signed_images (r : Root 4) (a : F) (x : E) (hx : f x = projectiveRoot r a) :
    f x = 1 ∨ f x = f (preimage f hf (projectiveRoot r 1)) ∨
      f x = (f (preimage f hf (projectiveRoot r 1)))⁻¹ := by
  rw [hx, preimage_map]
  rcases scalar_cases hF a with rfl | rfl | rfl
  · exact Or.inl (projectiveRoot_relations.zero r)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (projectiveRoot_relations.neg r 1))

include hf hc in
private theorem same_root_commute (r : Root 4) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot r b) : Commute x y :=
  commute_signed f hc (Commute.refl (preimage f hf (projectiveRoot r 1)))
    (signed_images hF f hf r a x hx) (signed_images hF f hf r b y hy)

include hF hf hc in
private theorem distant_commute (r s : Root 4) (a b : F) {x y : E}
    (hx : f x = projectiveRoot r a) (hy : f y = projectiveRoot s b)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) : Commute x y := by
  by_cases he : r = s
  · subst s
    exact same_root_commute hF f hf hc r a b hx hy
  apply commute_signed f hc (x := preimage f hf (projectiveRoot r 1))
    (y := preimage f hf (projectiveRoot s 1)) ?_
    (signed_images hF f hf r a x hx) (signed_images hF f hf s b y hy)
  have hbase : Commute (projectiveRoot (F := F) r 1) (projectiveRoot s 1) :=
    projectiveRoot_relations.commute r s 1 1 hrs hsr
  by_cases hs : r.val.1 = s.val.1 ∨ r.val.2 = s.val.2
  · obtain ⟨i, j, hij, hr, hs⟩ := shared_separator (F := F) r s he hrs hsr hs
    apply CentralExtension.commute_lifts_of_partial_inversion f hf hc
      (projectiveRoot r 1) (projectiveRoot s 1) (projectiveTorus i j hij)
      (by decide : Nat.Coprime 3 2) (root_cube hF r 1) hbase
    · rw [projectiveTorus_conj, hr, neg_one_mul, projectiveRoot_relations.neg]
    · apply mul_inv_eq_iff_eq_mul.mp
      rw [projectiveTorus_conj, hs, one_mul]
    · exact preimage_map f hf _
    · exact preimage_map f hf _
  · push Not at hs
    obtain ⟨t, ht, ht'⟩ := swap_roots (F := F) r s hs.1 hs.2 hsr.symm hrs
    exact CentralExtension.commute_lifts_of_swap f hf hc
      (projectiveRoot r 1) (projectiveRoot s 1) t
      (by decide : Nat.Coprime 3 2) (root_cube hF r 1) hbase (ht 1) (ht' 1)
      _ _ (preimage_map f hf _) (preimage_map f hf _)

/-- Normalization by a root inverter; its root coefficient is unchanged in characteristic three. -/
private noncomputable def rootLift (r : Root 4) (a : F) : E :=
  ⁅preimage f hf (rootTorus r), preimage f hf (projectiveRoot r a)⁆

include hF in
private theorem rootLift_map (r : Root 4) (a : F) : f (rootLift f hf r a) = projectiveRoot r a := by
  rw [rootLift, map_commutatorElement, preimage_map, preimage_map, commutatorElement_def,
    rootTorus_conj, ← projectiveRoot_relations.neg r a, projectiveRoot_relations.add]
  congr 1
  linear_combination -a * three_eq_zero hF

include hc in
omit hF [Finite F] in
/-- Commuting base diagonals give exact equivariance of the normalized lifts. -/
private theorem rootLift_conj (i j : Fin 4) (hij : i ≠ j) (t : E)
    (ht : f t = projectiveTorus i j hij) (r : Root 4) (a : F) :
    t * rootLift f hf r a * t⁻¹ =
      rootLift f hf r (sign i j r.val.1 * sign i j r.val.2 * a) := by
  rw [rootLift, conjugate_commutatorElement, rootLift]
  apply CentralExtension.commutator_eq_of_image_eq f hc
  · simp only [map_mul, map_inv, ht, preimage_map]
    unfold rootTorus
    rw [(projectiveTorus_commute i j r.val.1 (auxiliary r) hij
      (auxiliary_left r).symm).eq, mul_inv_cancel_right]
  · simp only [map_mul, map_inv, ht, preimage_map, projectiveTorus_conj]

include hF hc in
private theorem rootLift_add (r : Root 4) (a b : F) :
    rootLift f hf r a * rootLift f hf r b = rootLift f hf r (a + b) := by
  have hpre : f (preimage f hf (projectiveRoot r (a + b))) =
      f (preimage f hf (projectiveRoot r a) * preimage f hf (projectiveRoot r b)) := by
    rw [map_mul, preimage_map, preimage_map, preimage_map, projectiveRoot_relations.add]
  have hcom := same_root_commute hF f hf hc r a b
    (preimage_map f hf (projectiveRoot r a)) (rootLift_map hF f hf r b)
  symm
  change ⁅preimage f hf (rootTorus r), preimage f hf (projectiveRoot r (a + b))⁆ = _
  rw [CentralExtension.commutator_eq_of_image_eq f hc rfl hpre,
    commutatorElement_mul_right_eq_mul_conj]
  change rootLift f hf r a * preimage f hf (projectiveRoot r a) * rootLift f hf r b *
    (preimage f hf (projectiveRoot r a))⁻¹ = _
  rw [mul_assoc (rootLift f hf r a), hcom.eq, ← mul_assoc, mul_inv_cancel_right]

include hF hc in
private theorem rootLift_zero (r : Root 4) : rootLift f hf r 0 = 1 := by
  have h := rootLift_add hF f hf hc r 0 0
  simpa only [add_zero, mul_eq_left] using h

include hF hc in
private theorem rootLift_neg (r : Root 4) (a : F) : rootLift f hf r (-a) = (rootLift f hf r a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [rootLift_add hF f hf hc, neg_add_cancel, rootLift_zero hF f hf hc]

include hF hc in
/-- The chain error is central and inverted, hence trivial in the order-three kernel. -/
private theorem rootLift_chain [Finite E] (hk : Nat.card f.ker = 3)
    (i j k : Fin 4) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : F) :
    ⁅rootLift f hf (root i j hij) a, rootLift f hf (root j k hjk) b⁆ =
      rootLift f hf (root i k hik) (a * b) := by
  let p := root i j hij
  let q := root j k hjk
  let r := root i k hik
  obtain ⟨l, hil, hi, hj, hk'⟩ := triple_signs (F := F) i j k hij hjk hik
  obtain ⟨t, ht⟩ := hf (projectiveTorus i l hil)
  have htp : t * rootLift f hf p a * t⁻¹ = (rootLift f hf p a)⁻¹ := by
    rw [rootLift_conj f hf hc i l hil t ht]
    change rootLift f hf p (sign i l i * sign i l j * a) = _
    rw [hi, hj, mul_one, neg_one_mul, rootLift_neg hF f hf hc]
  have htq : t * rootLift f hf q b * t⁻¹ = rootLift f hf q b := by
    rw [rootLift_conj f hf hc i l hil t ht]
    change rootLift f hf q (sign i l j * sign i l k * b) = _
    rw [hj, hk', one_mul, one_mul]
  have htr : t * rootLift f hf r (a * b) * t⁻¹ = (rootLift f hf r (a * b))⁻¹ := by
    rw [rootLift_conj f hf hc i l hil t ht]
    change rootLift f hf r (sign i l i * sign i l k * (a * b)) = _
    rw [hi, hk', mul_one, neg_one_mul, rootLift_neg hF f hf hc]
  have hmap : f ⁅rootLift f hf p a, rootLift f hf q b⁆ = projectiveRoot r (a * b) := by
    rw [map_commutatorElement, rootLift_map hF, rootLift_map hF]
    exact projectiveRoot_relations.chain i j k hij hjk hik a b
  have hcom : Commute (rootLift f hf p a) ⁅rootLift f hf p a, rootLift f hf q b⁆ :=
    distant_commute hF f hf hc p r a (a * b) (rootLift_map hF f hf p a) hmap hij.symm hik.symm
  apply equal_inverted f hc hk t _ _ (hmap.trans (rootLift_map hF f hf r (a * b)).symm) _ htr
  rw [conjugate_commutatorElement, htp, htq, commutatorElement_inv_left,
    ← commutatorElement_inv]
  rw [hcom.inv_left.inv_right.eq, inv_mul_cancel_right]

include hF hc in
private theorem rootLift_relations [Finite E] (hk : Nat.card f.ker = 3) :
    Relations (rootLift f hf) where
  add := rootLift_add hF f hf hc
  distant r s a b hrs hsr := (distant_commute hF f hf hc r s a b
    (rootLift_map hF f hf r a) (rootLift_map hF f hf s b) hrs hsr).commutator_eq
  chain := rootLift_chain hF f hf hc hk

include hf hc in
/-- Sign-torus commutators lift every elementary root relation over the
three-element field in a central extension with kernel of order three. -/
theorem exists_root_lifts_three [Finite E] (hk : Nat.card f.ker = 3) :
    ∃ x : Root 4 → F → E, Relations x ∧ ∀ r a, f (x r a) = projectiveRoot r a :=
  ⟨rootLift f hf, rootLift_relations hF f hf hc hk, rootLift_map hF f hf⟩

end FieldThree

end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime.RootLiftsThree

open scoped MatrixGroups
open Theory.SpecificGroups.LinearHigher
namespace Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
universe u
variable {F : Type u} [Field F] [Finite F]

/-- Compatible degree-four root lifts over the three-element field. -/
theorem primeKernelRootLifts_three (hF : Nat.card F = 3) : PrimeKernelRootLifts F 3 := by
  intro E _ _ c hk
  exact RootLiftsThree.exists_root_lifts_three hF c.toMonoidHom c.surjective c.ker_le_center hk

/-- The defining prime is absent from every finite perfect central kernel
over PSL₄ of the three-element field. This discharges the ternary local
root-lifting premise in the defining-prime reduction. -/
theorem not_dvd_kernel_three (hF : Nat.card F = 3)
    {E : Type u} [Group E] [Finite E] (c : PerfectCentralCovering.Cover E PSL(4, F)) :
    ¬ 3 ∣ Nat.card c.toMonoidHom.ker :=
  not_dvd_kernel_of_primeKernelRootLifts (by decide) hF (primeKernelRootLifts_three hF) c

end Theory.SpecificGroups.HigherClassicalCovers.Linear.DefiningPrime
