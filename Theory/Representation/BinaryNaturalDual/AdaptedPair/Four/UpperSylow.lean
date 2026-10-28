module

public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Coordinates
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The upper/graph Sylow subgroup in dimension four

The actual coordinate-flag stabilizer has six free binary upper entries and
therefore order 64. The reversal-graph automorphism sends its matrix to the
reversal-transpose of the inverse, so it normalizes this subgroup. Its inner
image and the order-two graph subgroup intersect trivially; ambient
multiplication gives their semidirect product and the two-coset normal form.

The standard subgroup consequently has order 128. The finite-field GL order
formula gives |GL₄(2)| = 20160; when the inner automorphisms have index two,
the ambient automorphism group has order 40320 and the standard subgroup has
odd index 315. This constructs the actual ambient Sylow two-subgroup.

Source: the standard upper/graph calculation in the corrected adapted-pair
form of Aschbacher–Smith H.9.1(4), printed p.390. The parameter count adapts
`BinaryLinear.FiveFlagGeometry.SylowOvergroups.Sylow` to dimension four.
-/

public section

open BinaryNaturalDual BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.AdaptedPair.Four.UpperSylow

private abbrev UpperPosition := {ij : Fin 4 × Fin 4 // ij.1 < ij.2}

private def upperMatrix (f : UpperPosition → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  fun i j => if i = j then 1 else if h : i < j then f ⟨(i, j), h⟩ else 0

private theorem upperMatrix_triangular (f : UpperPosition → ZMod 2) :
    (upperMatrix f).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  simp only [upperMatrix, if_neg (ne_of_gt hji), dif_neg (not_lt_of_ge hji.le)]

private theorem upperMatrix_det (f : UpperPosition → ZMod 2) :
    (upperMatrix f).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (upperMatrix_triangular f)]
  simp [upperMatrix]

private def upperSL (f : UpperPosition → ZMod 2) :
    Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨upperMatrix f, upperMatrix_det f⟩

private noncomputable def fromParameters (f : UpperPosition → ZMod 2) : upperGroup 4 :=
  ⟨slEquivLinear 4 (upperSL f), by
    apply (mem_upperGroup_iff _).mpr
    change (((slEquivLinear 4).symm ((slEquivLinear 4) (upperSL f))).val).IsUpperTriangular
    rw [MulEquiv.symm_apply_apply]
    exact upperMatrix_triangular f⟩

private theorem coordinateMatrix_fromParameters (f : UpperPosition → ZMod 2) :
    coordinateMatrix (fromParameters f) = upperMatrix f := by
  change (((slEquivLinear 4).symm ((slEquivLinear 4) (upperSL f))).val) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

private noncomputable def parametersEquiv : upperGroup 4 ≃ (UpperPosition → ZMod 2) where
  toFun g ij := coordinateMatrix g ij.val.1 ij.val.2
  invFun := fromParameters
  left_inv g := by
    apply Subtype.ext
    apply coordinateMatrix_injective
    rw [coordinateMatrix_fromParameters]
    ext i j
    by_cases he : i = j
    · subst j
      simp [upperMatrix, upper_diagonal g.property]
    · by_cases hij : i < j
      · simp [upperMatrix, he, hij]
      · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) (Ne.symm he)
        simp [upperMatrix, he, hij, (mem_upperGroup_iff g).mp g.property hji]
  right_inv f := by
    funext ⟨⟨i, j⟩, hij⟩
    change coordinateMatrix (fromParameters f) i j = f ⟨(i, j), hij⟩
    rw [coordinateMatrix_fromParameters]
    simp [upperMatrix, ne_of_lt hij, hij]

/-- The six freely chosen binary upper entries count the actual stabilizer. -/
theorem upperGroup_card : Nat.card (upperGroup 4) = 64 := by
  rw [Nat.card_congr parametersEquiv, Nat.card_fun]
  have hpos : Nat.card UpperPosition = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [hpos]
  norm_num

theorem linearGroup_card : Nat.card (LinearGroup 4) = 20160 := by
  calc
    Nat.card (LinearGroup 4) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) :=
      (Nat.card_congr (matrixEquivLinear 4).toEquiv).symm
    _ = ∏ i : Fin 4, (Fintype.card (ZMod 2) ^ 4 - Fintype.card (ZMod 2) ^ i.val) :=
      Matrix.card_GL_field (𝔽 := ZMod 2) 4
    _ = 20160 := by decide

private theorem tau_inv (d : CoordinateAction 4) : (tau 4)⁻¹ = tau 4 :=
  inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using tau_sq d)

/-- Reversal-transpose of the inverse is the actual graph-twisted matrix. -/
theorem coordinateMatrix_tau (d : CoordinateAction 4) (g : LinearGroup 4) (i j : Fin 4) :
    coordinateMatrix (tau 4 g) i j = coordinateMatrix g⁻¹ j.rev i.rev := by
  have hc : MulAut.conj (tau 4 g) = tau 4 * MulAut.conj g * tau 4 := by
    have h : MulAut.conj (tau 4 g) = tau 4 * MulAut.conj g * (tau 4)⁻¹ := by
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply]
    simpa only [tau_inv d] using h
  have he := congrArg (fun a : MulAut (LinearGroup 4) =>
    (linearAction d a (axis j, 0)).1 i) hc
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] at he
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    linearAction_tau_fst, linearAction_inner, BinaryLinear.NaturalDualFlag.action_snd] at he
  rw [coordinateMatrix_apply, he, coordinateMatrix_apply]
  rw [linearAction_tau]
  change dotProduct (reversal 4 (axis j)) (g.symm (axis i.rev)) = _
  have hr : reversal 4 (axis j) = axis j.rev := by
    ext k
    simp only [reversal_apply, axis, Pi.single_apply]
    have hh : k.rev = j ↔ k = j.rev := by
      constructor <;> intro h <;> simpa using congrArg Fin.rev h
    simp only [hh]
  rw [hr]
  simp [axis]

theorem tau_mem_upperGroup (d : CoordinateAction 4) {g : LinearGroup 4}
    (hg : g ∈ upperGroup 4) : tau 4 g ∈ upperGroup 4 := by
  apply (mem_upperGroup_iff _).mpr
  intro i j hji
  rw [coordinateMatrix_tau d]
  exact (mem_upperGroup_iff _).mp ((upperGroup 4).inv_mem hg) (by simpa using hji)

/-- The upper inner subgroup of the actual automorphism group. -/
noncomputable abbrev innerUpper : Subgroup (MulAut (LinearGroup 4)) :=
  (upperGroup 4).map MulAut.conj

theorem innerUpper_le_innerGroup : innerUpper ≤ innerGroup 4 := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

theorem tau_normalizes (d : CoordinateAction 4) :
    tau 4 ∈ Subgroup.normalizer (innerUpper : Set (MulAut (LinearGroup 4))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  have hf {b : MulAut (LinearGroup 4)} (hb : b ∈ innerUpper) :
      tau 4 * b * (tau 4)⁻¹ ∈ innerUpper := by
    obtain ⟨g, hg, rfl⟩ := hb
    have he : tau 4 * MulAut.conj g * (tau 4)⁻¹ = MulAut.conj (tau 4 g) := by
      ext x
      simp [MulAut.mul_apply, MulAut.conj_apply]
    rw [he]
    exact Subgroup.mem_map_of_mem _ (tau_mem_upperGroup d hg)
  constructor
  · exact hf
  · intro ha
    have hh := hf ha
    simp only [tau_inv d, ← mul_assoc, ← pow_two, tau_sq d, one_mul] at hh
    simpa only [mul_assoc, ← pow_two, tau_sq d, mul_one] using hh

open scoped Pointwise

theorem tau_orderOf (d : CoordinateAction 4) : orderOf (tau 4) = 2 :=
  orderOf_eq_prime (tau_sq d) (fun h => tau_not_inner d (h ▸ (innerGroup 4).one_mem))

theorem mem_zpowers_tau_iff (d : CoordinateAction 4) (a : MulAut (LinearGroup 4)) :
    a ∈ Subgroup.zpowers (tau 4) ↔ a = 1 ∨ a = tau 4 := by
  constructor
  · intro ha
    have hfin : IsOfFinOrder (tau 4) :=
      isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, tau_sq d⟩
    classical
    rw [hfin.mem_zpowers_iff_mem_range_orderOf, tau_orderOf d] at ha
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp ha
    have hi2 := Finset.mem_range.mp hi
    have hi' : i = 0 ∨ i = 1 := by omega
    rcases hi' with rfl | rfl
    · exact Or.inl (by simpa using he.symm)
    · exact Or.inr (by simpa using he.symm)
  · rintro (rfl | rfl)
    · exact (Subgroup.zpowers (tau 4)).one_mem
    · exact Subgroup.mem_zpowers _

theorem innerUpper_disjoint_zpowers (d : CoordinateAction 4) :
    Disjoint innerUpper (Subgroup.zpowers (tau 4)) := by
  apply Subgroup.disjoint_def.mpr
  intro a ha ht
  rcases (mem_zpowers_tau_iff d a).mp ht with h | rfl
  · exact h
  · exact (tau_not_inner d (innerUpper_le_innerGroup ha)).elim

theorem innerUpper_inf_zpowers (d : CoordinateAction 4) :
    innerUpper ⊓ Subgroup.zpowers (tau 4) = ⊥ :=
  (innerUpper_disjoint_zpowers d).eq_bot

theorem standardGroup_set (d : CoordinateAction 4) :
    (standardGroup 4 : Set (MulAut (LinearGroup 4))) =
      (innerUpper : Set (MulAut (LinearGroup 4))) *
        (Subgroup.zpowers (tau 4) : Set (MulAut (LinearGroup 4))) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (Subgroup.zpowers_le.mpr (tau_normalizes d))

/-- Every standard actor has the inner or the graph-coset normal form. -/
theorem normal_form (d : CoordinateAction 4) :
    ∀ a ∈ standardGroup 4, ∃ u ∈ upperGroup 4,
      a = MulAut.conj u ∨ a = MulAut.conj u * tau 4 := by
  intro a ha
  have hm : a ∈ (innerUpper : Set (MulAut (LinearGroup 4))) *
      (Subgroup.zpowers (tau 4) : Set (MulAut (LinearGroup 4))) := by
    rw [← standardGroup_set d]
    exact ha
  obtain ⟨b, ⟨u, hu, rfl⟩, c, hc, rfl⟩ := hm
  refine ⟨u, hu, ?_⟩
  rcases (mem_zpowers_tau_iff d c).mp hc with rfl | rfl
  · exact Or.inl (mul_one _)
  · exact Or.inr rfl

/-- The first semidirect factor is faithfully the actual upper group. -/
noncomputable def upperEquivInner (d : CoordinateAction 4) : upperGroup 4 ≃* innerUpper :=
  (upperGroup 4).equivMapOfInjective MulAut.conj (conj_injective d)

@[simp] theorem upperEquivInner_apply (d : CoordinateAction 4) (u : upperGroup 4) :
    (upperEquivInner d u : MulAut (LinearGroup 4)) = MulAut.conj (u : LinearGroup 4) := by rfl

theorem innerUpper_card (d : CoordinateAction 4) : Nat.card innerUpper = 64 := by
  rw [← Nat.card_congr (upperEquivInner d).toEquiv, upperGroup_card]

/-- The conjugation action of the graph factor on the inner upper group. -/
noncomputable def graphAction (d : CoordinateAction 4) :
    Subgroup.zpowers (tau 4) →* MulAut innerUpper :=
  innerUpper.normalizerMonoidHom.comp
    (Subgroup.inclusion (Subgroup.zpowers_le.mpr (tau_normalizes d)))

/-- The graph factor acts by its actual ambient conjugation. -/
theorem graphAction_apply (d : CoordinateAction 4) (c : Subgroup.zpowers (tau 4))
    (u : innerUpper) : (graphAction d c u : MulAut (LinearGroup 4)) =
      (c : MulAut (LinearGroup 4)) * u * (c : MulAut (LinearGroup 4))⁻¹ := by rfl

/-- Multiplication embeds the actual semidirect factors in the standard group. -/
private noncomputable def semidirectHom (d : CoordinateAction 4) :
    innerUpper ⋊[graphAction d] Subgroup.zpowers (tau 4) →* standardGroup 4 :=
  (SemidirectProduct.monoidHomSubgroup
    (Subgroup.zpowers_le.mpr (tau_normalizes d))).codRestrict (standardGroup 4)
      (fun a => Subgroup.mul_mem_sup a.left.property a.right.property)

private theorem semidirectHom_bijective (d : CoordinateAction 4) :
    Function.Bijective (semidirectHom d) := by
  constructor
  · intro a b he
    have he' : (a.left : MulAut (LinearGroup 4)) * a.right =
        (b.left : MulAut (LinearGroup 4)) * b.right := congrArg Subtype.val he
    have hh : (a.left, a.right) = (b.left, b.right) :=
      Subgroup.mul_injective_of_disjoint (innerUpper_disjoint_zpowers d) he'
    exact SemidirectProduct.ext (congrArg Prod.fst hh) (congrArg Prod.snd hh)
  · intro a
    have ha : (a : MulAut (LinearGroup 4)) ∈
        (innerUpper : Set (MulAut (LinearGroup 4))) *
        (Subgroup.zpowers (tau 4) : Set (MulAut (LinearGroup 4))) := by
      rw [← standardGroup_set d]
      exact a.property
    obtain ⟨b, hb, c, hc, he⟩ := ha
    exact ⟨⟨⟨b, hb⟩, ⟨c, hc⟩⟩, Subtype.ext he⟩

/-- The standard subgroup is the upper inner group semidirect the order-two
reversal-graph group, with its actual ambient multiplication. -/
noncomputable def semidirectEquiv (d : CoordinateAction 4) :
    innerUpper ⋊[graphAction d] Subgroup.zpowers (tau 4) ≃* standardGroup 4 :=
  MulEquiv.ofBijective (semidirectHom d) (semidirectHom_bijective d)

theorem semidirectEquiv_apply (d : CoordinateAction 4)
    (a : innerUpper ⋊[graphAction d] Subgroup.zpowers (tau 4)) :
    (semidirectEquiv d a : MulAut (LinearGroup 4)) = a.left * a.right := by rfl

theorem standardGroup_card (d : CoordinateAction 4) : Nat.card (standardGroup 4) = 128 := by
  rw [← Nat.card_congr (semidirectEquiv d).toEquiv, SemidirectProduct.card,
    innerUpper_card d, Nat.card_zpowers, tau_orderOf d]

theorem innerGroup_card (d : CoordinateAction 4) : Nat.card (innerGroup 4) = 20160 := by
  rw [innerGroup, ← Nat.card_congr (MonoidHom.ofInjective (conj_injective d)).toEquiv,
    linearGroup_card]

theorem automorphismGroup_card (d : CoordinateAction 4) (hindex : (innerGroup 4).index = 2) :
    Nat.card (MulAut (LinearGroup 4)) = 40320 := by
  have h := (innerGroup 4).index_mul_card
  rw [hindex, innerGroup_card d] at h
  exact h.symm

theorem standardGroup_index (d : CoordinateAction 4) (hindex : (innerGroup 4).index = 2) :
    (standardGroup 4).index = 315 := by
  have h := (standardGroup 4).index_mul_card
  rw [standardGroup_card d, automorphismGroup_card d hindex] at h
  exact Nat.eq_of_mul_eq_mul_right (show 0 < 128 by decide)
    (h.trans (by decide : 40320 = 315 * 128))

theorem standardGroup_isPGroup (d : CoordinateAction 4) : IsPGroup 2 (standardGroup 4) :=
  IsPGroup.of_card (n := 7) (standardGroup_card d)

/-- The concrete standard Sylow two-subgroup of the full automorphism group. -/
noncomputable def standardSylow (d : CoordinateAction 4) (hindex : (innerGroup 4).index = 2) :
    Sylow 2 (MulAut (LinearGroup 4)) :=
  (standardGroup_isPGroup d).toSylow (by rw [standardGroup_index d hindex]; norm_num)

@[simp] theorem standardSylow_coe (d : CoordinateAction 4) (hindex : (innerGroup 4).index = 2) :
    (standardSylow d hindex : Subgroup (MulAut (LinearGroup 4))) = standardGroup 4 := by rfl

end BinaryNaturalDual.AdaptedPair.Four.UpperSylow
