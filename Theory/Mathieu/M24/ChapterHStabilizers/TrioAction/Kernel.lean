module

public import Theory.Mathieu.M24.ChapterHStabilizers.TrioAction.Coordinates

/-!
# The elementary translation core of a native trio stabilizer

Paired translations realize every triple of binary three-vectors with sum
zero. The Golay row-pairing constraint proves that these are exactly the
intrinsic two-core. The first two vectors are free, giving an elementary
abelian group of order 64. The ambient equivalence uses the literal subgroup
inclusion into M24.

Source: Aschbacher–Smith H.14.1(3), printed pp.396–397; Aschbacher,
*Sporadic Groups*, Lemma 20.2.
-/

public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped BigOperators

namespace Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
noncomputable section
/-- Translation triples with zero sum. -/
@[expose] def translationSpace : Submodule (ZMod 2) (Fin 3 → Vector) where
  carrier := {t | ∑ i, t i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b hx hy
    change (∑ i : Fin 3, (a i + b i)) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' c t ht := by
    change (∑ i, c • t i) = 0
    rw [← Finset.smul_sum, ht, smul_zero]

lemma translationSpace_last (t : translationSpace) : t.val 2 = t.val 0 + t.val 1 := by
  have h := t.property
  change (∑ i, t.val i) = 0 at h
  rw [Fin.sum_univ_three] at h
  have hh := eq_neg_of_add_eq_zero_right h
  funext j
  simpa only [Pi.neg_apply, ZMod.neg_eq_self_mod_two] using congrFun hh j

private def translationElement (t : translationSpace) : Kernel :=
  ⟨pairedTranslation 1 (t.val 0) * pairedTranslation 0 (t.val 1),
    (pCore 2 Stabilizer).mul_mem (pairedTranslation_mem_twoCore _ _)
      (pairedTranslation_mem_twoCore _ _)⟩

private lemma translationElement_point (t : translationSpace) (i : Fin 3) (v : Vector) :
    (translationElement t).val.val.val (point (i,v)) = point (i, v + t.val i) := by
  change (pairedTranslation 1 (t.val 0)).val.val
    ((pairedTranslation 0 (t.val 1)).val.val (point (i,v))) = _
  rw [pairedTranslation_point, pairedTranslation_point]
  fin_cases i <;> simp [translationSpace_last, add_comm, add_left_comm]

lemma kernel_ext {x y : Kernel} (h : ∀ i v,
    x.val.val.val (point (i,v)) = y.val.val.val (point (i,v))) : x = y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro z
  obtain ⟨⟨i,v⟩, rfl⟩ := point.surjective z
  exact h i v

def translation : Multiplicative translationSpace →* Kernel where
  toFun t := translationElement t.toAdd
  map_one' := by
    apply kernel_ext
    intro i v
    rw [translationElement_point]
    simp
  map_mul' x y := by
    show translationElement (x.toAdd + y.toAdd) =
      translationElement x.toAdd * translationElement y.toAdd
    apply kernel_ext
    intro i v
    simp only [Subgroup.coe_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [translationElement_point, translationElement_point, translationElement_point]
    simp only [Submodule.coe_add, Pi.add_apply, add_left_comm, add_comm]

lemma translation_point (t : Multiplicative translationSpace) (i : Fin 3) (v : Vector) :
    (translation t).val.val.val (point (i,v)) = point (i,v + t.toAdd.val i) :=
  translationElement_point _ _ _

lemma translation_bijective : Function.Bijective translation := by
  constructor
  · intro t u h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    have hh := congrArg (fun k : Kernel => k.val.val.val (point (i,0))) h
    rw [translation_point, translation_point] at hh
    simpa using congrArg Prod.snd (point.injective hh)
  · intro k
    obtain ⟨t, ht⟩ := (mem_standardTwoCore_iff k.val).mp k.property
    refine ⟨Multiplicative.ofAdd ⟨t, translation_sum_zero k.val t ht⟩, ?_⟩
    apply kernel_ext
    intro i v
    rw [translation_point, ht]
    rfl

@[expose] def translationEquiv : Multiplicative translationSpace ≃* Kernel :=
  MulEquiv.ofBijective translation translation_bijective

/-- The first two translations determine the third. -/
def translationPairEquiv : translationSpace ≃ₗ[ZMod 2] (Vector × Vector) where
  toFun t := (t.val 0, t.val 1)
  invFun p := ⟨![p.1, p.2, p.1 + p.2], by
    change (∑ i : Fin 3, ![p.1, p.2, p.1 + p.2] i) = 0
    rw [Fin.sum_univ_three]
    funext j
    exact CharTwo.add_self_eq_zero (p.1 j + p.2 j)⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    fin_cases i <;> simp [translationSpace_last]
  right_inv p := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma translationSpace_card : Nat.card translationSpace = 64 := by
  rw [Nat.card_congr translationPairEquiv.toEquiv]
  simp [Nat.card_eq_fintype_card]

lemma core_card : Nat.card Kernel = 64 := by
  rw [Nat.card_congr (translationEquiv.symm.toEquiv.trans Multiplicative.toAdd)]
  exact translationSpace_card

lemma core_elementary : IsElementaryAbelian 2 Kernel where
  toIsMulCommutative := isMulCommutative_iff.mpr (by
    intro x y
    apply translationEquiv.symm.injective
    simp only [map_mul, mul_comm])
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply translationEquiv.symm.injective
    rw [map_pow, map_one, pow_two]
    change Multiplicative.ofAdd ((translationEquiv.symm x).toAdd +
      (translationEquiv.symm x).toAdd) = Multiplicative.ofAdd 0
    congr 1
    apply Subtype.ext
    funext i j
    exact CharTwo.add_self_eq_zero _)

/-- The core included in native M24, with normality relative to its stabilizer. -/
@[expose] def core : Subgroup M24 := Kernel.map Stabilizer.subtype

@[expose] def ambientTranslationEquiv : Multiplicative translationSpace ≃* core :=
  translationEquiv.trans (Kernel.equivMapOfInjective Stabilizer.subtype
    Stabilizer.subtype_injective)

lemma core_ambient_card : Nat.card core = 64 := by
  rw [core, Subgroup.card_map_of_injective Stabilizer.subtype_injective, core_card]

lemma core_ambient_elementary : IsElementaryAbelian 2 core := by
  let := core_elementary
  exact IsElementaryAbelian.map_subtype

end
end Sporadic.Mathieu.M24ChapterHStabilizers.TrioAction
