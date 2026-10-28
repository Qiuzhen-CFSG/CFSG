module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Descent
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.Representation.BinaryOffender.GeneratedCore
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Large point-radical subgroups on the twisted tensor

For a nonidentity coefficient twist, a subgroup A of the actual point radical
with |A| > |F|² fixes at most three defining-field dimensions. Its image B on
the two noncentral coordinates has |B| > |F|, and its central kernel is nontrivial.
A central element forces the first matrix shape. The side equations have the
form M σ(w) = h J w. If h were nonzero, a scalar moved by σ would give an
injection B × B into F², contradicting |B| > |F|. Thus h and M vanish, and the
remaining fixed matrix is determined by its entries (0,0), (0,1), and (0,3).
These entries give the literal linear injection into F³.

Actual scalar descent gives binary fixed dimension at most 3s and codimension
at least 13s. Since the point radical has rank 6s, this excludes every point
actor of rank greater than 4s and ratio at most two, retaining the exact model
and component-subgroup maps used in the plane branch.

This repairs the point exclusion needed in Aschbacher–Smith, K.3.4.2,
printed p.457 (PDF p.468), without asserting the false equality of arbitrary
large-subgroup invariants with the full radical's fixed line. The full-radical
proof and counterexample remain in `PointRoots` and `PointRoots.RankObstruction`.
-/

open scoped Matrix TensorProduct
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour SymplecticConjugatePair


namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound
variable {F : Type*} [Field F] [Finite F]

private lemma annihilator_zero (B : AddSubgroup (Fin 2 → F)) (hB : Nat.card F < Nat.card B)
    (a b : F) (h : ∀ w ∈ B, a * w 0 + b * w 1 = 0) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    have hi : Function.Injective (fun w : B => w.val 1) := by
      intro x y he
      dsimp only at he
      apply Subtype.ext
      funext i
      fin_cases i
      · apply mul_left_cancel₀ ha
        have hx := h x.val x.property
        have hy := h y.val y.property
        rw [he] at hx
        exact add_right_cancel (hx.trans hy.symm)
      · exact he
    exact (not_le_of_gt hB) (Nat.card_le_card_of_injective _ hi)
  have hb : b = 0 := by
    by_contra hb
    have hi : Function.Injective (fun w : B => w.val 0) := by
      intro x y he
      dsimp only at he
      apply Subtype.ext
      funext i
      fin_cases i
      · exact he
      · have hx := h x.val x.property
        have hy := h y.val y.property
        simp only [ha, zero_mul, zero_add] at hx hy
        exact mul_left_cancel₀ hb (hx.trans hy.symm)
    exact (not_le_of_gt hB) (Nat.card_le_card_of_injective _ hi)
  exact ⟨ha, hb⟩

private lemma twisted_annihilator_zero (B : AddSubgroup (Fin 2 → F))
    (hB : Nat.card F < Nat.card B) (σ : F ≃+* F)
    (a b : F) (h : ∀ w ∈ B, a * σ (w 0) + b * σ (w 1) = 0) : a = 0 ∧ b = 0 := by
  have hz := annihilator_zero B hB (σ.symm a) (σ.symm b) (fun w hw => by
    simpa only [map_add, map_mul, RingEquiv.symm_apply_apply, map_zero] using
      congrArg σ.symm (h w hw))
  exact ⟨σ.symm.injective (hz.1.trans (map_zero _).symm),
    σ.symm.injective (hz.2.trans (map_zero _).symm)⟩

private lemma semilinear_scalar_zero (B : AddSubgroup (Fin 2 → F))
    (hB : Nat.card F < Nat.card B) (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    (a b c d h : F)
    (h0 : ∀ w ∈ B, a * σ (w 0) + b * σ (w 1) = h * w 1)
    (h1 : ∀ w ∈ B, c * σ (w 0) + d * σ (w 1) = h * w 0) : h = 0 := by
  by_contra hh
  obtain ⟨t, ht⟩ : ∃ t, σ t ≠ t := by
    by_contra! hn
    apply hne
    ext x
    exact hn x
  have hdis (w : Fin 2 → F) (hw : w ∈ B) (htw : t • w ∈ B) : w = 0 := by
    have e0 := h0 w hw
    have e1 := h1 w hw
    have et0 := h0 (t • w) htw
    have et1 := h1 (t • w) htw
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at et0 et1
    have e (j : Fin 2) : (σ t - t) * h * w j = 0 := by
      fin_cases j
      · change (σ t - t) * h * w 0 = 0
        linear_combination et1 - σ t * e1
      · change (σ t - t) * h * w 1 = 0
        linear_combination et0 - σ t * e0
    funext j
    exact (mul_eq_zero.mp (e j)).resolve_left
      (mul_ne_zero (sub_ne_zero.mpr ht) hh)
  let f : B × B → (Fin 2 → F) := fun p => p.1.val + t • p.2.val
  have hi : Function.Injective f := by
    rintro ⟨x,y⟩ ⟨x',y'⟩ he
    have he' : t • (y.val - y'.val) = x'.val - x.val := by
      change x.val + t • y.val = x'.val + t • y'.val at he
      rw [smul_sub]
      exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using he)
    have hy : y.val - y'.val = 0 :=
      hdis _ (B.sub_mem y.property y'.property) (he' ▸ B.sub_mem x'.property x.property)
    have hy' : y = y' := Subtype.ext (sub_eq_zero.mp hy)
    subst y'
    have hx : x = x' := Subtype.ext (add_right_cancel he)
    exact Prod.ext hx rfl
  have hc := Nat.card_le_card_of_injective _ hi
  have hc' : Nat.card B * Nat.card B ≤ Nat.card F * Nat.card F := by
    simpa [Nat.card_prod, Nat.card_fun, pow_two] using hc
  nlinarith
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- The noncentral image, in the order (v,u). -/
private def directions (A : Subgroup (Sp F)) : AddSubgroup (Fin 2 → F) where
  carrier := {w | ∃ z, (pointRadicalElement (w 1) (w 0) z).val ∈ A}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro w w' ⟨z,hz⟩ ⟨z',hz'⟩
    refine ⟨z + z' + w 1 * w' 0 + w 0 * w' 1, ?_⟩
    have hm := A.mul_mem hz hz'
    have he := congrArg Subtype.val (pointRadicalElement_mul (w 1) (w 0) z (w' 1) (w' 0) z')
    exact he ▸ hm
  neg_mem' := by
    rintro w ⟨z,hz⟩
    exact ⟨z, by simpa only [Pi.neg_apply, CharTwo.neg_eq] using hz⟩

private lemma point_eq_coordinates (g : Sp F) (hg : g ∈ SymplecticConjugatePair.pointRadical) :
    (pointRadicalElement (g.val (.inl 1) (.inr 0)) (g.val (.inr 1) (.inr 0))
      (g.val (.inl 0) (.inr 0))).val = g := by
  obtain ⟨u,v,z,rfl⟩ := (mem_pointRadical_iff g).mp hg
  rfl

omit [Finite F] [Algebra (ZMod 2) F] in
/-- This is the existing point-vector homomorphism with its two coordinates swapped. -/
private lemma directions_pointRadicalVector (A : Subgroup (Sp F))
    (g : Theory.SpecificGroups.SymplecticFour.pointRadical (F := F))
    (hg : g.val.val ∈ A) :
    ![(pointRadicalVector g).toAdd 1, (pointRadicalVector g).toAdd 0] ∈ directions A := by
  refine ⟨g.val.val.val (.inl 0) (.inr 0), ?_⟩
  change (pointRadicalElement (g.val.val.val (.inl 1) (.inr 0))
    (g.val.val.val (.inr 1) (.inr 0)) (g.val.val.val (.inl 0) (.inr 0))).val ∈ A
  rw [← pointRadical_eq_element g.val g.property]
  exact hg

private def directionOf {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (g : A) : directions A :=
  ⟨![g.val.val (.inr 1) (.inr 0), g.val.val (.inl 1) (.inr 0)], by
    exact directions_pointRadicalVector A
      ⟨pointRadicalElement (g.val.val (.inl 1) (.inr 0)) (g.val.val (.inr 1) (.inr 0))
        (g.val.val (.inl 0) (.inr 0)), pointRadicalElement_mem _ _ _⟩ (by
        rw [point_eq_coordinates _ (hA g.property)]
        exact g.property)⟩

private lemma direction_and_center_injective {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) :
    Function.Injective (fun g : A => (directionOf hA g, g.val.val (.inl 0) (.inr 0))) := by
  intro g k he
  have hv := congrArg (fun p => p.1.val 0) he
  have hu := congrArg (fun p => p.1.val 1) he
  have hz := congrArg Prod.snd he
  dsimp only at hz
  apply Subtype.ext
  rw [← point_eq_coordinates g.val (hA g.property),
    ← point_eq_coordinates k.val (hA k.property)]
  change g.val.val (.inr 1) (.inr 0) = k.val.val (.inr 1) (.inr 0) at hv
  change g.val.val (.inl 1) (.inr 0) = k.val.val (.inl 1) (.inr 0) at hu
  rw [hu,hv,hz]

private lemma directions_card_gt {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hc : Nat.card F ^ 2 < Nat.card A) :
    Nat.card F < Nat.card (directions A) := by
  have hi := Nat.card_le_card_of_injective _ (direction_and_center_injective hA)
  rw [Nat.card_prod] at hi
  by_contra hn
  have hm := Nat.mul_le_mul_right (Nat.card F) (Nat.le_of_not_gt hn)
  nlinarith [hi]

private lemma exists_central {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hc : Nat.card F ^ 2 < Nat.card A) :
    ∃ z : F, z ≠ 0 ∧ (pointRadicalElement 0 0 z).val ∈ A := by
  by_contra! hn
  have hi : Function.Injective (fun g : A => (directionOf hA g).val) := by
    intro g k he
    obtain ⟨u,v,z,hg⟩ := (mem_pointRadical_iff _).mp (hA g.property)
    obtain ⟨u',v',z',hk⟩ := (mem_pointRadical_iff _).mp (hA k.property)
    have hu := congrFun he 1
    have hv := congrFun he 0
    change g.val.val (.inl 1) (.inr 0) = k.val.val (.inl 1) (.inr 0) at hu
    change g.val.val (.inr 1) (.inr 0) = k.val.val (.inr 1) (.inr 0) at hv
    rw [← hg, ← hk] at hu hv
    change u = u' at hu
    change v = v' at hv
    subst u' v'
    have hmem := A.mul_mem g.property k.property
    rw [← hg, ← hk] at hmem
    have hmul : (pointRadicalElement u v z).val * (pointRadicalElement u v z').val =
        (pointRadicalElement 0 0 (z+z')).val := by
      rw [← Subgroup.coe_mul, pointRadicalElement_mul]
      simp [CharTwo.add_self_eq_zero, mul_comm, add_assoc]
    rw [hmul] at hmem
    have hz : z + z' = 0 := by
      by_contra hz
      exact hn (z+z') hz hmem
    have hzz : z = z' := (CharTwo.add_eq_zero).mp hz
    apply Subtype.ext
    rw [← hg, ← hk, hzz]
  have hh := Nat.card_le_card_of_injective _ hi
  have hle : Nat.card A ≤ Nat.card F ^ 2 := by
    simpa [Nat.card_fun] using hh
  omega
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

private lemma fixed_matrix_zero (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hc : Nat.card F ^ 2 < Nat.card A) (X : Mat (F := F))
    (hfix : ∀ u v z, (pointRadicalElement u v z).val ∈ A →
      matrixAction σ (pointRadicalElement u v z).val X = X)
    (ha : X (.inl 0) (.inl 0) = 0)
    (hb : X (.inl 0) (.inl 1) = 0)
    (hd : X (.inl 0) (.inr 1) = 0) : X = 0 := by
  obtain ⟨z,hz,hzA⟩ := exists_central hA hc
  have hsz : σ z ≠ 0 := (map_ne_zero σ).mpr hz
  have H := hfix 0 0 z hzA
  have h22 : X (.inr 0) (.inr 0) = 0 := by
    have he : z * X (.inr 0) (.inr 0) = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two] using
        congrArg (fun M => M (.inl 0) (.inr 0)) H
    exact (mul_eq_zero.mp he).resolve_left hz
  have h21 : X (.inr 0) (.inl 1) = 0 := by
    have he : z * X (.inr 0) (.inl 1) = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two] using
        congrArg (fun M => M (.inl 0) (.inl 1)) H
    exact (mul_eq_zero.mp he).resolve_left hz
  have h23 : X (.inr 0) (.inr 1) = 0 := by
    have he : z * X (.inr 0) (.inr 1) = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two] using
        congrArg (fun M => M (.inl 0) (.inr 1)) H
    exact (mul_eq_zero.mp he).resolve_left hz
  have h12 : X (.inl 1) (.inr 0) = 0 := by
    have he : X (.inl 1) (.inr 0) * σ z = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, add_assoc] using
        congrArg (fun M => M (.inl 1) (.inl 0)) H
    exact (mul_eq_zero.mp he).resolve_right hsz
  have h32 : X (.inr 1) (.inr 0) = 0 := by
    have he : X (.inr 1) (.inr 0) * σ z = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, add_assoc] using
        congrArg (fun M => M (.inr 1) (.inl 0)) H
    exact (mul_eq_zero.mp he).resolve_right hsz
  have hB := directions_card_gt hA hc
  have e0 : ∀ w ∈ directions A,
      X (.inl 1) (.inl 1) * σ (w 0) + X (.inl 1) (.inr 1) * σ (w 1) =
      X (.inr 0) (.inl 0) * w 1 := by
    rintro w ⟨c,hc⟩
    have he := congrArg (fun M => M (.inl 1) (.inl 0)) (hfix (w 1) (w 0) c hc)
    have he' : w 1 * X (.inr 0) (.inl 0) +
        X (.inl 1) (.inl 1) * σ (w 0) + X (.inl 1) (.inr 1) * σ (w 1) = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, h12,h21,h22,h23, add_assoc] using he
    have hh := (CharTwo.add_eq_zero).mp (show
      w 1 * X (.inr 0) (.inl 0) +
        (X (.inl 1) (.inl 1) * σ (w 0) + X (.inl 1) (.inr 1) * σ (w 1)) = 0 by
      simpa only [add_assoc] using he')
    exact hh.symm.trans (mul_comm _ _)
  have e1 : ∀ w ∈ directions A,
      X (.inr 1) (.inl 1) * σ (w 0) + X (.inr 1) (.inr 1) * σ (w 1) =
      X (.inr 0) (.inl 0) * w 0 := by
    rintro w ⟨c,hc⟩
    have he := congrArg (fun M => M (.inr 1) (.inl 0)) (hfix (w 1) (w 0) c hc)
    have he' : w 0 * X (.inr 0) (.inl 0) +
        X (.inr 1) (.inl 1) * σ (w 0) + X (.inr 1) (.inr 1) * σ (w 1) = 0 := by
      simp [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, h32,h21,h22,h23, add_assoc] at he
      linear_combination he
    have hh := (CharTwo.add_eq_zero).mp (show
      w 0 * X (.inr 0) (.inl 0) +
        (X (.inr 1) (.inl 1) * σ (w 0) + X (.inr 1) (.inr 1) * σ (w 1)) = 0 by
      simpa only [add_assoc] using he')
    exact hh.symm.trans (mul_comm _ _)
  have h20 := semilinear_scalar_zero (directions A) hB σ hne _ _ _ _ _ e0 e1
  have h02 : X (.inl 0) (.inr 0) = 0 := by
    have he : X (.inl 0) (.inr 0) * σ z = 0 := by
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, h20,h22,add_assoc] using
        congrArg (fun M => M (.inl 0) (.inl 0)) H
    exact (mul_eq_zero.mp he).resolve_right hsz
  have h11_13 := twisted_annihilator_zero (directions A) hB σ _ _
    (fun w hw => by simpa [h20] using e0 w hw)
  have h31_33 := twisted_annihilator_zero (directions A) hB σ _ _
    (fun w hw => by simpa [h20] using e1 w hw)
  have h10_30 := annihilator_zero (directions A) hB
    (X (.inl 1) (.inl 0)) (X (.inr 1) (.inl 0)) (by
      rintro w ⟨c,hc⟩
      have he := congrArg (fun M => M (.inl 0) (.inl 0)) (hfix (w 1) (w 0) c hc)
      simpa [matrixAction, pointRadicalElement, pointRadicalMatrix, Matrix.mul_apply,
        Fintype.sum_sum_type, Fin.sum_univ_two, ha,hb,hd,h20,h02,h12,h21,h22,h23,h32,
        h11_13.1,h11_13.2,h31_33.1,h31_33.2,mul_comm] using he)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ha,hb,hd,h20,h02,h12,h21,h22,h23,h32,
      h11_13.1,h11_13.2,h31_33.1,h31_33.2,h10_30.1,h10_30.2]
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality.PointSubgroupBound

@[expose] public section

namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- Three literal matrix entries of a fixed tensor. -/
noncomputable def pointFixedCoordinates (σ : F ≃+* F) (A : Subgroup (Sp F)) :
    Representation.invariants ((twistedTensor σ).comp A.subtype) →ₗ[F] (Fin 3 → F) where
  toFun w := ![coordinates w.val (.inl 0) (.inl 0),
    coordinates w.val (.inl 0) (.inl 1), coordinates w.val (.inl 0) (.inr 1)]
  map_add' x y := by ext i; fin_cases i <;> simp [map_add]
  map_smul' c x := by ext i; fin_cases i <;> simp [map_smul]

/-- Large point-radical subgroups have at most three independent fixed coordinates. -/
theorem pointFixedCoordinates_injective (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hc : Nat.card F ^ 2 < Nat.card A) :
    Function.Injective (pointFixedCoordinates σ A) := by
  suffices hz : ∀ w, pointFixedCoordinates σ A w = 0 → w = 0 by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, hxy, sub_self]
  intro w hw
  apply Subtype.ext
  apply coordinates.injective
  change coordinates w.val = coordinates 0
  rw [map_zero]
  apply PointSubgroupBound.fixed_matrix_zero σ hne hA hc (coordinates w.val)
  · intro u v z hg
    rw [← coordinates_action]
    exact congrArg coordinates (w.property ⟨_, hg⟩)
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

/-- The sufficient point-radical estimate for K.3.4.2. It asserts a bound,
without the false equality with the full radical's invariant line. -/
theorem point_subgroup_tensor_fixed_finrank_le (σ : F ≃+* F)
    (hne : σ ≠ RingEquiv.refl F) {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hc : Nat.card F ^ 2 < Nat.card A) :
    Module.finrank F (Representation.invariants ((twistedTensor σ).comp A.subtype)) ≤ 3 := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (pointFixedCoordinates_injective σ hne hA hc)
  simpa using h

/-- Rank form of the corrected estimate; no extra invariance or root hypothesis. -/
theorem point_subgroup_tensor_fixed_finrank_le_of_rank {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (σ : F ≃+* F) (hne : σ ≠ RingEquiv.refl F)
    {A : Subgroup (Sp F)} (hA : A ≤ SymplecticConjugatePair.pointRadical)
    (hr : 2 * n < rank A) :
    Module.finrank F (Representation.invariants ((twistedTensor σ).comp A.subtype)) ≤ 3 := by
  apply point_subgroup_tensor_fixed_finrank_le σ hne hA
  by_contra! hn
  have hl := Nat.log_mono_right (b := 2) hn
  rw [hF, ← pow_mul, Nat.log_pow (by decide : 1 < 2)] at hl
  change rank A ≤ n * 2 at hl
  omega
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Equality

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {D V F : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
  [ρ.IsIrreducible] [Field F] [Algebra (SchurField ρ) F]

/-- Actual scalar descent of the corrected point-subgroup bound. -/
theorem TensorIdentification.point_subgroup_fixed_finrank_le {s : ℕ}
    (h : TensorIdentification ρ F s) {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hr : 4*s < rank A) :
    Module.finrank (ZMod 2) (fixedSpace ρ (A.map h.groupEquiv.symm.toMonoidHom)) ≤ 3*s := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hne : h.sigma.toRingEquiv ≠ RingEquiv.refl F := by
    intro he
    apply h.sigma_ne
    ext t
    exact DFunLike.congr_fun he t
  rw [h.fixed_finrank ρ]
  have hf := TensorGeometry.Equality.point_subgroup_tensor_fixed_finrank_le_of_rank
    h.field_card h.sigma.toRingEquiv hne hA (by omega)
  simpa [Nat.mul_comm] using Nat.mul_le_mul_left s hf

/-- The point branch has codimension at least 13s in the original binary module. -/
theorem TensorIdentification.point_subgroup_fixedCodim_ge {s : ℕ}
    (h : TensorIdentification ρ F s) {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hr : 4*s < rank A) :
    13*s ≤ fixedCodim ρ (A.map h.groupEquiv.symm.toMonoidHom) := by
  have hf := h.point_subgroup_fixed_finrank_le ρ hA hr
  have hd := fixedCodim_add_finrank ρ (A.map h.groupEquiv.symm.toMonoidHom)
  rw [h.binary_finrank] at hd
  omega

/-- K.3.4.2's point actor is excluded by its literal small-ratio inequality. -/
theorem TensorIdentification.point_subgroup_not_small {s : ℕ}
    (h : TensorIdentification ρ F s) (hs : 0 < s) {A : Subgroup (Sp F)}
    (hA : A ≤ SymplecticConjugatePair.pointRadical) (hr : 4*s < rank A) :
    2 * rank A < fixedCodim ρ (A.map h.groupEquiv.symm.toMonoidHom) := by
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField ρ) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (SchurField ρ)).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (SchurField ρ) F).injective 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hA) (Subgroup.inclusion_injective hA)
  have hrank := Nat.log_mono_right (b := 2) hcard
  change rank A ≤ Representation.BinaryOffender.rank SymplecticConjugatePair.pointRadical at hrank
  rw [rank_pointRadical h.field_card] at hrank
  have hd := h.point_subgroup_fixedCodim_ge ρ hA hr
  omega
end CFSG.Quasithin.ChapterK.Symplectic

namespace CFSG.Quasithin.ChapterK.Symplectic
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- Component-subgroup transport for the point exclusion, with precisely the
same model map used by the plane equality owner. -/
theorem tensor_point_actor_not_small {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    {A : Subgroup G} (hAL : A ≤ L)
    (hpoint : (A.subgroupOf L).map h.groupEquiv.toMonoidHom ≤
      SymplecticConjugatePair.pointRadical)
    (hr : 4*s < rank A) : 2 * rank A < fixedCodim ρ A := by
  let B := (A.subgroupOf L).map h.groupEquiv.toMonoidHom
  have hback : B.map h.groupEquiv.symm.toMonoidHom = A.subgroupOf L := by
    simp [B, Subgroup.map_map]
  have hBr : rank B = rank A := by
    dsimp [B]
    rw [rank_map_injective _ h.groupEquiv.injective, rank_subgroupOf hAL]
  have hc := h.point_subgroup_not_small (ρ.comp L.subtype) hs hpoint (by rwa [hBr])
  rwa [hback, fixedCodim_subgroupOf ρ hAL, hBr] at hc

/-- A source actor of ratio at most two cannot lie in the point radical. -/
theorem tensor_point_actor_exclusion {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    {A : Subgroup G} (hAL : A ≤ L) (hr : 4*s < rank A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    ¬ (A.subgroupOf L).map h.groupEquiv.toMonoidHom ≤
      SymplecticConjugatePair.pointRadical := by
  intro hpoint
  exact (not_le_of_gt (tensor_point_actor_not_small ρ L h hs hAL hpoint hr)) hsmall
end CFSG.Quasithin.ChapterK.Symplectic

