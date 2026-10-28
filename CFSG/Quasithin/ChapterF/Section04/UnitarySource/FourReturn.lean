module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongClass
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourOrbits
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourShortMarked
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.LongPlacement
import all CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourLongClass
import all CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourOrbits

/-!
# Synchronized involution placement and the native long-root class

The same plane and point endpoint conjugations place an involution in the
plane two-core in both realizations of the marked amalgam. Independently,
an automorphism of the plane residual preserves the native long-root
class: its image is a nonzero Hermitian vector fixed by a Sylow subgroup,
so its determinant vanishes and SL₂ normalization gives the long root.
These statements let ambient core fusion detect long-root returns through
the actual residual without assuming an ambient recognition theorem.

Source: Aschbacher–Smith F.4.35 and F.4.42, printed pp.292 and295.
-/

open Matrix Subgroup Theory.GroupTheory
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitarySource.FourReturn
open GreenBook.LieModels.UnitaryFour
open SourceNormalizer.FourShortRoot
variable (m : ℕ) (hm : 1 ≤ m) [NeZero m]
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "B" => localFactor F (form F σ hσ)

private theorem long_element :
    FourOrbits.element m hm (SourceNormalizer.FourOrbits.representative m 0) =
      projection m hm (longLocal F σ hσ).val := by
  rw [FourOrbits.element_eq]
  apply congrArg (projection m hm)
  apply congrArg (unipotentSU F σ hσ)
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeHermitianEquiv,SourceNormalizer.FourOrbits.representative,
      FiniteModel.coordinates_symm_val,longParameter]

/-- An arbitrary residual automorphism preserves the native long-root class. -/
theorem automorphism_long (a : MulAut B) :
    IsConj (projection m hm (longLocal F σ hσ).val)
      (projection m hm (a (longLocal F σ hσ)).val) := by
  have hrad : a (longLocal F σ hσ) ∈ radical F σ hσ := by
    rw [radical_eq_twoCore,←pCore_map_iso 2 a]
    exact mem_map_of_mem a.toMonoidHom (by
      rw [←radical_eq_twoCore]
      exact (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).property)
  obtain ⟨X,hX⟩ := (radicalEquiv F σ hσ).surjective ⟨a (longLocal F σ hσ),hrad⟩
  have hXe : radicalHom F σ hσ X = a (longLocal F σ hσ) := congrArg Subtype.val hX
  have hne : X.toAdd ≠ 0 := by
    intro he
    have ha : a (longLocal F σ hσ) = 1 := by rw [←hXe,show X = 1 from he,map_one]
    have hz : longLocal F σ hσ = 1 := a.injective (ha.trans (map_one a).symm)
    have ho := longMark_order F σ hσ
    have hh : longMark F σ hσ = 1 := Subtype.ext hz
    rw [hh,orderOf_one] at ho
    contradiction
  obtain ⟨P,hP⟩ := ((FourLongClass.longClass_iff m hm (longMark F σ hσ)).mp (IsConj.refl _)).2.2
  have hzmark : (longMark F σ hσ).val = longLocal F σ hσ := rfl
  rw [hzmark] at hP
  have hfix : ∃ R : Sylow 2 B,
      (R : Subgroup B) ≤ centralizer ({radicalHom F σ hσ X} : Set B) := by
    refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
    rintro _ ⟨b,hb,rfl⟩
    rw [hXe]
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg a (mem_centralizer_singleton_iff.mp (hP hb))
    change a b * a (longLocal F σ hσ) = a (longLocal F σ hσ) * a b
    exact (map_mul a _ _).symm.trans (he.trans (map_mul a _ _))
  have hdet := (FourLongClass.singular_iff_local_sylow m hm X.toAdd).mpr hfix
  let Y := planeHermitianEquiv m X.toAdd
  have hY : Y ≠ 0 := fun he => hne ((planeHermitianEquiv m).injective (he.trans (map_zero _).symm))
  have hf : FiniteModel.form m Y = 0 := by
    apply Subtype.ext
    change (X.toAdd.val.map (planeFieldEquiv m)).det = 0
    simpa only [Matrix.det_fin_two,Matrix.map_apply,map_sub,map_mul,map_zero] using
      congrArg (planeFieldEquiv m) hdet
  obtain ⟨g,_,hg⟩ := FourOrbits.element_normalize m hm Y hY
  rw [hf,long_element] at hg
  have he : FourOrbits.element m hm Y = projection m hm (a (longLocal F σ hσ)).val := by
    rw [FourOrbits.element_eq]
    change projection m hm (unipotentSU F σ hσ ((planeHermitianEquiv m).symm
      (planeHermitianEquiv m X.toAdd))) = _
    exact (congrArg (fun X => projection m hm (unipotentSU F σ hσ X))
      ((planeHermitianEquiv m).symm_apply_apply X.toAdd)).trans
        (congrArg (fun b : B => projection m hm b.val) hXe)
  rw [he] at hg
  exact (isConj_iff.mpr ⟨g,hg⟩).symm


variable {G : Type*} [Group G]

omit [NeZero m] in
/-- Place an involution in the source plane core by the same two endpoint
conjugations in both ambient groups. -/
theorem synchronized_involution_placement (P R : Subgroup G)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P (P ⊓ R) R inf_le_left inf_le_right)
      (amalgam m hm).reverse)
    (x : P) (hx : x^2 = 1) :
    ∃ y : P, y ∈ pCore 2 P ∧ IsConj x.val y.val ∧
      IsConj (e.left x).val (e.left y).val := by
  let S := (projectiveSylow m hm).subtype (projectiveSylow_le_parabolics m hm).2
  have hp : IsPGroup 2 (zpowers (e.left x)) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_one,←map_pow,hx,map_one])
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨r,hr⟩ := MulAction.exists_smul_eq (planeParabolic m hm) Q S
  have hs : r * e.left x * r⁻¹ ∈ (S : Subgroup _) := by
    rw [←hr]
    exact ⟨e.left x,hQ (mem_zpowers _),rfl⟩
  let b : overlap m hm := ⟨(r * e.left x * r⁻¹).val,upperProjective_le_overlap m hm hs⟩
  have hb2 : b.val^2 = 1 := by
    change ((r * e.left x * r⁻¹)^2).val = 1
    have hh : (e.left x)^2 = 1 := by rw [←map_pow,hx,map_one]
    simpa only [map_pow,map_one,MulAut.conj_apply,Subgroup.coe_one] using
      congrArg (fun u : planeParabolic m hm => u.val) (congrArg (MulAut.conj r) hh)
  obtain ⟨k,hk⟩ := FourPlacement.projective_sylow_involution_placement m hm b.val hs hb2
  let v := k.val * b.val * k.val⁻¹
  have hvP : v ∈ pointParabolic m hm :=
    (pointParabolic m hm).mul_mem ((pointParabolic m hm).mul_mem k.property
      (((exact_overlap m hm).ge b.property).1)) ((pointParabolic m hm).inv_mem k.property)
  have hvR : v ∈ planeParabolic m hm :=
    pCoreIn_le 2 _ (FourPlacement.planeCore_le_twoCore m hm hk)
  let c : overlap m hm := ⟨v,(exact_overlap m hm).le ⟨hvP,hvR⟩⟩
  let b₀ := e.middle.symm b
  let c₀ := e.middle.symm c
  let r₀ := e.left.symm r
  let k₀ := e.right.symm k
  let y : P := ⟨c₀.val,c₀.property.1⟩
  have hbL : (e.left ⟨b₀.val,b₀.property.1⟩).val = b.val := by
    have hh := congrArg Subtype.val (e.left_commutes b₀)
    change (e.left ⟨b₀.val,b₀.property.1⟩).val = (e.middle b₀).val at hh
    rwa [e.middle.apply_symm_apply] at hh
  have hcL : (e.left y).val = c.val := by
    have hh := congrArg Subtype.val (e.left_commutes c₀)
    change (e.left y).val = (e.middle c₀).val at hh
    rwa [e.middle.apply_symm_apply] at hh
  have hbR : (e.right ⟨b₀.val,b₀.property.2⟩).val = b.val := by
    have hh := congrArg Subtype.val (e.right_commutes b₀)
    change (e.right ⟨b₀.val,b₀.property.2⟩).val = (e.middle b₀).val at hh
    rwa [e.middle.apply_symm_apply] at hh
  have hcR : (e.right ⟨c₀.val,c₀.property.2⟩).val = c.val := by
    have hh := congrArg Subtype.val (e.right_commutes c₀)
    change (e.right ⟨c₀.val,c₀.property.2⟩).val = (e.middle c₀).val at hh
    rwa [e.middle.apply_symm_apply] at hh
  have hr₀ : r₀.val*x.val*r₀.val⁻¹ = b₀.val := by
    have he : r₀*x*r₀⁻¹ = (⟨b₀.val,b₀.property.1⟩ : P) := by
      apply e.left.injective
      apply Subtype.ext
      simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
      rw [show e.left r₀ = r from e.left.apply_symm_apply _,hbL]
      rfl
    exact congrArg Subtype.val he
  have hk₀ : k₀.val*b₀.val*k₀.val⁻¹ = c₀.val := by
    have he : k₀ * (⟨b₀.val,b₀.property.2⟩ : R) * k₀⁻¹ = ⟨c₀.val,c₀.property.2⟩ := by
      apply e.right.injective
      apply Subtype.ext
      simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]
      rw [show e.right k₀ = k from e.right.apply_symm_apply _,hbR,hcR]
    exact congrArg Subtype.val he
  refine ⟨y,?_,isConj_iff.mpr ⟨k₀.val*r₀.val,?_⟩,isConj_iff.mpr ⟨k.val*r.val,?_⟩⟩
  · have hn : e.left y ∈ pCore 2 (planeParabolic m hm) := by
      apply (mem_map_iff_mem (planeParabolic m hm).subtype_injective).mp
      change (e.left y).val ∈ (planeParabolic m hm).pCoreIn 2
      rw [hcL]
      exact FourPlacement.planeCore_le_twoCore m hm hk
    rw [←pCore_map_iso 2 e.left] at hn
    exact (mem_map_iff_mem e.left.injective).mp hn
  · calc
      _ = k₀.val*(r₀.val*x.val*r₀.val⁻¹)*k₀.val⁻¹ := by group
      _ = y.val := by rw [hr₀,hk₀]
  · rw [hcL]
    change (k.val*r.val)*(e.left x).val*(k.val*r.val)⁻¹ =
      k.val*(r.val*(e.left x).val*r.val⁻¹)*k.val⁻¹
    group

end CFSG.Quasithin.ChapterF.UnitarySource.FourReturn
