module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherLinearLifts

/-!
# Literal symplectic residuals of the raw normalizer action

Both native symplectic parabolics retain their exact SL2 core quotient and
characteristic-two generalized Fitting subgroup through the actual two-kernel
lift. Nonshortness is measured on the original elementary module with its
full centralizer quotient, then transported to the same residual in K.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.RawClassicalResidual
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The native symplectic-four residuals retain their exact SL2 core and
characteristic-two Fitting structure after a surjective two-kernel lift. -/
theorem symplectic_data (K : Subgroup G) (f : K →* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hP : P ∈ ({pointParabolic,
      planeParabolic} : Set (Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)))) :
    let B := (P.comap f).map K.subtype
    let A := (solvableResidual B).map B.subtype
    generalizedFitting A = pCore 2 A ∧ Nonempty ((A ⧸ pCore 2 A) ≃* SL(2,F)) := by
  intro B A
  have hgt : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = 2^1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn)
  let er : solvableResidual (P.comap f) ≃* A :=
    (((P.comap f).equivMapOfInjective K.subtype K.subtype_injective).solvableResidualEquiv).trans
      ((solvableResidual B).equivMapOfInjective B.subtype B.subtype_injective)
  have hm : ∃ J : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F),
      (solvableResidual P).map P.subtype = J ∧ generalizedFitting J = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* SL(2,F)) := by
    rcases hP with rfl | hP
    · exact ⟨pointLocal,
        pointParabolic_solvableResidual_eq hF hn,
        (pointNaturalExtension hF hn).generalizedFitting_eq hgt,
        ⟨pointLocalCoreQuotientEquiv hF hn⟩⟩
    · have he : P = planeParabolic := hP
      subst P
      exact ⟨planeLocal,
        planeParabolic_solvableResidual_eq hF hn,
        (planeNaturalExtension hF hn).generalizedFitting_eq hgt,
        ⟨planeLocalCoreQuotientEquiv hF hn⟩⟩
  obtain ⟨J,hJ,hfit,⟨eq⟩⟩ := hm
  let em : solvableResidual P ≃* J :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hJ)
  have hm : generalizedFitting (solvableResidual P) = pCore 2 (solvableResidual P) := by
    rw [←map_generalizedFitting_equiv em.symm,←pCore_map_iso 2 em.symm,hfit]
  have hr := f.preimageResidual_generalizedFitting P hf hk hm
  refine ⟨?_,⟨?_⟩⟩
  · rw [←map_generalizedFitting_equiv er,←pCore_map_iso 2 er,hr]
  · exact (QuotientGroup.congr _ _ er.symm (pCore_map_iso 2 er.symm)).trans
      ((f.preimageResidualCoreEquiv P hf hk).trans
        ((QuotientGroup.congr _ _ em (pCore_map_iso 2 em)).trans eq))

/-- Nonshortness is measured on the original elementary module, including
the full centralizer kernel, then transported to the residual inside K. -/
theorem symplectic_nonshort
    (K R : Subgroup G) [Group.IsPerfect K]
    (hnK : R ≤ normalizer (K : Set G)) (hR : IsPGroup 2 R)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (I : Subgroup ((K ⊔ R : Subgroup G) ⧸ centralizer (W : Set (K ⊔ R : Subgroup G))))
    (f : K →* I)
    (hval : ∀ x : K, (f x : (K ⊔ R : Subgroup G) ⧸ centralizer (W : Set (K ⊔ R : Subgroup G))) =
      QuotientGroup.mk' _ (inclusion le_sup_left x))
    (e : I ≃* Theory.SpecificGroups.SymplecticFour.Sp F) {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (P : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hP : P ∈ ({pointParabolic,
      planeParabolic} : Set (Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)))) :
    ¬ChapterC.IsShort (solvableResidual ((P.comap (e.toMonoidHom.comp f)).map K.subtype)) := by
  let H := K ⊔ R
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let K0 := K.subgroupOf H
  let R0 := R.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hnK)
  let i : K0 ≃* K := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect K0 := Group.IsPerfect.ofSurjective (f := i.symm.toMonoidHom) i.symm.surjective
  have hgen : K0 ⊔ R0 = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      map_subgroupOf_eq_of_le (show R ≤ H from le_sup_right),←MonoidHom.range_eq_map,range_subtype]
  let j := I.subtype.comp e.symm.toMonoidHom
  have hns := ClassicalResidualAction.symplectic_four W q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) j (I.subtype_injective.comp e.symm.injective) hF hn
  have hn : ¬ChapterC.IsShort (solvableResidual ((P.map j).comap q)) := by
    rcases hP with rfl | hP
    · exact hns.1
    · have he : P = planeParabolic := hP
      subst P
      exact hns.2
  let B := ((P.map e.symm.toMonoidHom).map I.subtype).comap q
  let A := (P.comap (e.toMonoidHom.comp f)).map K.subtype
  have hB : B = (P.map j).comap q := by dsimp only [B,j]; rw [map_map]
  have hC : (((P.map e.symm.toMonoidHom).comap (f.comp i.toMonoidHom)).map K0.subtype).map H.subtype = A := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨i z,?_,rfl⟩
      obtain ⟨a,ha,he⟩ := hz
      change e.symm a = f (i z) at he
      change e (f (i z)) ∈ P
      rw [←he,e.apply_symm_apply]
      exact ha
    · rintro ⟨y,hy,rfl⟩
      refine ⟨K0.subtype (i.symm y),?_,rfl⟩
      refine ⟨i.symm y,?_,rfl⟩
      refine ⟨e (f y),hy,?_⟩
      change e.symm (e (f y)) = f (i (i.symm y))
      rw [i.apply_symm_apply,e.symm_apply_apply]
  have he := congrArg (Subgroup.map H.subtype)
    (preimage_residual_eq K0 R0 hR.comap_subtype hgen q I (f.comp i.toMonoidHom)
      (fun x => hval (i x)) (P.map e.symm.toMonoidHom))
  rw [map_embedded_solvableResidual_of_hom,map_embedded_solvableResidual_of_hom,
    map_embedded_solvableResidual_of_hom,hC] at he
  let eb := (B.equivMapOfInjective H.subtype H.subtype_injective).solvableResidualEquiv
  let er := ((solvableResidual A).equivMapOfInjective A.subtype A.subtype_injective).trans
    ((MulEquiv.subgroupCongr he.symm).trans
      ((solvableResidual (B.map H.subtype)).equivMapOfInjective
        (B.map H.subtype).subtype (B.map H.subtype).subtype_injective).symm)
  intro hs
  apply hn
  rw [←hB]
  exact (hs.of_mulEquiv er).of_mulEquiv eb.symm

end CFSG.Quasithin.Chapter15.Section01.RawClassicalResidual
