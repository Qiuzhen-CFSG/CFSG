module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawClassicalCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2Local
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalLifts

/-! Literal residual comparison and linear-three residual data. The full
normalizer preimage and the preimage inside the original perfect subgroup
have the same solvable residual. All maps and their kernels are retained. -/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.RawClassicalResidual
variable {X D : Type*} [Group X] [Finite X] [Group D]

/-- A perfect normal subgroup with a two-group supplement contains the
residual of every full preimage of a subgroup of its actual image. -/
theorem preimage_residual_eq
    (K R : Subgroup X) [K.Normal] [Group.IsPerfect K]
    (hR : IsPGroup 2 R) (hgen : K ⊔ R = ⊤)
    (q : X →* D) (I : Subgroup D) (f : K →* I)
    (hval : ∀ x : K, (f x : D) = q x) (P : Subgroup I) :
    (solvableResidual ((P.map I.subtype).comap q)).map
      ((P.map I.subtype).comap q).subtype =
    ((solvableResidual (P.comap f)).map (P.comap f).subtype).map K.subtype := by
  let B := (P.map I.subtype).comap q
  let C := (P.comap f).map K.subtype
  have hCB : C ≤ B := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨f x,hx,hval x⟩
  have hRK : (solvableResidual B).map B.subtype ≤ K :=
    (map_solvableResidual_le B.subtype).trans
      (residuals_of_perfect_normal_sup_twoGroup K R hR hgen).2.le
  have hRC : (solvableResidual B).map B.subtype ≤ C := by
    intro x hx
    have hxK := hRK hx
    refine ⟨⟨x,hxK⟩,?_,rfl⟩
    have hxB : x ∈ B := (map_subtype_le _) hx
    obtain ⟨z,hz,he⟩ := hxB
    change f ⟨x,hxK⟩ ∈ P
    have hh : f ⟨x,hxK⟩ = z := Subtype.ext ((hval _).trans he.symm)
    rwa [hh]
  rw [map_embedded_solvableResidual_of_hom]
  change (solvableResidual B).map B.subtype = (solvableResidual C).map C.subtype
  apply le_antisymm
  · let : Group.IsPerfect ((solvableResidual B).map B.subtype) := Group.IsPerfect.map B.subtype
    exact le_map_solvableResidual_of_isPerfect _ C hRC
  · exact map_solvableResidual_mono hCB

variable {G : Type*} [Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The native linear-three residuals retain their exact SL2 core and
characteristic-two Fitting structure after a surjective two-kernel lift. -/
theorem linear_data (K : Subgroup G) (f : K →* SL(3,F))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) (hF : 4 ≤ Nat.card F)
    (P : Subgroup SL(3,F))
    (hP : P ∈ ({Matrix.PSL3.LinearThree.pointParabolicSL F,
      Matrix.PSL3.LinearThree.lineParabolicSL F} : Set (Subgroup SL(3,F)))) :
    let B := (P.comap f).map K.subtype
    let A := (solvableResidual B).map B.subtype
    generalizedFitting A = pCore 2 A ∧ Nonempty ((A ⧸ pCore 2 A) ≃* SL(2,F)) := by
  intro B A
  let er : solvableResidual (P.comap f) ≃* A :=
    (((P.comap f).equivMapOfInjective K.subtype K.subtype_injective).solvableResidualEquiv).trans
      ((solvableResidual B).equivMapOfInjective B.subtype B.subtype_injective)
  have hm : ∃ J : Subgroup SL(3,F),
      (solvableResidual P).map P.subtype = J ∧ generalizedFitting J = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* SL(2,F)) := by
    rcases hP with rfl | hP
    · exact ⟨Matrix.PSL3.LinearThree.pointLocalSL F,
        Matrix.PSL3.LinearThree.pointParabolicSL_residual F hF,
        Matrix.PSL3.LinearThree.pointLocalSL_generalizedFitting_eq_twoCore F,
        ⟨Matrix.PSL3.LinearThree.pointLocalSLCoreQuotientEquiv F⟩⟩
    · have he : P = Matrix.PSL3.LinearThree.lineParabolicSL F := hP
      subst P
      exact ⟨Matrix.PSL3.LinearThree.lineLocalSL F,
        Matrix.PSL3.LinearThree.lineParabolicSL_residual F hF,
        Matrix.PSL3.LinearThree.lineLocalSL_generalizedFitting_eq_twoCore F,
        ⟨Matrix.PSL3.LinearThree.lineLocalSLCoreQuotientEquiv F⟩⟩
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
theorem linear_nonshort
    (K R : Subgroup G) [Group.IsPerfect K]
    (hnK : R ≤ normalizer (K : Set G)) (hR : IsPGroup 2 R)
    (W : Subgroup (K ⊔ R : Subgroup G)) [W.Normal] [IsElementaryAbelian 2 W]
    (I : Subgroup ((K ⊔ R : Subgroup G) ⧸ centralizer (W : Set (K ⊔ R : Subgroup G))))
    (f : K →* I)
    (hval : ∀ x : K, (f x : (K ⊔ R : Subgroup G) ⧸ centralizer (W : Set (K ⊔ R : Subgroup G))) =
      QuotientGroup.mk' _ (inclusion le_sup_left x))
    (e : I ≃* SL(3,F)) (hF : 4 ≤ Nat.card F)
    (P : Subgroup SL(3,F))
    (hP : P ∈ ({Matrix.PSL3.LinearThree.pointParabolicSL F,
      Matrix.PSL3.LinearThree.lineParabolicSL F} : Set (Subgroup SL(3,F)))) :
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
  have hns := ClassicalResidualAction.linear_three W q (QuotientGroup.mk'_surjective C)
    (QuotientGroup.ker_mk' C) j (I.subtype_injective.comp e.symm.injective) hF
  have hn : ¬ChapterC.IsShort (solvableResidual ((P.map j).comap q)) := by
    rcases hP with rfl | hP
    · exact hns.1
    · have he : P = Matrix.PSL3.LinearThree.lineParabolicSL F := hP
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
