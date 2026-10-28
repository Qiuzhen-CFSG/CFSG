module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedIsotropicAction
public import CFSG.Quasithin.ChapterG.Section12.RecognitionTransitive
public import CFSG.Quasithin.ChapterG.Section12.RecognitionQuadraticResidual
public import Theory.LinearAlgebra.BinaryReflectionCenter
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticFourModel
public import Theory.SpecificGroups.AlternatingSix.PerfectSubgroups
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedCentralKernelNondegenerateSymplecticHigherModel
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Recognition of the original nondegenerate exchanged constituent

The original hyperplane transvection action supplies the genuine G.12
hypotheses for the literal image of HY on I, where H is the normal component
orbit and Y is its original elementary actor stabilizer. The H-image is
perfect and relatively normal; the two-group supplement identifies it with
the generated image's embedded solvable residual.

In degree at least six, the proved transitive and nontransitive G.12
recognition theorems identify that residual with the full symplectic or
orthogonal residual on the same form. In degree four, the actual embedding
in Sp4(2) and perfect-subgroup recognition give its A6 residual or an A5
subgroup. These images are centerless; faithful ambient irreducibility then
kills the center of the original H, without assuming constituent faithfulness.

The final original-flag application retains both fixed-point clauses,
component exchange, the marked point, original quotient and actor, and every
earlier source premise. It introduces no recognition hypothesis. Exclusion
of these nondegenerate models, the marked action catalogue and guarded
same-G,T assembly remain outstanding. MixedSizeInput is still independent.

The image and hyperplane calculations adapt the checked Section03
ExchangedCentralSource arguments to this rank-three flag, without importing
its rank-two or Theorem E hypotheses.
Source: Aschbacher--Smith G.10.15, G.11.6 and G.12.1/10/12, printed
pp.362--366,370--375; original 14.4.2 and 14.4.14, pp.1006--1012,
refs/quasithin.pdf.
-/

@[expose] public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerate
variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
  (hn : ¬ Group.IsSolvable D) {C : Subgroup D} (hC : IsComponent D C)
  {I : Submodule (ZMod 2) U}
  (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I)

abbrev constituentLinearAction (ρ : Representation (ZMod 2) D U)
    (C X : Subgroup D) (I : Submodule (ZMod 2) U)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) : (componentOrbit C ⊤) →* (I ≃ₗ[ZMod 2] I) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    (invariantSubspace ρ (componentOrbit C ⊤) I
      hI.invariant).toRepresentation.asGroupHom

abbrev constituentStabilizer (ρ : Representation (ZMod 2) D U)
    (X : Subgroup D) (I : Submodule (ZMod 2) U) :=
  (subspaceStabilizer ρ I).subgroupOf X

/-- The literal action of N_X(I) on I. -/
def constituentStabilizerAction (ρ : Representation (ZMod 2) D U)
    (X : Subgroup D) (I : Submodule (ZMod 2) U) : constituentStabilizer ρ X I →*
    (I ≃ₗ[ZMod 2] I) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    ((stabilizerRepresentation ρ I).asGroupHom.comp
      { toFun := fun y => ⟨((y : X) : D), y.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl })

abbrev constituentGeneratedImage (ρ : Representation (ZMod 2) D U)
    (C X : Subgroup D) (I : Submodule (ZMod 2) U)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) : Subgroup (I ≃ₗ[ZMod 2] I) :=
  (constituentLinearAction ρ C X I hI).range ⊔
    (constituentStabilizerAction ρ X I).range


include h hn hI in
theorem constituentImage_irreducible :
    ChapterG.Section12.Irreducible (constituentLinearAction ρ C X I hI).range := by
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  intro U hU
  let R := invariantSubspace ρ (componentOrbit C ⊤) I hI.invariant
  let J : Subrepresentation R.toRepresentation := ⟨U, fun a w hw =>
    hU _ ⟨a,rfl⟩ w hw⟩
  rcases (hI.isIrrPlus.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) (componentOrbit C ⊤)).eq_bot_or_eq_top J with hb | ht
  · exact Or.inl (congrArg Subrepresentation.toSubmodule hb)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule ht)

omit [FiniteDimensional (ZMod 2) U] in
include h hI in
theorem constituentGeneratedImage_preserves :
    (constituentGeneratedImage ρ C X I hI) ≤ ChapterG.Section12.formStabilizer (B.restrict I) := by
  apply sup_le
  · rintro _ ⟨a,rfl⟩ u w
    exact h.preserves a u w
  · rintro _ ⟨a,rfl⟩ u w
    exact h.preserves ((a : X) : D) u w

include h hn hC hI in
/-- The same nondegenerate constituent, with its literal H and Y images,
meets G.12.1's hypotheses. No classification alternative is assumed. -/
theorem nondegenerate_classification_inputs
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (haxis : ¬ I ≤ (B v).ker)
    (hnd : (B.restrict I).Nondegenerate) :
    ∃ u i : I, ChapterG.Section12.ClassificationHypotheses
      (constituentGeneratedImage ρ C X I hI) (B.restrict I) u i := by
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  let : Group.IsPerfect (componentOrbit C ⊤) := hC.orbit_isPerfect ⊤
  obtain ⟨x,hx,hop,hdis,hindex,i,hi0,hvi,hiW,hcenter⟩ := hgeo
  let axis := I ⊓ (B v).ker
  let W : Submodule (ZMod 2) I := ((B v).comp I.subtype).ker
  let j : W ≃ₗ[ZMod 2] axis :=
    { toFun := fun w => ⟨w, w.val.property, w.property⟩
      invFun := fun w => ⟨⟨w,w.property.1⟩,w.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let iw : W := j.symm i
  let Q := (constituentStabilizerAction ρ X I).range
  have hfull : BinaryTransvection.FullCenterAction Q.subtype W iw := by
    refine ⟨?_,?_,?_,?_⟩
    · intro hz
      exact hi0 (congrArg (fun z : I => (z : U)) hz)
    · rintro ⟨_,y,rfl⟩
      exact Subtype.ext (hcenter.fixes y)
    · rintro ⟨_,y,rfl⟩ w
      have hm := hcenter.displacement y (j w)
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
      exact Submodule.mem_span_singleton.mpr ⟨c,Subtype.ext hc⟩
    · intro φ hφ
      obtain ⟨y,hy⟩ := hcenter.full (φ.comp j.symm.toLinearMap) hφ
      refine ⟨⟨_,y,rfl⟩,fun w => ?_⟩
      exact Subtype.ext (hy (j w))
  have hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) I := by
    apply Module.Dual.finrank_ker_add_one_of_ne_zero
    intro hz
    apply haxis
    intro w hw
    have he := LinearMap.congr_fun hz (⟨w,hw⟩ : I)
    exact he
  have halt : (B.restrict I).IsAlt := fun w => h.alternating w
  have hpres := constituentGeneratedImage_preserves h hI
  have hperp : W = ((B.restrict I) (iw : I)).ker :=
    hfull.hyperplane_eq_orthogonal (B.restrict I) halt hnd
      (fun q => hpres ((show Q ≤ (constituentGeneratedImage ρ C X I hI) from le_sup_right) q.property))
      hW (hI.isIrrPlus.finrank_gt_two ρ (componentOrbit C ⊤))
  have hgood := ChapterG.Section12.goodVector_of_fullCenterAction halt hpres
    (show Q ≤ (constituentGeneratedImage ρ C X I hI) from le_sup_right) hfull hperp
  have hWne : W ≠ ⊤ := by
    intro he
    rw [he,finrank_top] at hW
    omega
  obtain ⟨a,ha,haW⟩ := (constituentImage_irreducible h hn hI).exists_outside hWne hfull.nonzero
  have hpair : (B.restrict I) (a iw) iw ≠ 0 := by
    intro hz
    exact haW (hperp.ge (halt.eq_iff.mp hz))
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I) halt hnd
  have hd := (hI.isIrrPlus.finrank_gt_two ρ (componentOrbit C ⊤))
  exact ⟨a iw,iw,halt,hnd,hpres,by omega,
    hgood.conjugate hpres ((show (constituentLinearAction ρ C X I hI).range ≤ (constituentGeneratedImage ρ C X I hI)
      from le_sup_left) ha),hgood,hpair⟩


omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
include hC hI in
/-- The normal component orbit has perfect image on the same constituent. -/
theorem constituentImage_perfect : Group.IsPerfect (constituentLinearAction ρ C X I hI).range := by
  let : Group.IsPerfect (componentOrbit C ⊤) := hC.orbit_isPerfect ⊤
  exact Group.IsPerfect.ofSurjective (f := (constituentLinearAction ρ C X I hI).rangeRestrict)
    (constituentLinearAction ρ C X I hI).rangeRestrict_surjective

omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
include hI in
/-- Relative normality in the generated action image, not in all GL(I). -/
theorem constituentImage_normal :
    ((constituentLinearAction ρ C X I hI).range.subgroupOf (constituentGeneratedImage ρ C X I hI)).Normal := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let N := subspaceStabilizer ρ I
  let a : N →* (I ≃ₗ[ZMod 2] I) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
      (stabilizerRepresentation ρ I).asGroupHom
  have hK : (constituentLinearAction ρ C X I hI).range = (H.subgroupOf N).map a := by
    ext k
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨⟨h,hI.invariant h.property⟩,h.property,rfl⟩
    · rintro ⟨h,hh,he⟩
      exact ⟨⟨h,hh⟩,he⟩
  have hQ : (constituentStabilizerAction ρ X I).range ≤
      (⊤ : Subgroup N).map a := by
    rintro k ⟨y,rfl⟩
    exact ⟨⟨((y : X) : D),y.property⟩,mem_top _,rfl⟩
  have hn : (constituentStabilizerAction ρ X I).range ≤
      normalizer ((constituentLinearAction ρ C X I hI).range : Set (I ≃ₗ[ZMod 2] I)) := by
    rw [hK]
    exact hQ.trans (by
      rw [← (H.subgroupOf N).normalizer_eq_top]
      exact Subgroup.le_normalizer_map a)
  exact normal_subgroupOf_of_le_normalizer
    (sup_le (constituentLinearAction ρ C X I hI).range.le_normalizer hn)

omit [Finite D] in
include hC hI in
/-- HY has the literal H-image as its embedded solvable residual. -/
theorem constituentGeneratedImage_residual :
    ChapterG.Section12.embeddedResidual (constituentGeneratedImage ρ C X I hI) =
      (constituentLinearAction ρ C X I hI).range := by
  let : Finite I := Module.finite_of_finite (ZMod 2)
  let : Finite (I ≃ₗ[ZMod 2] I) :=
    Finite.of_injective (fun a : I ≃ₗ[ZMod 2] I => (a : I → I)) DFunLike.coe_injective
  let K := (constituentLinearAction ρ C X I hI).range
  let Q := (constituentStabilizerAction ρ X I).range
  let D := (constituentGeneratedImage ρ C X I hI)
  let Y := constituentStabilizer ρ X I
  let : IsElementaryAbelian 2 Y :=
    IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  have hp : IsPGroup 2 Q := (IsElementaryAbelian.isPGroup 2 Y).of_surjective
    (constituentStabilizerAction ρ X I).rangeRestrict
    (constituentStabilizerAction ρ X I).rangeRestrict_surjective
  let : Group.IsPerfect K := constituentImage_perfect hC hI
  let : (K.subgroupOf D).Normal := constituentImage_normal hI
  let : Group.IsPerfect (K.subgroupOf D) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ D from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ D from le_sup_left)).symm.surjective
  have hgen : K.subgroupOf D ⊔ Q.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ D from le_sup_left),
      map_subgroupOf_eq_of_le (show Q ≤ D from le_sup_right),
      ← MonoidHom.range_eq_map,range_subtype]
  change (solvableResidual D).map D.subtype = K
  rw [(residuals_of_perfect_normal_sup_twoGroup (K.subgroupOf D)
    (Q.subgroupOf D) hp.comap_subtype hgen).2,
    map_subgroupOf_eq_of_le (show K ≤ D from le_sup_left)]


include h hn hC hI in
/-- Above degree four, recognition gives the literal full symplectic or
orthogonal residual on the original constituent. -/
theorem higher_models
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (haxis : ¬ I ≤ (B v).ker) (hnd : (B.restrict I).Nondegenerate)
    (hd : 6 ≤ finrank (ZMod 2) I) :
    (constituentLinearAction ρ C X I hI).range =
      ChapterG.Section12.embeddedResidual (ChapterG.Section12.formStabilizer (B.restrict I)) ∨
    ∃ q : QuadraticForm (ZMod 2) I, q.polarBilin = B.restrict I ∧
      (constituentGeneratedImage ρ C X I hI) ≤ q.isometrySubgroup ∧
      (constituentLinearAction ρ C X I hI).range =
        ChapterG.Section12.embeddedResidual q.isometrySubgroup := by
  obtain ⟨u,i,hi⟩ := nondegenerate_classification_inputs h hn hC hI hgeo haxis hnd
  by_cases ht : ∀ x : I, x ≠ 0 → ∃ a ∈ constituentGeneratedImage ρ C X I hI, a i = x
  · left
    rw [← constituentGeneratedImage_residual hC hI,
      hi.eq_formStabilizer_of_transitive_ge_six hd ht]
  · right
    obtain ⟨q,hq,hO,he⟩ := hi.good_v.residual_orthogonal_of_not_transitive hnd
      hi.preserves hi.irreducible (by omega) ht
    rw [constituentGeneratedImage_residual hC hI] at he
    exact ⟨q,hq,hO,he⟩

include h hn hC hI in
/-- Faithful ambient irreducibility makes the actual component image nontrivial. -/
theorem constituentImage_ne_bot : (constituentLinearAction ρ C X I hI).range ≠ ⊥ := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    (h.irreducible_of_not_solvable hn) H hC.componentOrbit_top_ne_bot
  intro he
  apply hI.isIrrPlus.ne_bot ρ
  apply bot_unique
  rw [← hfix]
  intro u hu a
  have ha : constituentLinearAction ρ C X I hI a = 1 :=
    mem_bot.mp (he ▸ (show constituentLinearAction ρ C X I hI a ∈
      (constituentLinearAction ρ C X I hI).range from ⟨a,rfl⟩))
  exact congrArg (fun f : I ≃ₗ[ZMod 2] I => (f ⟨u,hu⟩ : U)) ha

include h hn hC hI in
/-- In degree four the actual perfect image in Sp(I) is its A6 residual or
an A5 subgroup. Both alternatives retain the original inclusion in GL(I). -/
theorem four_models (hnd : (B.restrict I).Nondegenerate)
    (hd : finrank (ZMod 2) I = 4) :
    (constituentLinearAction ρ C X I hI).range =
      ChapterG.Section12.embeddedResidual (ChapterG.Section12.formStabilizer (B.restrict I)) ∨
    Nonempty ((constituentLinearAction ρ C X I hI).range ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨f⟩ := Matrix.PSp4Three.exists_isometry 2 (B.restrict I)
    (fun w => h.alternating w) hnd hd
  let e : ChapterG.Section12.formStabilizer (B.restrict I) ≃* Equiv.Perm (Fin 6) :=
    (ChapterG.Section12.formStabilizerEquivSp (B.restrict I) f).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  let : Group.IsPerfect (constituentLinearAction ρ C X I hI).range :=
    constituentImage_perfect hC hI
  exact AlternatingSix.PerfectSubgroups.in_symmetric_six
    (constituentLinearAction ρ C X I hI).range
    (ChapterG.Section12.formStabilizer (B.restrict I)) e
    (constituentImage_ne_bot h hn hC hI)
    (le_sup_left.trans (constituentGeneratedImage_preserves h hI))

/-- The exhaustive nondegenerate image alternatives, on the literal
constituent and its original form. No recognition input is part of this predicate. -/
def RecognizedData
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (C X : Subgroup D) (I : Submodule (ZMod 2) U)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit C ⊤) X I) : Prop :=
  let K := (constituentLinearAction ρ C X I hI).range
  let J := constituentGeneratedImage ρ C X I hI
  (∃ u i : I, ChapterG.Section12.ClassificationHypotheses J (B.restrict I) u i) ∧
  (K = ChapterG.Section12.embeddedResidual (ChapterG.Section12.formStabilizer (B.restrict I)) ∨
    (6 ≤ finrank (ZMod 2) I ∧ ∃ q : QuadraticForm (ZMod 2) I,
      q.polarBilin = B.restrict I ∧ J ≤ q.isometrySubgroup ∧
      K = ChapterG.Section12.embeddedResidual q.isometrySubgroup) ∨
    (finrank (ZMod 2) I = 4 ∧ Nonempty (K ≃* alternatingGroup (Fin 5))))

include h hn hC hI in
/-- The actual nondegenerate constituent satisfies the full image catalogue.
The two higher-degree cases use proved G.12 recognition; degree four uses
perfect-subgroup recognition in the actual symplectic group. -/
theorem recognized_data
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (haxis : ¬ I ≤ (B v).ker) (hnd : (B.restrict I).Nondegenerate) :
    RecognizedData ρ B C X I hI := by
  have hg := nondegenerate_classification_inputs h hn hC hI hgeo haxis hnd
  refine ⟨hg,?_⟩
  obtain ⟨u,i,hi⟩ := hg
  by_cases hd : finrank (ZMod 2) I = 4
  · rcases four_models h hn hC hI hnd hd with hs | ha
    · exact Or.inl hs
    · exact Or.inr (Or.inr ⟨hd,ha⟩)
  · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I) hi.alternating hnd
    have hd6 : 6 ≤ finrank (ZMod 2) I := by have := hi.dimension; omega
    rcases higher_models h ‹¬ Group.IsSolvable D› hC hI hgeo haxis hnd hd6 with hs | ho
    · exact Or.inl hs
    · exact Or.inr (Or.inl ⟨hd6,ho⟩)

include h hn hC hI in
/-- Every recognized image has trivial center. This does not assume that
the original component orbit acts faithfully on the constituent. -/
theorem recognized_image_centerless
    (hnd : (B.restrict I).Nondegenerate) (hm : RecognizedData ρ B C X I hI) :
    center (constituentLinearAction ρ C X I hI).range = ⊥ := by
  let : (componentOrbit C ⊤).Normal := componentOrbit_top_normal C
  let : Group.IsPerfect (componentOrbit C ⊤) := hC.orbit_isPerfect ⊤
  have hd := hI.isIrrPlus.finrank_gt_two ρ (componentOrbit C ⊤)
  rcases hm.2 with hs | ⟨_,q,hq,_,he⟩ | ⟨hfour,⟨e⟩⟩
  · rw [hs]
    by_cases hf : finrank (ZMod 2) I = 4
    · exact (ChapterG.Section12.symplecticResidual_four_model
        (B.restrict I) (fun w => h.alternating w) hnd hf).1
    · obtain ⟨n,hn⟩ := AlternatingForm.even_finrank (B.restrict I)
        (fun w => h.alternating w) hnd
      exact (ChapterG.Section12.symplecticResidual_center_and_threeRank
        (B.restrict I) (fun w => h.alternating w) hnd (by omega)).1
  · have hir := constituentImage_irreducible h hn hI
    rw [he] at hir ⊢
    exact BinaryReflectionCenter.center_orthogonal_residual_eq_bot q (hq.symm ▸ hnd) hd hir
  · apply _root_.eq_bot_iff.mpr
    intro z hz
    apply e.injective
    rw [map_one]
    apply mem_bot.mp
    rw [← alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5))]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a,rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz a)

include h hn hC hI in
/-- Centerlessness of the actual image kills the center of its original
normal component orbit, retaining the literal action map and its kernel. -/
theorem recognized_orbit_centerless
    (hnd : (B.restrict I).Nondegenerate) (hm : RecognizedData ρ B C X I hI) :
    center (componentOrbit C ⊤) = ⊥ := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let a := constituentLinearAction ρ C X I hI
  apply center_eq_bot_of_constituent_quotient ρ h.faithful
    (h.irreducible_of_not_solvable hn) H I hI.invariant (hI.isIrrPlus.ne_bot ρ)
    a.rangeRestrict a.rangeRestrict_surjective
    (recognized_image_centerless h hn hC hI hnd hm)
  intro z hz
  have he : a z = 1 := congrArg Subtype.val hz
  have hu := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).injective
    (he.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).map_one.symm)
  exact congrArg Units.val hu

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNondegenerate

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor CoreGeometry
open LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Apply the nondegenerate image recognition to the original rank-three flag.
The original actor, component, constituent and restricted form are unchanged. -/
theorem source_exchanged_nondegenerate_recognition (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit C ⊤)
      (F.terminalDot (F.X g)) I) (hv : v ∉ I) (hnd : (B.restrict I).Nondegenerate) :
    ExchangedNondegenerate.RecognizedData F.terminalRepresentation B C
      (F.terminalDot (F.X g)) I hI ∧
    center (ExchangedNondegenerate.constituentLinearAction F.terminalRepresentation C
      (F.terminalDot (F.X g)) I hI).range = ⊥ ∧ center (componentOrbit C ⊤) = ⊥ := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hns := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := Chapter14.Section03.NonabelianSource.Recognition.terminal_component_normalizer_index_le_two
    d.qtke F (by decide) C hC
  have hPX : (P : Subgroup F.TerminalHdot) ≤ normalizer (F.terminalDot (F.X g) : Set F.TerminalHdot) :=
    (normal_subgroupOf_iff_le_normalizer hXP).mp hN
  have hc := source_exchanged_completion d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv
  have hgeo := hyp.exchanged_constituent_geometry hns hC hm P hPX hind hI hv
  have haxis := hyp.exchanged_constituent_not_le_axis hns hC hm P hPX hind hI hv hc.1
  have hr := ExchangedNondegenerate.recognized_data hyp hns hC hI hgeo haxis hnd
  exact ⟨hr,ExchangedNondegenerate.recognized_image_centerless hyp hns hC hI hnd hr,
    ExchangedNondegenerate.recognized_orbit_centerless hyp hns hC hI hnd hr⟩

namespace FixedLineReduction
/-- The large original flag now supplies the exhaustive nondegenerate image
models. The earlier source and independent mixed-size premises are retained;
model exclusions and guarded final assembly remain to be discharged. -/
theorem source_large_recognized_nondegenerate_remainder_of_mixed_size (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (size : Chapter10.MixedZeroCore.MixedSizeInput G)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
      ∃ C : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot C ∧
        ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
        ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B C ∧
        ∃ I : Submodule (ZMod 2) (Additive F.Uhat),
        ∃ hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation
            (componentOrbit C ⊤) (F.terminalDot (F.X g)) I,
          v ∉ I ∧ ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I ∧
          ExchangedGeometry.CompletedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧ (B.restrict I).Nondegenerate ∧
          ExchangedNondegenerate.RecognizedData F.terminalRepresentation B C
            (F.terminalDot (F.X g)) I hI ∧
          center (ExchangedNondegenerate.constituentLinearAction F.terminalRepresentation C
            (F.terminalDot (F.X g)) I hI).range = ⊥ ∧ center (componentOrbit C ⊤) = ⊥ := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd⟩ :=
    source_large_nondegenerate_remainder_of_mixed_size d earlier hq chosen structural alternatives
      classification size F hne hZ hlarge g hg hgP hgH
  let := heU
  let := heX
  exact ⟨heU,heX,B,v,hyp,hline,hS,hn,hmodule,C,hC,hm,horth,I,hI,hv,hgeo,hc,hnd,
    source_exchanged_nondegenerate_recognition d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hline hn hC hm hI hv hnd⟩
end FixedLineReduction
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
