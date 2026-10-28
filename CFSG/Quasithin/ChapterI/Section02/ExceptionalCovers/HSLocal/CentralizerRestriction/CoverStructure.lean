module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.CoverResidual
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.SquareReduction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Setup

/-!
# The central root and distinguished square in the HS cover

The perfect cover residual centralizes every lift of the model core center.
Thus the central cyclic root lifts to the actual cover core center. Combining
it with any other root proves the distinguished square, including central
roots. The same argument identifies the image of the whole core center and
proves that the residual centralizes that center.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction

noncomputable def markedCoreEquiv : core ≃* centralizerCore e0 :=
  (core.equivMapOfInjective (localGroup 0).subtype (localGroup 0).subtype_injective).trans
    (MulEquiv.subgroupCongr marked_centralizer_core_eq.symm)

theorem markedCoreEquiv_apply (r : core) : (markedCoreEquiv r : Carrier) = r.val.val := rfl

/-- The model core center is centralized by the model residual, in HS itself. -/
theorem marked_coreCenter_centralizes :
    coreCenter e0 ≤ centralizer (centralizerTwoResidual e0 : Set Carrier) := by
  rintro _ ⟨z,hz,rfl⟩
  let r := markedCoreEquiv.symm z
  have hr : r ∈ center core := by
    apply mem_center_iff.mpr
    intro s
    apply markedCoreEquiv.injective
    simpa only [map_mul, r, MulEquiv.apply_symm_apply] using
      (mem_center_iff.mp hz (markedCoreEquiv s))
  rw [mem_centralizer_iff]
  intro x hx
  rw [marked_centralizer_residual_eq] at hx
  obtain ⟨g,hg,hgx⟩ := mem_map.mp hx
  rw [← hgx]
  have hh := modelResidual_fixes_center ⟨g,hg⟩ r hr
  have he := congrArg (fun a : localGroup 0 => (a : Carrier))
    (mul_inv_eq_iff_eq_mul.mp hh)
  change g.val * z.val = z.val * g.val
  have hrval : r.val.val = z.val :=
    congrArg Subtype.val (markedCoreEquiv.apply_symm_apply z)
  simpa only [coe_mul,hrval] using he

variable {K : Type*} [Group K] [Finite K]

/-- Any core element mapping into the model core center is central upstairs. -/
theorem cover_core_central_of_image
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) (a : centralizerCore u)
    (ha : modelMap e a ∈ coreCenter e0) : a ∈ center (centralizerCore u) := by
  have h := cover_commutes_of_model_commutes e hZ u hu a
    (marked_coreCenter_centralizes ha)
  apply mem_center_iff.mpr
  intro r
  apply Subtype.ext
  exact mem_centralizer_iff.mp h r ((map_subtype_le _) r.property)

/-- The literal embedded core centers have exactly the specified image. -/
theorem cover_coreCenter_image
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    (coreCenter u).map (modelMap e) = coreCenter e0 := by
  have hR := cover_core_image e hZ u hu
  apply le_antisymm
  · rintro _ ⟨a,⟨r,hr,rfl⟩,rfl⟩
    have hr0 : modelMap e r ∈ centralizerCore e0 := by
      rw [← hR]
      exact mem_map_of_mem _ r.property
    refine mem_map.mpr ⟨⟨modelMap e r,hr0⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro s
    have hs : s.val ∈ (centralizerCore u).map (modelMap e) := hR.symm ▸ s.property
    obtain ⟨x,hx,he⟩ := mem_map.mp hs
    apply Subtype.ext
    simpa only [coe_mul, map_mul, he] using
      congrArg (fun x : centralizerCore u => modelMap e x)
        (mem_center_iff.mp hr ⟨x,hx⟩)
  · rintro _ ⟨r,hr,rfl⟩
    have hs : r.val ∈ (centralizerCore u).map (modelMap e) := hR.symm ▸ r.property
    obtain ⟨x,hx,he⟩ := mem_map.mp hs
    refine mem_map.mpr ⟨x,mem_map.mpr ⟨⟨x,hx⟩,?_,rfl⟩,he⟩
    apply cover_core_central_of_image e hZ u hu
    rw [he]
    exact mem_map_of_mem _ hr

/-- The residual centralizes V=Z(R), with both groups embedded in K. -/
theorem cover_residual_centralizes_coreCenter
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    centralizerTwoResidual u ≤ centralizer (coreCenter u : Set K) := by
  apply le_centralizer_iff.mpr
  intro a ha
  apply cover_commutes_of_model_commutes e hZ u hu a
  apply marked_coreCenter_centralizes
  rw [← cover_coreCenter_image e hZ u hu]
  exact mem_map_of_mem _ ha

/-- The central cyclic square root really lifts to the upstairs core center. -/
theorem exists_central_core_root
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) :
    ∃ a : centralizerCore u, a ∈ center (centralizerCore u) ∧
      modelMap e ((a : K) ^ 2) = modelMap e u := by
  have hr : cyclicGenerator.val.val ∈ (centralizerCore u).map (modelMap e) := by
    rw [cover_core_image e hZ u hu, marked_centralizer_core_eq]
    exact mem_map_of_mem _ cyclicGenerator.property
  obtain ⟨a,ha,he⟩ := mem_map.mp hr
  refine ⟨⟨a,ha⟩,cover_core_central_of_image e hZ u hu ⟨a,ha⟩ ?_,?_⟩
  · rw [he]
    refine mem_map.mpr ⟨markedCoreEquiv cyclicGenerator,?_,rfl⟩
    apply mem_center_iff.mpr
    intro s
    obtain ⟨s,rfl⟩ := markedCoreEquiv.surjective s
    simpa only [map_mul] using congrArg markedCoreEquiv
      (mem_center_iff.mp cyclicGenerator_mem_center s)
  · rw [map_pow,he,hu]
    exact (congrArg (fun x : core => x.val.val) cyclicGenerator_square).trans commonInvolution_eq_e0

/-- The distinguished-square clause for the marked two-central class. -/
theorem marked_hasUniqueCoreSquareLift
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : modelMap e u = e0) : HasUniqueCoreSquareLift u := by
  obtain ⟨a,ha,haimage⟩ := exists_central_core_root e hZ u hu
  exact hasUniqueCoreSquareLift_of_central_root e hZ u (by rw [hu]; exact central_involution_order)
    (hu.symm ▸ e0_twoCentral) a ha haimage

/-- The distinguished-square clause for every two-central quotient involution. -/
theorem twoCentral_hasUniqueCoreSquareLift
    (e : (K ⧸ center K) ≃* Carrier) (hZ : Nat.card (center K) = 2)
    (u : K) (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u)) :
    HasUniqueCoreSquareLift u := by
  obtain ⟨g,hg⟩ := isConj_iff.mp ((twoCentral_iff_isConj_e0 _ hu).mp hc).symm
  exact marked_hasUniqueCoreSquareLift (e.trans (MulAut.conj g)) hZ u hg

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
