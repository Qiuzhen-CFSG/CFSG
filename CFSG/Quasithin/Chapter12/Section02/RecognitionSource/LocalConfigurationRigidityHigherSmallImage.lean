module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherIntrinsicQuotients
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.BinaryDegree
public import Theory.Representation.BinaryOffender.TwoCoreFixedSpace

/-!
# Quasisimplicity of the actual low-degree containing image

The original radical R has binary rank at most nine and is self-centralizing,
so N_G(R)/R acts faithfully on it. The containing image has central two-core.
Its action on the fixed space of that core has exactly the core as kernel,
by the P × Q lemma. Thus its intrinsic two-core quotient still has a faithful
binary action of degree at most nine. The genuine noncentral-Fitting degree
bound (at least fifteen) makes this quotient quasisimple, and the central
cover lifts quasisimplicity to the original containing image.

This removes the nonquasisimple-image possibility before identifying the
maximal overcomponent. HigherNoncentral uses it to descend the actual
prime-field projection and close the remaining maximal-component case.
Source: Aschbacher–Smith A.3.6, B.1.10–11 and original 12.2.25,
printed pp.43–45,72–73,805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u

private theorem small_binary_central_core_quasisimple
    {X : Type u} [Group X] [Finite X] {κ : GroupClass.{u}}
    (hQ : IsSQTK κ (X ⧸ pCore 2 X)) (hX : (⊤ : Subgroup X).IsCComponent)
    (hcentral : pCore 2 X ≤ center X)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (ρ : Representation (ZMod 2) X M) (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) M ≤ 12) : IsQuasisimple X := by
  let Q := pCore 2 X
  let W := BinaryOffender.fixedSpace ρ Q
  have hW := BinaryOffender.fixedSpace_stable_of_normal ρ Q
  let a := BinaryOffender.invariantActionHom ρ W hW
  let : Subsingleton (X ⧸ (⊤ : Subgroup X)) := QuotientGroup.subsingleton_quotient_top
  have ha : a.ker = Q := by
    rw [BinaryOffender.invariantActionHom_ker]
    exact BinaryOffender.fixedSpace_kernel_eq_twoCore_of_centralizes ρ hρ ⊤
      (IsPGroup.of_subsingleton 2 _) (by intro x hx y _; exact mem_center_iff.mp (hcentral hx) y)
  let e : (X ⧸ Q) ≃* BinaryOffender.subspaceActionImage ρ W :=
    (QuotientGroup.quotientMulEquivOfEq ha.symm).trans
      (BinaryOffender.invariantActionQuotientEquiv ρ W hW)
  let τ := (BinaryOffender.subspaceImageRepresentation ρ W).comp e.toMonoidHom
  have hτ : Function.Injective τ := (BinaryOffender.subspaceImageRepresentation_injective ρ W).comp e.injective
  let : Group.IsNilpotent Q := pCore_isNilpotent
  have htop : (⊤ : Subgroup (X ⧸ Q)).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hX.map_quotient Q
  have hfit : fittingSubgroup (⊤ : Subgroup (X ⧸ Q)) ≤ center (⊤ : Subgroup (X ⧸ Q)) :=
    ChapterA.Section03.NoncentralFitting.fitting_le_center_of_binary_degree_le_twelve hQ
      (pCore_quotient_pCore_eq_bot 2) htop (τ.comp (⊤ : Subgroup (X ⧸ Q)).subtype)
      (hτ.comp Subtype.val_injective) ((Submodule.finrank_le W).trans hd)
  have hr : solvableRadical (⊤ : Subgroup (X ⧸ Q)) = center (⊤ : Subgroup (X ⧸ Q)) := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm (fun x y => Subtype.ext (mem_center_iff.mp y.property x)))
  let := htop.perfect
  let := htop.isSimpleGroup_quotient_solvableRadical
  let : IsQuasisimple (⊤ : Subgroup (X ⧸ Q)) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hr).symm.isSimpleGroup⟩
  let : IsQuasisimple (X ⧸ Q) := IsQuasisimple.of_mulEquiv topEquiv
  let : Group.IsPerfect X := Group.IsPerfect.top_iff.mp hX.perfect
  exact (show PerfectCentralCovering.Cover X (X ⧸ Q) from
    { toMonoidHom := QuotientGroup.mk' Q, surjective := QuotientGroup.mk'_surjective _,
      isPerfect := inferInstance, ker_le_center := by rwa [QuotientGroup.ker_mk'] }).isQuasisimple

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G} {d : ℕ}

/-- The actual containing image is quasisimple before its maximal-overcomponent
catalogue is known: its faithful binary degree is at most nine, and its
central two-core can be removed on the fixed space without losing faithfulness. -/
theorem containing_image_quasisimple
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : 3 < d)
    {K : Subgroup G}
    (hK : (K.subgroupOf (normalizer (sectionRadical T U : Set G))).IsCComponent)
    (hYK : rigidityHyperplaneResidual L U V ≤ K) :
    IsQuasisimple (ThreeRigidity.image T U K) := by
  let R := sectionRadical T U
  let N := normalizer (R : Set G)
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let : IsElementaryAbelian 2 R := B.elementary
  have hRtwo : IsPGroup 2 R := IsElementaryAbelian.isPGroup 2 R
  have hRne : R ≠ ⊥ := ne_bot_of_le_ne_bot (C.core_ne_bot (by omega : 2 ≤ d))
    (le_inf C.core_le_sylow (by let := C.elementary; exact le_centralizer U))
  have hN : IsSQTK KnownSimple.IsKnownSimple N := h.simpleQTKE.twoLocal_sqtk ⟨R,hRne,hRtwo,rfl⟩
  have hNR : IsSQTK KnownSimple.IsKnownSimple (NormalizerQuotient R) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (R.subgroupOf N) hRtwo.comap_subtype).trans
      (hN.stronglyQuasithin p hp ho)
  let Kb := ThreeRigidity.image T U K
  have hKb := hNR.subgroup Kb
  have hQ : IsSQTK KnownSimple.IsKnownSimple (Kb ⧸ pCore 2 Kb) := by
    refine ⟨?_,hKb.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hKb.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (R.subgroupOf N) := hRtwo.comap_subtype.isNilpotent
  have hcomp : Kb.IsCComponent := hK.map_quotient (R.subgroupOf N)
  have htop : (⊤ : Subgroup Kb).IsCComponent := by
    simpa only [subgroupOf_self] using hcomp.subgroupOf le_rfl
  have he := sectionRadical_selfCentralizing h A C B
  let a := (action R he.symm.le).comp Kb.subtype
  have ha : Function.Injective a := (action_injective R he).comp Kb.subtype_injective
  let σ := Representation.elementaryRepresentation (p := 2) a
  have hσ : Function.Injective σ := by
    intro x y hxy
    apply ha
    apply MulEquiv.ext
    intro r
    exact congrArg Additive.toMul (congrArg
      (fun f : Module.End (ZMod 2) (Additive R) => f (Additive.ofMul r)) hxy)
  apply small_binary_central_core_quasisimple hQ htop
    (containing_image_twoCore_central h D structural A C B hd hK hYK) σ hσ
  have hh := sectionRadical_finrank_le_nine h D structural A C hnone
  change Module.finrank (ZMod 2) (Additive R) ≤ 9 at hh
  omega
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
