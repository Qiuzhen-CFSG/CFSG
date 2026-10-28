module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointContainment
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointSections
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock





/-!
# The actual chosen-orbit point quotient actions

On the original central involution, V_z/Z is the natural SL₂(4) module
and V/V_z is the five-point A₅ core. The maps use the same actual residual
quotient and original conjugation action. Their full kernels are exactly
Z and V_z. Natural irreducibility is expressed by the original invariant
subgroups between Z and V_z, as needed for the centralizer-closure argument.

The tensor application retains the previously established central involution,
strict invariant flag, C-component, V ≤ O₂(L_z), and complete transvection
pairing. All new coordinate and quotient-action premises are discharged.
Source: Aschbacher–Smith 8.2.11(2–4), printed p.722, refs/quasithin.pdf.
The full ambient closure in 8.2.12, 8.2.13, and the independent zero-closure
branch still remain before the normalized Hermitian contradiction is complete.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Stellmacher ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

private theorem point_sections_of_marking
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) (c : binaryImage 1)
    (hk : IsPGroup 2 D.orbitComponentHom.ker)
    (z : D.sourceOrbit)
    (hc : c.val (D.hermitianOrbitCoordinates 1 d (Additive.ofMul z)) = PointSection.pointVector) :
    PointSectionActions D.sourceOrbit
      (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
      (Chapter8.Section02.Centralizer.localResidual L z) := by
  let e := (D.hermitianOrbitCoordinates 1 d).trans c.val
  let q := (MulAut.conj c).toMonoidHom.comp (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  have hq : Function.Surjective q := (MulAut.conj c).surjective.comp
    (d.groupEquiv.surjective.comp D.orbitComponentHom_surjective)
  have hker : IsPGroup 2 q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective,
      MonoidHom.ker_comp_of_injective _ _ d.groupEquiv.injective]
    exact hk
  have he (l : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes l)) v) = (q l).val (e v) := by
    change c.val (D.hermitianOrbitCoordinates 1 d
      (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer l) v)) =
        c.val ((d.groupEquiv (D.orbitComponentHom l)).val
          (c.val.symm (c.val (D.hermitianOrbitCoordinates 1 d v))))
    exact (congrArg c.val (D.hermitianOrbitCoordinates_component 1 d l v)).trans
      (congrArg (fun w => c.val ((d.groupEquiv (D.orbitComponentHom l)).val w))
        (c.val.symm_apply_apply (D.hermitianOrbitCoordinates 1 d v)).symm)
  exact marked_point_residual_sections D.sourceOrbit L
    D.sourceOrbit_component_normalizes e q he hq hker z hc

/-- The original centralizer residual acts naturally on V_z/Z and as A₅
on V/V_z, through the actual quotient maps and the same residual quotient. -/
theorem sourceOrbit_hermitian_point_sections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    PointSectionActions D.sourceOrbit
      (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
      (Chapter8.Section02.Centralizer.localResidual L z) := by
  obtain ⟨c,hc⟩ := D.sourceOrbit_hermitian_point_marking d z hz hne
  have hk : IsPGroup 2 D.orbitComponentHom.ker := by
    rw [D.hermitian_component_kernel h hmany hV hnon hcommL 1 d]
    exact pCore_isPGroup
  exact D.point_sections_of_marking d c hk z hc

/-- The literal positive-closure tensor consumer supplies both source quotient
actions together with the full point-core containment and transvection pairing. -/
theorem sourceOrbit_hermitian_tensor_point_sections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n)
    (hw : 0 < globalW D.sourceOrbit T) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧ V = L.pCoreIn 2 ∧
      ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
        zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
        Nonempty ((Chapter8.Section02.Centralizer.localResidual L z ⧸
          pCore 2 (Chapter8.Section02.Centralizer.localResidual L z)) ≃* SL(2,Matrix.PSL3Four.F)) ∧
        ((Chapter8.Section02.Centralizer.localResidual L z).subgroupOf
          (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent ∧
        Nat.card (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) = 32 ∧
        ⊥ < zpowers (z : G) ∧
        zpowers (z : G) < Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
        Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z < D.sourceOrbit ∧
        Chapter8.Section02.Centralizer.localResidual L z ⊔ (T : Subgroup G) ≤ normalizer
          (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z : Set G) ∧
        ⁅D.sourceOrbit,Chapter8.Section02.Centralizer.localResidual L z⁆ = D.sourceOrbit ∧
        D.sourceOrbit ≤ Chapter8.Section02.Centralizer.localTwoCore L z ∧
        (centralizer (D.sourceOrbit : Set G)).subgroupOf (Chapter8.Section02.Centralizer.localTwoCore L z) =
          D.sourceOrbit.subgroupOf (Chapter8.Section02.Centralizer.localTwoCore L z) ∧
        (∀ U : Subgroup G, zpowers (z : G) ≤ U →
          U ≤ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z →
          Chapter8.Section02.Centralizer.localResidual L z ≤ normalizer (U : Set G) →
          U = zpowers (z : G) ∨ U = Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) ∧
        PointSectionActions D.sourceOrbit
          (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
          (Chapter8.Section02.Centralizer.localResidual L z) ∧
        FullPointTransvectionAction D.sourceOrbit (Chapter8.Section02.Centralizer.localTwoCore L z) z ∧
        D.sourceOrbit ⊓ centralizer (Chapter8.Section02.Centralizer.localTwoCore L z : Set G) =
          zpowers (z : G) ∧
        ∀ v : D.sourceOrbit, (∀ x : Chapter8.Section02.Centralizer.localTwoCore L z,
          ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔
            v.val ∈ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,he,hcomp,hWcard,hZbot,hZW,hWV,hWN⟩ :=
    D.sourceOrbit_hermitian_tensor_point_movement
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  have hdegree1 : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = 1 := hdegree.trans hn
  have hfield1 : B.degree = 2*1 := hfield.trans (congrArg (fun k : ℕ => 2*k) hn)
  have hmodel1 : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) 1 := hn ▸ hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree1 hfield1 hmodel1
  obtain ⟨_,_,_,hcomm,hcommL⟩ := D.sourceOrbit_hermitian_tensor_core_commutators
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  have hzEq := D.sourceOrbit_omega_center_of_core_commutator h hmany hV hnon hcomm
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    (hzEq.le.trans inf_le_right) (hZ.le (mem_zpowers _))
  have hpointCore := D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hzne
  have hsections := D.sourceOrbit_hermitian_point_sections h hmany hV hnon hcommL d z hz hzne
  have htrans := D.sourceOrbit_hermitian_point_transvections h hmany hV hnon hcommL d z hz hzne
  have hker := D.sourceOrbit_hermitian_point_action_kernel h hmany hV hnon hcommL (z : G)
  have hker' := hker.trans (congrArg
    (fun U : Subgroup G => U.subgroupOf (Chapter8.Section02.Centralizer.localTwoCore L z))
    (hcore.symm.trans hV))
  exact ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,he,hcomp,hWcard,hZbot,hZW,hWV,hWN,hpointCore.1,hpointCore.2,hker',
    fun U hZU hUW hRU => hsections.natural_interval _ _ _ _ U hZU hUW hRU,hsections,htrans⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
