module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointCentralizer
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointMovement
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock


/-!
# The original central-involution five-space and strict flag

The point marking sends the full original residual core onto the native
point radical. Equivariance therefore gives order 32 for the literal
V_z = [V,O₂(C_L(z)^∞)]. The original Sylow normalizes V_z, and its unique
fixed line lies in this nontrivial two-group. The original module has order
512, giving the strict L_z T-invariant series 1 < Z < V_z < V.

The tensor theorem applies this to the same central involution and retains
its SL₂(4) residual quotient and C-component, with no additional geometric
premise. Source: Aschbacher–Smith 8.2.11(1–2), printed p.722,
refs/quasithin.pdf. The natural action on V_z/Z, the action on V/V_z,
and transvection duality remain separate obligations before 8.2.12–13.
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

private theorem point_movement_of_marking
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1))) (c : binaryImage 1)
    (hk : IsPGroup 2 D.orbitComponentHom.ker)
    (z : D.sourceOrbit)
    (hc : c.val (D.hermitianOrbitCoordinates 1 d (Additive.ofMul z)) = PointSection.pointVector) :
    Nat.card (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) = 32 := by
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
  exact marked_point_residual_commutator_card D.sourceOrbit L
    D.sourceOrbit_component_normalizes e q he hq hker z hc

/-- The literal V_z=[V,O₂(C_L(z)^∞)] has order 32 on the original action. -/
theorem sourceOrbit_hermitian_point_commutator_card
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Nat.card (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) = 32 := by
  obtain ⟨c,hc⟩ := D.sourceOrbit_hermitian_point_marking d z hz hne
  have hk : IsPGroup 2 D.orbitComponentHom.ker := by
    rw [D.hermitian_component_kernel h hmany hV hnon hcommL 1 d]
    exact pCore_isPGroup
  exact D.point_movement_of_marking d c hk z hc

/-- The tensor consumer constructs the same central involution, its source
C-component, and the five-dimensional commutator space with no new premise. -/
theorem sourceOrbit_hermitian_tensor_point_movement
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
          (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z : Set G) := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,he,hcomp⟩ :=
    D.sourceOrbit_hermitian_tensor_point_centralizer
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
  have hWcard := D.sourceOrbit_hermitian_point_commutator_card h hmany hV hnon hcommL d z hz hzne
  have hVcard : Nat.card D.sourceOrbit = 512 := by
    change Nat.card (Additive D.sourceOrbit) = 512
    rw [Nat.card_congr (D.hermitianOrbitCoordinates 1 d).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_binary]
    norm_num
  have hTz : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz t ht)
  have hseries := point_commutator_strict_series L D.sourceOrbit (T : Subgroup G) (z : G)
    D.sourceOrbit_component_normalizes D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes T.isPGroup' hTz hzo (hzEq.symm.trans hZ.symm)
    hVcard hWcard
  exact ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,he,hcomp,hWcard,hseries⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
