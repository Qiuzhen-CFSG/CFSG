module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointExtraspecial
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointProduct

/-!
# The full original Hermitian point-radical product

On the same chosen-module tensor action and central involution, the closure
and original module generate exactly O₂(L_z). The perfect class-two action
argument removes the full O₂(LT) denominator, discharging the last equality
in source 8.2.12(3). All three clauses of the field-four 8.2.12 calculation
now hold on this literal consumer. Source 8.2.13 and the independent zero
weak-closure branch remain for the complete Hermitian exclusion.

Source: Aschbacher–Smith 8.2.12, printed p.722, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Stellmacher ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- All three clauses of source 8.2.12 on the original positive-closure tensor consumer. -/
theorem sourceOrbit_hermitian_tensor_point_product
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
        let R := Chapter8.Section02.Centralizer.localResidual L z
        let X := Chapter8.Section02.Centralizer.localTwoCore L z
        let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
        let Cz := centralizer ({(z : G)} : Set G)
        let E := (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z).map Cz.subtype
        R = L ⊓ Cz ∧ E = Cz.pCoreIn 2 ∧
          Q ⊓ Cz.pCoreIn 2 = Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
          E ⊔ D.sourceOrbit = X ∧ D.sourceOrbit ⊓ E =
            Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
          IsExtraspecial 2 (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) ∧
          Nat.card (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) = 512 ∧
          Nonempty (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z ≃*
            DihedralCentralProductFourSix.FourModel) := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,hRC,hE,hcap,hjoin,hVE,hextra,hEcard,hfour⟩ :=
    D.sourceOrbit_hermitian_tensor_point_core_intersection
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨_,_,_,hcomm,hcommL⟩ := D.sourceOrbit_hermitian_tensor_core_commutators
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  rcases hn with rfl
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hZ.le (mem_zpowers _))).2.2
  have hTz : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) :=
    fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
  have hWcard := D.sourceOrbit_hermitian_point_commutator_card h hmany hV hnon hcommL d z hz hzne
  have hVcard : Nat.card D.sourceOrbit = 512 := by
    change Nat.card (Additive D.sourceOrbit) = 512
    rw [Nat.card_congr (D.hermitianOrbitCoordinates 1 d).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_binary]
    norm_num
  have hzEq := D.sourceOrbit_omega_center_of_core_commutator h hmany hV hnon hcomm
  obtain ⟨_,hZW,_,hWN⟩ := point_commutator_strict_series L D.sourceOrbit (T : Subgroup G) (z : G)
    D.sourceOrbit_component_normalizes D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes T.isPGroup' hTz hzo
    (hzEq.symm.trans hZ.symm) hVcard hWcard
  obtain ⟨htrans,hfix,_⟩ := D.sourceOrbit_hermitian_point_transvections h hmany hV hnon hcommL d z hz hzne
  have hker := D.sourceOrbit_hermitian_point_action_kernel h hmany hV hnon hcommL (z : G)
  have hker' := hker.trans (congrArg (fun A : Subgroup G => A.subgroupOf
    (Chapter8.Section02.Centralizer.localTwoCore L z)) (hcore.symm.trans hV))
  have hsections := D.sourceOrbit_hermitian_point_sections h hmany hV hnon hcommL d z hz hzne
  have hclosure := point_closure_core L D.sourceOrbit T z (h.simpleQTKE.evenCharacteristic T)
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.le_sylow hzo hTz hZW hWN hsections
  have hVX := (D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hzne).2
  have hcapE : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓
      (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z).map
        (centralizer ({(z : G)} : Set G)).subtype =
      Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z := by
    rw [hE]
    exact hcap
  have hprod := point_closure_join_module L D.sourceOrbit T z hzo
    D.sourceOrbit_component_normalizes D.sylow_normalizes_component
    D.sourceOrbit_weakClosure_setup.normalizes hTz (hV ▸ D.le_core) (hV ▸ D.core_centralizes)
    hVX hsections htrans hker' hfix hZW.le hE
    ((commutator_mono le_rfl hclosure.1).trans hclosure.2.1) hjoin hcapE
  exact ⟨rfl,hB,hw1,hcore,z,hzne,hzo,hZ,hRC,hE,hcap,hprod,hVE,hextra,hEcard,hfour⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
