module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointLocalCore
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointExtraspecial

/-!
# The original Hermitian point centralizer has an extraspecial two-core

For the same central involution and original tensor action, the full LT-core
fixed-subgroup argument identifies O₂(LT) ∩ O₂(C_G(z)) with V_z.
Consequently the original relative normal closure E is all of O₂(C_G(z)).
Its seed is self-centralizing and has fixed subgroup ⟨z⟩. The full pairing
therefore makes E extraspecial of order 512, and its elementary seed of
order 32 identifies it with the concrete central product of four D₈'s.

All new local premises are discharged on the literal chosen-module tensor
consumer. The equality EV = O₂(L_z), the SQTK exclusion in 8.2.13, and the
independent zero-weak-closure branch remain for the Hermitian contradiction.
Source: Aschbacher–Smith 8.2.12(1),(2), printed p.722, refs/quasithin.pdf.
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

/-- The original point centralizer is perfect; the actual point radical
has no additional fixed cosets modulo the central line in the whole LT core. -/
theorem sourceOrbit_hermitian_point_full_core_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcomm : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (hcore : V = L.pCoreIn 2)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G))
    (hne : z ≠ 1) (ho : orderOf (z : G) = 2) :
    Chapter8.Section02.Centralizer.localResidual L z = L ⊓ centralizer ({(z : G)} : Set G) ∧
      ∀ a ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2,
        (∀ x : Chapter8.Section02.Centralizer.localTwoCore L z,
          ⁅(x : G),a⁆ ∈ zpowers (z : G)) →
        a ∈ Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z := by
  obtain ⟨c,_,hf,hk,hP,_⟩ := D.sourceOrbit_hermitian_point_centralizer
    h hmany hV hnon hcommL d z hz hne
  have hVX := (D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hne).2
  have hcoreOrbit : D.sourceOrbit = L.pCoreIn 2 := hV.symm.trans hcore
  have hRC := point_residual_eq_centralizer L (z : G) (D.hermitianPointProjection d c) hf hk hP
    ((hcoreOrbit.symm.le.trans hVX).trans (Chapter8.Section02.Centralizer.localTwoCore_le L z))
  obtain ⟨htrans,hfix,hfix2⟩ := D.sourceOrbit_hermitian_point_transvections h hmany hV hnon hcommL d z hz hne
  have hker := D.sourceOrbit_hermitian_point_action_kernel h hmany hV hnon hcommL (z : G)
  have hker' := hker.trans (congrArg (fun A : Subgroup G => A.subgroupOf
    (Chapter8.Section02.Centralizer.localTwoCore L z)) hcoreOrbit.symm)
  refine ⟨hRC,?_⟩
  intro a ha hfixed
  have haV := point_full_core_second_fixed L D.sourceOrbit T z D.sourceOrbit_component_normalizes
    D.sylow_normalizes_component D.sourceOrbit_weakClosure_setup.le_sylow (hV ▸ D.le_core)
    (hV ▸ D.core_centralizes) hcomm.le
    (D.sourceOrbit_nonFF_sylow_centralizer h hmany hV hnon).1 ho hz hRC htrans hker' hfix a ha hfixed
  exact (hfix2 ⟨a,haV⟩).mp hfixed

/-- On the literal tensor consumer the whole pair of cores intersects in V_z,
and the original normal closure is the full centralizer two-core. -/
theorem sourceOrbit_hermitian_tensor_point_core_intersection
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
          E ⊔ Q = X ⊔ Q ∧ D.sourceOrbit ⊓ E =
            Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
          IsExtraspecial 2 (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) ∧
          Nat.card (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) = 512 ∧
          Nonempty (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z ≃*
            DihedralCentralProductFourSix.FourModel) := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,hprod,hE,hCQ,hcross,hjoin,hc,hVC,hVE⟩ :=
    D.sourceOrbit_hermitian_tensor_point_local_core h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨_,_,_,hcomm,hcommL⟩ := D.sourceOrbit_hermitian_tensor_core_commutators
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  rcases hn with rfl
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hZ.le (mem_zpowers _))).2.2
  obtain ⟨hRC,hfixed⟩ := D.sourceOrbit_hermitian_point_full_core_fixed h hmany hV hnon
    hcomm hcommL hcore d z hz hzne hzo
  let Cz := centralizer ({(z : G)} : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let W := Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z
  let E := (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z).map Cz.subtype
  have hWQ : W ≤ Q := (Chapter8.Section02.Centralizer.commutatorSpace_le L D.sourceOrbit z
    D.sourceOrbit_component_normalizes).trans (hV ▸ D.le_core)
  have hWE : W ≤ E := Chapter8.Section02.Centralizer.commutatorSpace_le_sourceClosure L D.sourceOrbit z
    z.property D.sourceOrbit_component_normalizes
  have hcap : Q ⊓ Cz.pCoreIn 2 = W := by
    apply le_antisymm ?_ (le_inf hWQ (hWE.trans hE))
    intro a ha
    apply hfixed a ha.1
    intro x
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator x.property ha)
  have hEQ : E = Cz.pCoreIn 2 := by
    apply le_antisymm hE
    intro a ha
    have hac : a ∈ Cz := pCoreIn_le 2 Cz ha
    have hjoin' : a ∈ E ⊔ Q := hjoin.ge (hCQ ha)
    have hQC : Q ≤ Cz := by
      have hQT : Q ≤ (T : Subgroup G) := by
        simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
          (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)] using
            pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hz x (hQT hx))
    have hEC : E ≤ Cz := map_subtype_le _
    have hej : (⟨a,hac⟩ : Cz) ∈ E.subgroupOf Cz ⊔ Q.subgroupOf Cz := by
      rw [←subgroupOf_sup hEC hQC]
      exact hjoin'
    let : (E.subgroupOf Cz).Normal := by
      have he : E.subgroupOf Cz = Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z := by
        exact comap_map_eq_self_of_injective Cz.subtype_injective _
      rw [he]
      infer_instance
    obtain ⟨e,he,q,hq,heq⟩ := mem_sup_of_normal_left.mp hej
    have heq' : (e : G)*(q : G)=a := congrArg Cz.subtype heq
    have hqC : (q : G) ∈ Cz.pCoreIn 2 := by
      have hh := (Cz.pCoreIn 2).mul_mem ((Cz.pCoreIn 2).inv_mem (hE he)) ha
      change (e : G)⁻¹*a ∈ _ at hh
      rw [←heq',inv_mul_cancel_left] at hh
      exact hh
    rw [←heq']
    exact E.mul_mem he (hWE (hcap.le ⟨hq,hqC⟩))
  have hWcard := D.sourceOrbit_hermitian_point_commutator_card h hmany hV hnon hcommL d z hz hzne
  have hVcard : Nat.card D.sourceOrbit = 512 := by
    change Nat.card (Additive D.sourceOrbit) = 512
    rw [Nat.card_congr (D.hermitianOrbitCoordinates 1 d).toEquiv]
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_binary]
    norm_num
  have hTz : (T : Subgroup G) ≤ Cz := fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)
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
  have helem := point_closure_center_quotient L D.sourceOrbit z hclosure.1 hclosure.2.1 hclosure.2.2
  have hLQ : L ≤ normalizer (Q : Set G) := le_sup_left.trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hcapE : Q ⊓ E = W := by rw [hEQ]; exact hcap
  obtain ⟨hself,hfixedE⟩ := point_closure_seed_centralizers L D.sourceOrbit Q z hzo
    D.sourceOrbit_component_normalizes hLQ (hV ▸ D.le_core) (hV ▸ D.core_centralizes)
    htrans hker' hfix hZW.le hjoin hcapE
  have hextra := point_closure_extraspecial L D.sourceOrbit z hzo D.sourceOrbit_component_normalizes
    helem (by rw [hWcard]; decide) hself hfixedE
  have hVX := (D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hzne).2
  have hEcard := point_closure_card L D.sourceOrbit Q z hLQ (hV ▸ D.le_core)
    (hV ▸ D.core_centralizes) hVX htrans hker' hWcard hjoin hcapE
  have hfour := point_closure_four_model L D.sourceOrbit z D.sourceOrbit_component_normalizes
    hextra hEcard hWcard hself
  exact ⟨rfl,hB,hw1,hcore,z,hzne,hzo,hZ,hRC,hEQ,hcap,hjoin,hVE,hextra,hEcard,hfour⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
