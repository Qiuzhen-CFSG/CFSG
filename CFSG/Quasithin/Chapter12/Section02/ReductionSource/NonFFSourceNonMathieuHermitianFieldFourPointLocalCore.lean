module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointCrossing
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointLocalCore

/-!
# The original point-local core and closure saturation

The actual point projection and its full kernel identify O₂(L_z T) with
O₂(L_z) O₂(LT). The already constructed central involution, selected-plane
crossing and dual interval then show E O₂(LT) = O₂(L_z) O₂(LT).
The common core commutes with O₂(L_z) modulo the original central line;
the actual fixed-space identity consequently gives V ∩ O₂(C_G(z)) = V_z
and V ∩ E = V_z. All new premises are discharged for the literal tensor.

The original Sylow, module, centralizer, residual, and normal closure are
unchanged. The larger intersection O₂(LT) ∩ O₂(C_G(z)), the equality
EV = O₂(L_z), the extraspecial structure, 8.2.13, and zero weak closure
remain necessary for the full Hermitian contradiction.

Source: Aschbacher–Smith 8.2.11(4) and 8.2.12, printed p.722,
refs/quasithin.pdf.
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

/-- The full original Sylow introduces precisely the original LT core in the point local. -/
theorem sourceOrbit_hermitian_point_local_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcommL : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (Chapter8.Section02.Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 =
      Chapter8.Section02.Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  obtain ⟨c,_,hf,hk,hP,_⟩ := D.sourceOrbit_hermitian_point_centralizer
    h hmany hV hnon hcommL d z hz hne
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz t ht)
  exact point_local_core_product L T z D.sylow_normalizes_component hTC
    (D.hermitianPointProjection d c) hf hk hP

/-- On the same original central involution, crossing and dual irreducibility
fill the full point core modulo O₂(LT), with no marking or kernel premise. -/
theorem sourceOrbit_hermitian_tensor_point_local_core
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
        (R ⊔ (T : Subgroup G)).pCoreIn 2 = X ⊔ Q ∧
          E ≤ Cz.pCoreIn 2 ∧ Cz.pCoreIn 2 ≤ X ⊔ Q ∧
          (¬ E ≤ Q) ∧ E ⊔ Q = X ⊔ Q ∧
          ⁅Q ⊓ Cz.pCoreIn 2,X⁆ ≤ zpowers (z : G) ∧
          D.sourceOrbit ⊓ Cz.pCoreIn 2 =
            Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
          D.sourceOrbit ⊓ E =
            Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,hWcard,hZW,hWV,hsections,htrans,
    hE,hEQ,hsq,hlocal,helem,hdual,H,I,i,S,s,hzU,hWB,hnot,hcross⟩ :=
    D.sourceOrbit_hermitian_tensor_point_crossing
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  obtain ⟨_,_,_,hcomm,hcommL⟩ := D.sourceOrbit_hermitian_tensor_core_commutators
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  rcases hn with rfl
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  have hz : (z : G) ∈ centralizer (T : Set G) :=
    ((mem_omegaOneCenterAmbient_iff _ _).mp (hZ.le (mem_zpowers _))).2.2
  have hprod := D.sourceOrbit_hermitian_point_local_core h hmany hV hnon hcommL d z hz hzne
  have hCQ : (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
      Chapter8.Section02.Centralizer.localTwoCore L z ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    hlocal.trans_eq hprod
  have hE' := map_mono (f := (centralizer ({(z : G)} : Set G)).subtype) hE
  have hVX := (D.sourceOrbit_hermitian_point_core h hmany hV hnon hcommL d z hz hzne).2
  have hjoin := point_closure_join_core L D.sourceOrbit T z hVX (hV ▸ D.le_core)
    (hE'.trans hCQ) hcross hdual
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz t ht)
  have hel := D.sourceOrbit_elementary_join_core_of_core_commutator h hmany hV hnon hcomm
  have hc := point_core_intersection_commutator L D.sourceOrbit T z hTC hel hEQ hjoin
  have hfix := (D.sourceOrbit_hermitian_point_transvections h hmany hV hnon hcommL d z hz hzne).2.2
  have hcap := point_module_core_intersections L D.sourceOrbit T z
    D.sourceOrbit_component_normalizes (hV ▸ D.le_core) hE' hc hfix
  exact ⟨rfl,hB,hw1,hcore,z,hzne,hzo,hZ,hprod,hE',hCQ,hcross,hjoin,hc,hcap⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
