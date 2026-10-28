module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourPointSections
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourPointClosure

/-!
# The actual chosen-orbit closure in the involution centralizer

The positive-weak-closure tensor input supplies the same original central
involution, natural section and transvection pairing. Condition (E) applies
to its full centralizer because that centralizer contains the original T.
The irreducible-section closure calculation then gives E ≤ O₂(C_G(z)),
[E,O₂(C_G(z))] ≤ ⟨z⟩, and squares in ⟨z⟩. Thus E/Z(E) is elementary abelian.
The full centralizer core is also contained in O₂(L_z T).

Every new containment and quotient premise is discharged on the literal
chosen orbit, retaining the original central line and all covering kernels.
Source: Aschbacher–Smith 8.2.12, first paragraph, printed p.722,
refs/quasithin.pdf. The crossing, exact core equality, extraspecial structure,
8.2.13 and zero-weak-closure contradiction remain required for full exclusion.
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

/-- The original tensor action places its actual centralizer normal closure in
the full centralizer two-core, with the central involution retained. -/
theorem sourceOrbit_hermitian_tensor_point_closure
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
        Nat.card (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) = 32 ∧
        zpowers (z : G) < Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z ∧
        Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z < D.sourceOrbit ∧
        PointSectionActions D.sourceOrbit
          (Chapter8.Section02.Centralizer.commutatorSpace L D.sourceOrbit z) (zpowers (z : G))
          (Chapter8.Section02.Centralizer.localResidual L z) ∧
        FullPointTransvectionAction D.sourceOrbit (Chapter8.Section02.Centralizer.localTwoCore L z) z ∧
        Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z ≤
          pCore 2 (centralizer ({(z : G)} : Set G)) ∧
        ⁅Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z,
          pCore 2 (centralizer ({(z : G)} : Set G))⁆ ≤
          (zpowers (z : G)).subgroupOf (centralizer ({(z : G)} : Set G)) ∧
        (∀ x : Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z,
          (x.val : G)^2 ∈ zpowers (z : G)) ∧
        (centralizer ({(z : G)} : Set G)).pCoreIn 2 ≤
          (Chapter8.Section02.Centralizer.localResidual L z ⊔ (T : Subgroup G)).pCoreIn 2 ∧
        IsElementaryAbelian 2 ((Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z) ⧸
          center (Chapter8.Section02.Centralizer.sourceClosure L D.sourceOrbit z)) := by
  obtain ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,_,_,hWcard,_,hZW,hWV,hWN,_,_,_,_,hsections,htrans,_⟩ :=
    D.sourceOrbit_hermitian_tensor_point_sections
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw
  have hTC : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp (hZ.le (mem_zpowers _))).2.2 t ht)
  have hclosure := point_closure_core L D.sourceOrbit T z (h.simpleQTKE.evenCharacteristic T)
    D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.le_sylow
    hzo hTC hZW hWN hsections
  exact ⟨hn,hB,hw1,hcore,z,hzne,hzo,hZ,hWcard,hZW,hWV,hsections,htrans,
    hclosure.1,hclosure.2.1,hclosure.2.2,point_centralizer_core_le_local_core L T z hTC,
    point_closure_center_quotient L D.sourceOrbit z hclosure.1 hclosure.2.1 hclosure.2.2⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
