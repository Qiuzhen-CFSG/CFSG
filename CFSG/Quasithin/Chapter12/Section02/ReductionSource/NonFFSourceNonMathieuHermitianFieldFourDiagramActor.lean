module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBinaryDiagram
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourDiagramLift

/-!
# The original Sylow actor behind the Hermitian binary diagram row

The maximal-core equality makes the original quotient overlap core-free.
Lift its existing diagram witness to an element of the original T and a
noninner automorphism of the same full residual K=O²(H/O₂(H)). The map on
K is explicitly conjugation by the image of that original element.

Source: Aschbacher–Smith 8.2.9, printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The existing diagram witness is induced by an element of the original T,
acting noninnerly on the same full residual of H/O₂(H). -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_diagram_actor
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
    (hw : 0 < globalW D.sourceOrbit T)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hsol : ¬Group.IsSolvable H) :
    IsEGenerated 1 H ∧ generationParameter H = 1 ∧
    ((normalizer (L : Set G)).subgroupOf H).normalCore = pCore 2 H ∧
    let q := QuotientGroup.mk' (pCore 2 H)
    let M := ((normalizer (L : Set G)).subgroupOf H).map q
    let Tplus := ((T : Subgroup G).subgroupOf H).map q
    ∃ K : Subgroup (H ⧸ pCore 2 H), IsComponent (H ⧸ pCore 2 H) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (H ⧸ pCore 2 H) = K ∧
      center K = ⊥ ∧ K ⊔ Tplus = ⊤ ∧ SingleClauses M K Tplus ∧
      ClassicalGroup.IsPSL K 3 2 ∧ DiagramModel M K Tplus 1 ∧
      ∃ t : H, (t : G) ∈ (T : Subgroup G) ∧ ∃ α : MulAut K,
        α ∉ MulAut.innerSubgroup K ∧
        (∀ k : K, (α k : H ⧸ pCore 2 H) = q t * (k : H ⧸ pCore 2 H) * (q t)⁻¹) := by
  obtain ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram⟩ :=
    D.sourceOrbit_hermitian_tensor_nonsolvable_binary_diagram
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH hsol
  let q := QuotientGroup.mk' (pCore 2 H)
  let M := ((normalizer (L : Set G)).subgroupOf H).map q
  let Tplus := ((T : Subgroup G).subgroupOf H).map q
  let := hKN
  have hMcore : sourceKernel M = ⊥ := image_normalCore_eq_bot _ _ hcore
  obtain ⟨tplus,α,hα,hact⟩ := corefree_diagram_actor_lift M K Tplus hMcore hdiagram
  obtain ⟨t,ht,hqt⟩ := tplus.property
  have hqt' : q t = (tplus : H ⧸ pCore 2 H) := hqt
  refine ⟨hgen,hpar,hcore,K,hcomp,hKC,hKN,hres,hcenter,hKT,hclauses,h2,hdiagram,
    t,ht,α,hα,?_⟩
  intro k
  rw [hqt']
  exact hact k
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
