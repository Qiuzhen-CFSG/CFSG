module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourGeneration
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNonsolvable
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The nonsolvable Hermitian parabolic and its full residual

On positive weak closure, the actual chosen module gives the marked
involution and cubic rank bound in the same H. The source catalogue now
constructs a normal quasisimple component in the literal H/O₂(H). It is
exactly the two-residual, and the full maximal core maps to its center.
The surviving odd linear-two, odd degree-three and binary linear-three
rows retain their actual maximal overlaps and automizer or diagram markings.

This discharges the original generation-parameter and normal-component
inputs to the inspection in 8.2.9. The remaining odd-row inspection and
chief-section exclusions must still give H = IT; zero weak closure and
8.2.10–13 are also still required for the Hermitian contradiction.

Source: Aschbacher–Smith 8.2.9, printed pp.720–721, refs/quasithin.pdf.
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

/-- The actual nonsolvable H-star residual with its original quotient markings. -/
theorem sourceOrbit_hermitian_tensor_nonsolvable_source_models
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
    let q := QuotientGroup.mk' (pCore 2 H)
    let M := ((normalizer (L : Set G)).subgroupOf H).map q
    let Tplus := ((T : Subgroup G).subgroupOf H).map q
    ∃ K : Subgroup (H ⧸ pCore 2 H), IsComponent (H ⧸ pCore 2 H) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (H ⧸ pCore 2 H) = K ∧
      (((normalizer (L : Set G)).subgroupOf H).normalCore).map q =
        (center K).map K.subtype ∧
      K ⊔ Tplus = ⊤ ∧ SingleClauses M K Tplus ∧
      (SingleOddLinearModel M K Tplus ∨ SingleOddRankThreeModel M K Tplus ∨
       ClassicalGroup.IsPSL (sourceImage M K) 3 2 ∧ DiagramModel M K Tplus 1) := by
  have hg := D.sourceOrbit_hermitian_tensor_parabolic_generation
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨_,_,_,I,i,S,s,_,h3,_,himage,_⟩ :=
    D.sourceOrbit_hermitian_tensor_parabolic_odd_rotations
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,_,hout⟩ := intrinsic_source_data h28 R hR hP hM
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH ⟨x.property,hx⟩
  have hm := parabolic_quotient_normal_component_models h28.sqtk R hP hsol
    (D.sourceOrbit.subgroupOf H) hVR hout hmax himage h3
  have hJ : ChapterB.minimalParabolicCore R hP =
      ((normalizer (L : Set G)).subgroupOf H).normalCore := by
    change (ChapterB.minimalParabolicMax R hP).normalCore = _
    rw [←hM]
  dsimp only at hm
  rw [hJ,←hM,hR] at hm
  exact ⟨hg.1,hg.2,hm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
