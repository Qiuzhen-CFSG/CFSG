module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOddProducts
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourGeneration
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original H-star group has generation parameter one

The original Hermitian tensor and positive weak closure supply the same
selected pair, its full two-core intersection, and the marked involution
in H/O₂(H). That involution survives the full maximal core. The original
maximal subgroup normalizes V, so the source component argument gives
E-generation at one and hence n(H) = 1 in the original group.

All local marking and centralization premises are discharged here from
the chosen module and its half-field tensor model. Solvability of H is
not assumed. The nonsolvable residual sieve and chief-section exclusions
in the remainder of 8.2.9 remain separate steps.

Source: Aschbacher–Smith 8.2.9, printed p.720, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
open Chapter8.Section02.Normalizer.SmallOvergroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- E-generation and the attained parameter on every original H-star member. -/
theorem sourceOrbit_hermitian_tensor_parabolic_generation
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
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    IsEGenerated 1 H ∧ generationParameter H = 1 := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨_,_,_,I,i,S,s,_,_,_,himage,_⟩ :=
    D.sourceOrbit_hermitian_tensor_parabolic_odd_rotations
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  obtain ⟨hVR,_,hcore,hout⟩ := intrinsic_source_data h28 R hR hP hM
  have hstar := (parabolic_involution_star_transport R hP (D.sourceOrbit.subgroupOf H)
    hcore hout himage).1
  have hmax : ChapterB.minimalParabolicMax R hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    intro x hx
    exact D.sourceOrbit_hstar_intersection_normalizes h hmany hV hnon hH ⟨x.property,hx⟩
  exact parabolic_generation_one_of_star_involution h28.sqtk R hP
    (D.sourceOrbit.subgroupOf H) hVR hmax hstar

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
