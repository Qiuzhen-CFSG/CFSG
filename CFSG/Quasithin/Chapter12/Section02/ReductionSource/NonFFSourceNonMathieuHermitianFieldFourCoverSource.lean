module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCoverParabolics

/-!
# Original tensor application of the central-cover parabolic calculation

The original hypotheses supply an H-star overgroup. The positive-weak-closure
theorem then supplies its selected pair and the T-normalization of VA.
These give both full core commutators, which discharge
all premises of the central-cover construction. Its parabolic calculation is
then transported to the same U, P=N_L(U), and R=N_L(U)^∞ in the original G.
In particular, the original O₂(L) lies in [O₂(R),R]V.

This is progress in the central-cover step of Aschbacher–Smith 8.2.10(3),
printed p.721, refs/quasithin.pdf. Eliminating the remaining central kernel
still requires comparison with the original P_I/U natural modules. Neither
O₂(L)=V nor the final Hermitian contradiction is asserted here.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The same original selected four-space supplies the central-cover parabolic
identities without an additional kernel, normalizer, or commutator premise. -/
theorem sourceOrbit_hermitian_tensor_cover_parabolics
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
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        let U := D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
        let P := L ⊓ normalizer (U : Set G)
        let R := Chapter8.Section02.Normalizer.localResidual L U
        ⁅P.pCoreIn 2,P⁆ ⊔ D.sourceOrbit = P.pCoreIn 2 ∧
          ⁅R.pCoreIn 2,R⁆ ⊔ D.sourceOrbit = P.pCoreIn 2 ∧
          L.pCoreIn 2 ≤ ⁅R.pCoreIn 2,R⁆ ⊔ D.sourceOrbit := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨hn,hB,hw1,I,i,S,s,_,_,_,_,hTVA⟩ := D.sourceOrbit_hermitian_tensor_parabolic
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  rcases hn with rfl
  obtain ⟨hcomm,hcommL⟩ := D.sourceOrbit_hermitian_selected_core_commutators
    h.toHypothesis1221 hV s hTVA
  exact ⟨rfl,hB,hw1,H,hH,I,i,S,s,D.sourceOrbit_hermitian_selected_cover_parabolics
    h hmany hV hnon hcomm hcommL d s⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
