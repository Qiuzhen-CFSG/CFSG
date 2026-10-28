module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourParabolic
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourSolvable

/-!
# The solvable H-star branch of the original Hermitian parabolic

On the original selected pair, E.2.1 and the three- and five-rank bounds
force the full two-residual of H/O₂(H) to have order three or five.
The representative-preserving quotient marking places this residual in
I⁺. The two-core normalizes the original conjugate pair, so residual
lifting proves O²(I) = O²(H), H = IT as a set product, and the original
T-normalization of VA. Every local input is supplied by the chosen-module
and tensor theorems; solvability is the branch being treated.

The nonsolvable parabolic branches, zero weak closure, and the subsequent
8.2.10–13 exclusion remain with the Hermitian source assembly.
Source: Aschbacher–Smith 8.2.9(1–2), printed pp.720–721, refs/quasithin.pdf.
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

/-- Complete 8.2.9(1–2) for every solvable original H-star member,
retaining the selected conjugator, full cores and original Sylow group. -/
theorem sourceOrbit_hermitian_tensor_solvable_parabolic
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
    (hsol : Group.IsSolvable H) :
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        (Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 3 ∨
          Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 5) ∧
        (pResidual 2 I).map I.subtype = (pResidual 2 H).map H.subtype ∧
        (T : Subgroup G) ≤ normalizer ((pResidual 2 I).map I.subtype : Set G) ∧
        (H : Set G) = (I : Set G) * (T : Set G) ∧
        (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G) := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨h28,_⟩ := D.sourceOrbit_hermitian_hstar_setup h hmany hV hnon hs hrow hH
  obtain ⟨hn,hB,hw1,I,i,S,s,_,_,_,_,_,K,_,_,_,_,_,_,_,_,_,_,_,_,hsieve,_,_,_,_,_,_,
    h3,h5,_,hinter,himage,_⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_parabolic_core
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  exact ⟨hn,hB,hw1,I,i,S,s,selected_one_solvable_parabolic s h28 hH hsol
    D.sourceOrbit_weakClosure_setup.normalizes h3 h5 (hinter ▸ inf_le_right) himage hsieve⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
