module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourMovement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCore

/-!
# Residual movement in the original field-four core

The selected core modulo its rank-four fixed subgroup has no fixed points
under the literal two-residual. Coprime action through the selected odd
dihedral quotient moves that entire section. Thus the core is its residual
commutator times the fixed subgroup, and that subgroup is exactly its
residual centralizer. The tensor application retains the original chosen
orbit, original Sylow subgroup, and the literal embedded residual.

These discharge the core movement used at the opening of subsection 8.2.2
and in 8.2.7. Selection and the earlier E.2.14 rank and torus clauses remain
explicit; the complete normalizer/centralizer exclusion through 8.2.13
still requires proof.

Source: Aschbacher–Smith E.2.14 and §8.2.2, printed pp.226–227,717–718
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) {H I : Subgroup G} {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The source core movement and exact residual centralizer on the original
parameter-one pair, with no additional action or splitting hypothesis. -/
theorem sourceOrbit_hermitian_selected_one_residual_core
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U ∧
      I.pCoreIn 2 ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G) = U := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  obtain ⟨_,_,_,_,hUeq,_⟩ := Chapter8.Section02.HermitianSource.selected_one_fixed_subgroup s
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  refine ⟨?_,?_⟩
  · exact (Chapter8.Section02.HermitianSource.selected_one_core_residual_product s).trans
      (congrArg (fun U : Subgroup G => ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U)
        hUeq.symm)
  · exact (Chapter8.Section02.HermitianSource.selected_one_core_residual_centralizer s).trans
      hUeq.symm

/-- The literal half-field tensor supplies both core identities in the
original H-star subgroup. Selection and E.2.14 remain explicit source inputs. -/
theorem sourceOrbit_hermitian_tensor_selected_residual_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : D.SourceOrbitNonFF)
    (eR : E214RankClause (G := G) KnownSimple.IsKnownSimple)
    (eT : E214TorusClause (G := G) KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I k i S)
    (B : BinaryField) (C : LinearCover B 3 D.orbitComponent)
    (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (n : ℕ) [NeZero n]
    (hdegree : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      schurDegree (inflated D.orbitRepresentation C) = n)
    (hfield : B.degree = 2*n)
    (hmodel : let := inflated_irreducible D.orbitRepresentation C hs.irreducible
      HasAbsoluteTwistedModel (inflated D.orbitRepresentation C) n) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    n = 1 ∧ k = 1 ∧ B.degree = 2 ∧
      I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔ U ∧
      I.pCoreIn 2 ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G) = U := by
  obtain ⟨hn,hk,hB,_⟩ := D.sourceOrbit_hermitian_tensor_selected_fixed_subgroup_of_hstar
    h hmany hV hs hnon eR eT hH s B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  subst k
  exact ⟨hn,rfl,hB,D.sourceOrbit_hermitian_selected_one_residual_core h.toHypothesis1221 s n d⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
