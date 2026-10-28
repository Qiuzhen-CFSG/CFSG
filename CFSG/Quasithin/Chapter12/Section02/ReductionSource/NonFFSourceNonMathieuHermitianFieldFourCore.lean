module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianSourceSelection

/-!
# The literal field-four pair core and its fixed subgroup

The original chosen orbit supplies Hermitian coordinates for the actual
selected actor. At parameter one its two-core is the product of the original
two elementary factors, has order 2^12, and has the rank-four fixed subgroup
as its center. The quotient by that subgroup is elementary abelian of order
2^8, and its action kernel in I is exactly O₂(I). Minimality of the original H-star subgroup gives H = ⟨I,T⟩, so H
normalizes the fixed subgroup and its two-residual centralizes it.

The tensor application discharges the parameter-one premise with the checked
torus argument. Selection and the earlier E.2.14 rank and torus clauses remain
explicit. The containing-component, tensor and centralizer arguments through
8.2.13 are still required for the full exclusion.

Source: Aschbacher–Smith E.2.10(1,2,6), E.2.13(7) and §8.2.2, pp.222–225,
717–720 (1 March 2004 manuscript, refs/quasithin.pdf).
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

/-- The actual parameter-one pair has the core and quotient used in the
field-four normalizer argument. All subgroups retain their original embeddings. -/
theorem sourceOrbit_hermitian_selected_one_core_structure
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (n : ℕ) [NeZero n]
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction n (binaryImage n))) :
    let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
    let U := D.sourceOrbit ⊓ centralizer (A : Set G)
    I.pCoreIn 2 = (D.sourceOrbit ⊓ I.pCoreIn 2) ⊔ A ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      (∃ _hUI : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^8 ∧
        Nat.card (I.pCoreIn 2) = 2^12 := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding n d h
  have hnorm := Chapter8.Section02.HermitianSource.selected_one_hstar_normalizer s hH
    D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he
  exact ⟨Chapter8.Section02.HermitianSource.selected_one_core_product s,
    Chapter8.Section02.HermitianSource.selected_one_center s
      D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he,
    Chapter8.Section02.HermitianSource.selected_generates_hstar s hH,
    hnorm.1,hnorm.2,
    Chapter8.Section02.HermitianSource.selected_one_section_kernel s
      D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he,
    Chapter8.Section02.HermitianSource.selected_one_core_section s
      D.sourceOrbit_weakClosure_setup n (D.hermitianOrbitCoordinates n d) j hj he⟩

/-- The literal half-field tensor gives the field-four core structure inside
the original H-star subgroup. Earlier selection and E.2.14 remain explicit. -/
theorem sourceOrbit_hermitian_tensor_selected_core_structure
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
      I.pCoreIn 2 = (D.sourceOrbit ⊓ I.pCoreIn 2) ⊔ A ∧
      (center (pCore 2 I)).map (I.subtype.comp (pCore 2 I).subtype) = U ∧
      I ⊔ (T : Subgroup G) = H ∧ H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      (∃ _hUI : (U.subgroupOf I).Normal,
        centralizerModulo ⊤ (pCore 2 I) (U.subgroupOf I) = pCore 2 I) ∧
      ∃ _hU : (U.subgroupOf (I.pCoreIn 2)).Normal,
        IsElementaryAbelian 2 (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) ∧
        Nat.card (I.pCoreIn 2 ⧸ U.subgroupOf (I.pCoreIn 2)) = 2^8 ∧
        Nat.card (I.pCoreIn 2) = 2^12 := by
  obtain ⟨hn,hk,hB,_⟩ := D.sourceOrbit_hermitian_tensor_selected_fixed_subgroup_of_hstar
    h hmany hV hs hnon eR eT hH s B C eQ n hdegree hfield hmodel
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  subst k
  exact ⟨hn,rfl,hB,D.sourceOrbit_hermitian_selected_one_core_structure
    h.toHypothesis1221 hH s n d⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
