module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourCanonical
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourWeakImage

/-!
# The whole zeroth weak closure on the original field-four orbit

The canonical plane calculation identifies the action of the entire original
W₀(T,V), not just the image of one returning conjugate. Its quotient by the
literal centralizer of V is elementary abelian of order sixteen. Every moving
whole conjugate in T generates that same quotient; its join with the
centralizer kernel is W₀ itself.

The tensor application first uses the checked descent and higher-field
exclusion. It retains the original chosen orbit, automizer and Sylow subgroup,
and supplies the exact quotient for the remaining zero-closure analysis.
Zero-closure exclusion and the normalizer/centralizer argument through 8.2.13
remain unfinished.
Source: Aschbacher--Smith E.3.13, E.3.28, H.4.4--5 and 7.5.6,
printed pp.233,237,381--382,701, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterK.Linear.Recognition.ThreeCubicSieve
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- All moving conjugates in the original Sylow generate W₀ modulo its
centralizer kernel, and this is a rank-four elementary abelian quotient. -/
theorem sourceOrbit_hermitian_zero_closure_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (hw : globalW D.sourceOrbit T = 0) :
    let P := indexedWeakClosure D.sourceOrbit T 0
    rank (inducedAutomizer D.sourceOrbit P) = 4 ∧
      (∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf P).Normal,
        IsElementaryAbelian 2 (P ⧸ (centralizer (D.sourceOrbit : Set G)).subgroupOf P) ∧
        Nat.card (P ⧸ (centralizer (D.sourceOrbit : Set G)).subgroupOf P) = 16) ∧
      ∀ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T →
        ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.sourceOrbit : Set G) →
          P = D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊔
            (P ⊓ centralizer (D.sourceOrbit : Set G)) := by
  have hr := (D.sourceOrbit_hermitian_initial_parameters 1 d h hmany hV hnon).1
  have hm := (D.sourceOrbit_hermitian_localM 1 d h.toHypothesis1221).1
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  let e := D.hermitianOrbitCoordinates 1 d
  have hFF := D.sourceOrbit_automizer_nonFF h.toHypothesis1221 hnon
  exact ⟨(field_four_zero_closure_image D.sourceOrbit e j hj he T
      D.sourceOrbit_weakClosure_setup hFF hr hm hw).2.1,
    (field_four_zero_closure_quotient D.sourceOrbit e j hj he T
      D.sourceOrbit_weakClosure_setup hFF hr hm hw).2,
    fun g hg hc => field_four_zero_closure_generated_by_return D.sourceOrbit e j hj he T
      D.sourceOrbit_weakClosure_setup hFF hr hm hw g hg hc⟩

/-- The original tensor marking gives the exact centralizer quotient of
its zeroth weak closure, without a new action or a substituted Sylow subgroup. -/
theorem sourceOrbit_hermitian_tensor_zero_closure_quotient
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
    (hw : globalW D.sourceOrbit T = 0) :
    n = 1 ∧ B.degree = 2 ∧
      let P := indexedWeakClosure D.sourceOrbit T 0
      rank (inducedAutomizer D.sourceOrbit P) = 4 ∧
        (∃ _hK : ((centralizer (D.sourceOrbit : Set G)).subgroupOf P).Normal,
          IsElementaryAbelian 2 (P ⧸ (centralizer (D.sourceOrbit : Set G)).subgroupOf P) ∧
          Nat.card (P ⧸ (centralizer (D.sourceOrbit : Set G)).subgroupOf P) = 16) ∧
        ∀ g : G, D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ T →
          ¬ D.sourceOrbit.map (MulAut.conj g).toMonoidHom ≤ centralizer (D.sourceOrbit : Set G) →
            P = D.sourceOrbit.map (MulAut.conj g).toMonoidHom ⊔
              (P ⊓ centralizer (D.sourceOrbit : Set G)) := by
  obtain ⟨hn,hB⟩ := D.sourceOrbit_hermitian_tensor_field_four
    h hmany hV hs hnon B C eQ n hdegree hfield hmodel
  refine ⟨hn,hB,?_⟩
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  exact D.sourceOrbit_hermitian_zero_closure_quotient h hmany hV hnon d hw

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
