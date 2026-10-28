module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourMultiplicity
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourTensor
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
/-!
# The original Hermitian pair's cubic and quintic tensors

The selected quotient's faithful F₄ multiplicity action makes every
nonidentity odd element fixed-point-free on the original P/U. A reflection
lifted from the original V fixes the literal B₀/U. The original section
inclusion and the two-copy dimension identity therefore construct the
source tensor: over F₂ in the cubic row and over constructed F₄ scalars in
the quintic row. Both formulas retain the actual quotient maps and product
conjugation action. Every new premise is discharged from the chosen module.

Positive weak closure remains explicit. Equality R=K, the zero weak-closure
exclusion and the remaining 8.2.9–13 belong to the final contradiction.
Source: Aschbacher–Smith 8.2.8(5), printed pp.718–719, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups commutatorElement
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

/-- The actual half-field tensor constructs both source tensor alternatives on the original selected P/U, with their specified fields and literal B₀/U inclusion. -/
theorem sourceOrbit_hermitian_tensor_selected_source_tensor
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
    n = 1 ∧ B.degree = 2 ∧ globalW D.sourceOrbit T = 1 ∧
      ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
        Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
        let U := D.sourceOrbit ⊓ centralizer
          (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
        let R := Chapter8.Section02.Normalizer.localResidual L U
        rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
          U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
          R ⊓ centralizer (U : Set G) = R.pCoreIn 2 ∧
          Nonempty ((R ⧸ pCore 2 R) ≃* SL(2,E 1)) ∧
          ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
            (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
            R ≤ K ∧ normalizer (U : Set G) ≤ normalizer (K : Set G) ∧
            IsQuasisimple (K ⧸ pCore 2 K) ∧
            ⁅R, centralizer (U : Set G)⁆ ≤ R.pCoreIn 2 ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I : Set G) ∧
            R ⊔ K.pCoreIn 2 ≤ normalizer (I.pCoreIn 2 : Set G) ∧
            PairProductAction R I D.sourceOrbit U ∧
            NaturalSectionAction R (D.sourceOrbit ⊓ I.pCoreIn 2) U ∧
            PairNaturalAction R I D.sourceOrbit U i ∧
            PairMultiplicityAction R I D.sourceOrbit U i ∧
            (Nonempty ((I ⧸ pCore 2 I) ≃* PSL(2,ZMod 2)) ∨
             Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) ∧
            (PairCubicTensor R I D.sourceOrbit U ∨ PairQuinticTensor R I D.sourceOrbit U) := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_multiplicity_action
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair,hm,hsieve⟩ := hK
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,_,_,_,_,hIC,_⟩ := selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
    1 (D.hermitianOrbitCoordinates 1 d) j hj he
  have htensor := selected_one_source_tensor s hp hm
    ((commutator_mono le_rfl hIC).trans hcomm) hsieve
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair,hm,hsieve,htensor⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
