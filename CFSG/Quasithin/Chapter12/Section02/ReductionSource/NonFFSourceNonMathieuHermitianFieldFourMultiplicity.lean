module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourNatural
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourMultiplicity
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
/-!
# The actual Hermitian pair's multiplicity action and small quotient

The original half-field tensor input supplies the selected natural pair.
Its commuting I-action therefore descends faithfully to I/O₂(I) on an
F₄-plane, retaining the actual P/U marking and conjugator. The selected
odd prime-power dihedral alternative then restricts that quotient to
L₂(2) or D₁₀. Every new action, kernel and commutator premise is discharged
from the original chosen module and its same containing C-component.

Positive weak closure remains explicit. The field-specific tensor
recognition, equality R=K, zero weak-closure exclusion and remaining
8.2.9–13 still belong to the final Hermitian contradiction.

Source: Aschbacher–Smith 8.2.8(3–5), printed pp.718–719,
refs/quasithin.pdf (1 March 2004 manuscript).
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

/-- The actual tensor input constructs the faithful original multiplicity action and proves the cubic/quintic quotient dichotomy. -/
theorem sourceOrbit_hermitian_tensor_selected_multiplicity_action
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
             Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_natural_action
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair⟩ := hK
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,_,_,_,_,hIC,_⟩ := selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
    1 (D.hermitianOrbitCoordinates 1 d) j hj he
  obtain ⟨hm,hsieve⟩ := selected_one_multiplicity_cases s hp hpair
    ((commutator_mono le_rfl hIC).trans hcomm)
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair,hm,hsieve⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
