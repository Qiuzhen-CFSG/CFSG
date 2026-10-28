module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourProduct
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourNaturalPair
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates
/-!
# The original Hermitian natural section and its two-copy extension

For the specified source pair, the same cover marking identifies B₀ with
the canonical hyperplane and U with its Hermitian corner. The last-column
map constructs the natural SL₂(4) action on the actual B₀/U. The exact
residual kernel identifies its acting quotient with R/O₂(R). Two-conjugate
core generation then identifies the original P/U with two natural copies,
retaining the literal inclusion and conjugator i⁻¹, and makes the R-action
diagonal on both.

The half-field tensor consumer supplies every coordinate, kernel and pair
action premise from the original chosen module. Positive weak closure
remains explicit. The multiplicity action of I/P, cubic/dihedral tensor
recognition, R=K, zero weak-closure exclusion and remaining 8.2.8–13 are
still required for the Hermitian contradiction.

Source: Aschbacher–Smith H.4.6(2) and 8.2.8(3–5), printed pp.382,718–719,
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

/-- The natural SL₂(4) marking on the original selected B₀/U. -/
theorem sourceOrbit_hermitian_selected_natural_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hRP : Chapter8.Section02.Normalizer.localResidual L (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) ≤
        normalizer (I.pCoreIn 2 : Set G)) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    NaturalSectionAction R (D.sourceOrbit ⊓ I.pCoreIn 2) U := by
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  obtain ⟨j,hj,he,hcomp⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  obtain ⟨c,hU,hB⟩ := selected_one_section_coordinates s D.sourceOrbit_weakClosure_setup
    (D.hermitianOrbitCoordinates 1 d) j hj he
  let z := binaryActionHom 1 c
  let z' : binaryImage 1 := ⟨z,⟨c,rfl⟩⟩
  let e := (D.hermitianOrbitCoordinates 1 d).trans z
  let q := (MulAut.conj z').toMonoidHom.comp
    (d.groupEquiv.toMonoidHom.comp D.orbitComponentHom)
  let l := (MulAut.conj z).toMonoidHom.comp ((binaryNormalizer 1).subtype.comp j)
  have hl (a : Automizer D.sourceOrbit) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit a v) = l a (e v) := by
    change z (D.hermitianOrbitCoordinates 1 d (automizerRepresentation D.sourceOrbit a v)) =
      z ((j a).val (z.symm (z (D.hermitianOrbitCoordinates 1 d v))))
    rw [z.symm_apply_apply]
    exact congrArg z (he a v)
  have heq (a : L) (v : Additive D.sourceOrbit) :
      e (automizerRepresentation D.sourceOrbit
        (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
          (inclusion D.sourceOrbit_component_normalizes a)) v) = (q a).val (e v) := by
    change e (automizerRepresentation D.sourceOrbit (D.hermitianComponentAutomizer a) v) = _
    rw [hl]
    change z ((j (D.hermitianComponentAutomizer a)).val (z.symm (e v))) =
      z ((d.groupEquiv (D.orbitComponentHom a)).val (z.symm (e v)))
    exact congrArg (fun t : (Space 1 ≃ₗ[ZMod 2] Space 1) => z (t (z.symm (e v)))) (hcomp a)
  have hRL : R ≤ L := (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_left
  have hRU : R ≤ normalizer (U : Set G) :=
    (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right
  have hRB : R ≤ normalizer (D.sourceOrbit ⊓ I.pCoreIn 2 : Set G) :=
    (le_inf (hRL.trans D.sourceOrbit_component_normalizes) hRP).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨_,hR⟩ := D.sourceOrbit_hermitian_selected_fixed_residual_kernel h d s
  obtain ⟨hBU,eB,_,eR,heR⟩ := field_four_section_natural D.sourceOrbit L
    (D.sourceOrbit ⊓ I.pCoreIn 2) U R inf_le_left hRL
    D.sourceOrbit_component_normalizes hRB hRU e q heq hU hB
    (D.sourceOrbit_hermitian_selected_section_kernel h d s) hR
  exact ⟨hRB,hRU,hBU,eB,eR,heR⟩

/-- The actual half-field tensor input supplies the natural section and faithful product action
on the original selected P/U, with no additional action or kernel callback. -/
theorem sourceOrbit_hermitian_tensor_selected_natural_action
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
            PairNaturalAction R I D.sourceOrbit U i := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_pair_normalizer
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP⟩ := hK
  have hp := D.sourceOrbit_hermitian_selected_product_action h.toHypothesis1221 d s
    (le_sup_left.trans hRI) hcomm
  have hn := D.sourceOrbit_hermitian_selected_natural_action h.toHypothesis1221 d s
    (le_sup_left.trans hRP)
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h.toHypothesis1221
  obtain ⟨_,_,_,_,_,_,_,hIC,_⟩ := selected_one_fixed_subgroup s D.sourceOrbit_weakClosure_setup
    1 (D.hermitianOrbitCoordinates 1 d) j hj he
  have hpair := selected_one_natural_pair_action s hp hn
    ((commutator_mono le_rfl hIC).trans hcomm)
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,hp,hn,hpair⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
