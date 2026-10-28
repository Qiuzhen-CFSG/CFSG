module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourSection
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourProduct
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianCoordinates

/-!
# The faithful product action on the original Hermitian pair core

On the selected branch, conjugation on P/U has the full kernel O₂(RI)=P O₂(R).
The two restricted kernels are O₂(R) and P. The literal inclusion B₀/U → P/U
intertwines the original R-actions. The quotient by the full
kernel is the product of the original core quotients. The product equivalence
sends the class of ri to the two original quotient classes; the action acts
on the literal original P/U, without a faithful replacement of either group.

The half-field tensor application constructs the same selected pair and
containing quasisimple component and discharges every action/kernel premise.
Positive weak closure remains explicit. The natural/tensor identification,
R=K, zero weak-closure exclusion and the remaining 8.2.8–13 argument remain.
Source: Aschbacher–Smith 8.2.8(4), printed p.718,
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

/-- The original residual and selected pair act on the original eight-space
with their full kernels and marked direct-product quotient. -/
theorem sourceOrbit_hermitian_selected_product_action
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hRI : Chapter8.Section02.Normalizer.localResidual L (D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)) ≤
        normalizer (I : Set G))
    (hcomm :
      let U := D.sourceOrbit ⊓ centralizer
        (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
      let R := Chapter8.Section02.Normalizer.localResidual L U
      ⁅R,centralizer (U : Set G)⁆ ≤ R.pCoreIn 2) :
    let U := D.sourceOrbit ⊓ centralizer
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    PairProductAction R I D.sourceOrbit U := by
  obtain ⟨j,hj,he,_⟩ := D.sourceOrbit_hermitian_normalizer_embedding 1 d h
  let U := D.sourceOrbit ⊓ centralizer
    (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 : Set G)
  let R := Chapter8.Section02.Normalizer.localResidual L U
  have hRU : R ≤ normalizer (U : Set G) :=
    (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right
  have hRV : R ≤ normalizer (D.sourceOrbit : Set G) :=
    (Chapter8.Section02.Normalizer.localResidual_le L U).trans
      (inf_le_left.trans D.sourceOrbit_component_normalizes)
  exact selected_one_full_product_action s D.sourceOrbit_weakClosure_setup
    (D.hermitianOrbitCoordinates 1 d) j hj he R hRV hRI hRU hcomm
    (D.sourceOrbit_hermitian_selected_section_kernel h d s)

/-- The actual half-field tensor input supplies the faithful product action
on the original selected P/U, with no additional action or kernel callback. -/
theorem sourceOrbit_hermitian_tensor_selected_product_action
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
            PairProductAction R I D.sourceOrbit U := by
  obtain ⟨hn,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,hK⟩ :=
    D.sourceOrbit_hermitian_tensor_selected_pair_normalizer
      h hmany hV hs hnon B C eQ n hdegree hfield hmodel hw hH
  subst hn
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C 1 hdegree hfield hmodel
  obtain ⟨K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP⟩ := hK
  exact ⟨rfl,hB,hw1,I,i,S,s,hu,hTU,hUeq,hker,hR,
    K,hKU,hK,hRK,hNK,hq,hcomm,hRI,hRP,
    D.sourceOrbit_hermitian_selected_product_action h.toHypothesis1221 d s
      (le_sup_left.trans hRI) hcomm⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
