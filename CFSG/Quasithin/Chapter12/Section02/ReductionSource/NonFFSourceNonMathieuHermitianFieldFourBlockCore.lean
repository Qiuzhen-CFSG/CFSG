module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourHStarSolvable
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration

/-!
# The original Hermitian block layer

The selected actor A moves the original module and normalizes its product VA.
Its kernel is the literal conjugate intersection, so [O₂(LT),A] lies in V.
The kernel of the action on O₂(LT)/V is normal in LT and contains this escaping
two-actor. Quasisimple generation forces its product with T to be LT;
perfectness then places L in that kernel. Since V=[V,L] and V≤O₂(L), both
[O₂(LT),L] and [O₂(L),L] are exactly V.

The tensor consumer supplies the original selected pair and VA-normalization
using the completed positive-weak-closure argument. No action-kernel or
commutator-generation premise is added to that application.
Source: Aschbacher–Smith 8.2.10(1), printed p.721, refs/quasithin.pdf.
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
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original selected actor and its Sylow-normalized product identify both
actual core commutators. The full core of LT is retained. -/
theorem sourceOrbit_hermitian_selected_core_commutators
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S)
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let A := D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2
  obtain ⟨hAT,hAC,_,hker,_⟩ := selected_core_actor_data s D.sourceOrbit_weakClosure_setup
  have hVQ : D.sourceOrbit ≤ Q := hV ▸ D.le_core
  have hQC : Q ≤ centralizer (D.sourceOrbit : Set G) := hV ▸ D.core_centralizes
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] using
      pCoreIn_le_sylow J (T.subtype le_sup_right)
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hQA : ⁅Q,A⁆ ≤ D.sourceOrbit :=
    Chapter8.Section02.Normalizer.core_commutator_le Q D.sourceOrbit A T hVQ hQC
      (hAT.trans D.sourceOrbit_weakClosure_setup.normalizes)
      ((hAT.trans le_sup_right).trans hJQ)
      (hker ▸ inf_le_left) hQT hTVA
  let K := L.subgroupOf J
  let W := D.sourceOrbit.subgroupOf J
  let QJ := Q.subgroupOf J
  let P := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hWJ : D.sourceOrbit ≤ J := hVQ.trans (pCoreIn_le 2 J)
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let : W.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le D.sourceOrbit_component_normalizes D.sourceOrbit_weakClosure_setup.normalizes)
  let : QJ.Normal := normal_subgroupOf_of_le_normalizer hJQ
  let N := centralizerModulo (⊤ : Subgroup J) QJ W
  let : N.Normal := centralizerModulo_top_normal QJ W
  have hAN : A.subgroupOf J ≤ N := by
    intro a ha
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _,?_⟩
    intro q hq
    exact hQA (commutator_mem_commutator hq ha)
  have hK : K.IsCComponent := h.maximal_faithful.1.1.1
  let : Group.IsPerfect K := hK.perfect
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let e : K ≃* L := subgroupOfEquivOfLe le_sup_left
  let : IsQuasisimple (K ⧸ pCore 2 K) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hgen : K ⊔ (P : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  obtain ⟨x,hx,hxC⟩ := SetLike.not_le_iff_exists.mp hAC
  let y : J := ⟨x,mem_sup_right (hAT hx)⟩
  have hyQ : y ∉ pCore 2 J := fun hh => hxC (hQC (mem_map_of_mem J.subtype hh))
  have hNP := normal_sup_eq_top_of_two_escape K N (P : Subgroup J) hK P.isPGroup'
    hgen (pCore_isPGroup.le_sylow_of_normal P) y (hAT hx) (hAN hx) hyQ
  let : Group.IsNilpotent (J ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N (P : Subgroup J) P.isPGroup' hNP).isNilpotent
  have hKN := le_of_isPerfect_of_solvable_quotient K N
  have hQL : ⁅Q,L⁆ ≤ D.sourceOrbit := by
    apply commutator_le.mpr
    intro q hq l hl
    exact (mem_centralizerModulo_iff.mp (hKN (show
      (⟨l,mem_sup_left hl⟩ : J) ∈ K from hl))).2
      ⟨q,(pCoreIn_le 2 J) hq⟩ hq
  have hLW : D.sourceOrbit ≤ ⁅L.pCoreIn 2,L⁆ := by
    rw [←hV,D.eq_commutator]
    exact commutator_mono D.le_componentCore le_rfl
  have hLQ : L.pCoreIn 2 ≤ Q := pCoreIn_mono_of_normalizes le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  exact ⟨le_antisymm hQL (hLW.trans (commutator_mono hLQ le_rfl)),
    le_antisymm ((commutator_mono hLQ le_rfl).trans hQL) hLW⟩

/-- The literal half-field tensor supplies the block layer on positive weak
closure, including the parameter-one reduction and the original full LT core. -/
theorem sourceOrbit_hermitian_tensor_core_commutators
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
      ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit := by
  obtain ⟨d,_,_⟩ := Chapter7.NormalizedSource.NonMathieuHermitian.exists_component_coordinates
    hs B C n hdegree hfield hmodel
  have hrow : Chapter7.NormalizedSource.NonMathieuAssembly.HermitianRow hs := by
    refine ⟨B,C,⟨eQ⟩,?_⟩
    dsimp only
    rw [hdegree]
    exact ⟨NeZero.pos n,hfield,d.linearEquiv.finrank_eq.trans (finrank_binary n),hmodel⟩
  obtain ⟨H,hH,_⟩ := D.sourceOrbit_hermitian_exists_HStar_outside_core h hmany hs hrow
  obtain ⟨hn,hB,hw1,I,i,S,s,_,_,_,_,hTVA⟩ :=
    D.sourceOrbit_hermitian_tensor_parabolic h hmany hV hs hnon B C eQ n
      hdegree hfield hmodel hw hH
  exact ⟨hn,hB,hw1,D.sourceOrbit_hermitian_selected_core_commutators
    h.toHypothesis1221 hV s hTVA⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
