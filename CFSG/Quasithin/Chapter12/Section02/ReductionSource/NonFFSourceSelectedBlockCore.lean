module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourBlock
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoGeneration
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original selected block core and action kernel

T-normalization of VA bounds the commutator of O₂(LT) with the original
selected actor. Quasisimple generation and actor escape then identify both
core commutators with the chosen orbit, independently of the selected
degree or model row. Shortness identifies its full component-action kernel
with O₂(L), before eliminating the central two-core quotient O₂(L)/V.

Source: Aschbacher--Smith 8.2.10(1), printed p.721, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- The original selected actor and its Sylow-normalized product identify both
actual core commutators. The full core of LT is retained. -/
theorem sourceOrbit_selected_core_commutators
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hV : V = D.sourceOrbit)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I} {degree : ℕ}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I degree i S)
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

/-- Once the original block commutator is the chosen orbit, its full action
kernel is exactly O₂(L). This keeps the literal component homomorphism. -/
theorem sourceOrbit_component_kernel_of_core_commutator
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (hcomm : ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit) :
    D.orbitComponentHom.ker = pCore 2 L := by
  have hb := D.sourceOrbit_short_of_core_commutator h hmany hV hnon hcomm
  have hB : (ChapterC.blockU L).map L.subtype = D.sourceOrbit := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  apply le_antisymm ?_ (D.orbitComponentHom_kills_core h.toHypothesis1221)
  intro l hl
  rw [←hb.centralizer_blockU]
  intro u hu
  apply Subtype.ext
  let v : Additive D.sourceOrbit := Additive.ofMul ⟨u,hB ▸ mem_map_of_mem L.subtype hu⟩
  let w := D.sourceOrbitCoordinates.symm v
  have hw : w.val.toMul.val.val = (u : G) := by
    exact (D.sourceOrbitCoordinates_apply w).symm.trans
      (congrArg (fun z : Additive D.sourceOrbit => (z.toMul : G))
        (D.sourceOrbitCoordinates.apply_symm_apply v))
  have he := congrArg (fun a : D.orbitComponent =>
    (D.orbitRepresentation a w).val.toMul.val.val) (MonoidHom.mem_ker.mp hl)
  change (l : G) * w.val.toMul.val.val * (l : G)⁻¹ = w.val.toMul.val.val at he
  rw [hw] at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The same selected pair supplies both core commutators and the complete
original component-action kernel, retaining precisely the earlier VA normalization. -/
theorem sourceOrbit_selected_block_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    {H I : Subgroup G} {i : I} {S : Sylow 2 I} {degree : ℕ}
    (s : Selected H T (normalizer (L : Set G)) D.sourceOrbit I degree i S)
    (hTVA : (T : Subgroup G) ≤ normalizer ((D.sourceOrbit ⊔
      (D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2) : Subgroup G) : Set G)) :
    ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,L⁆ = D.sourceOrbit ∧
      ⁅L.pCoreIn 2,L⁆ = D.sourceOrbit ∧ D.orbitComponentHom.ker = pCore 2 L := by
  obtain ⟨hJ,hL⟩ := D.sourceOrbit_selected_core_commutators h.toHypothesis1221 hV s hTVA
  exact ⟨hJ,hL,D.sourceOrbit_component_kernel_of_core_commutator h hmany hV hnon hL⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
