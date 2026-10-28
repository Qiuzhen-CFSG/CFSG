module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicBlockAction
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# Intrinsic linear-block recognition on the chosen module

Once [O₂(L),L]=V, the natural marking makes the literal commutator layer
irreducible and centerless. The original faithful-local hypothesis supplies
two-perfectness and F*(L)=O₂(L); reducedness supplies centrality of the layer
in the two-core. The quotient map by C_{U(L)}(L) then constructs the actual
BlockModuleModel, with its original conjugation equation and core quotient.

This is a conditional recognition lemma consumed by the completed cyclic
block argument, not a new hypothesis in the source theorem.
Source: Aschbacher--Smith, C.1.7, C.1.12 and 12.2.24, printed pp.123--124,804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U W : Subgroup G} {d p : ℕ} {g v : G}

omit [Finite G] in
theorem NaturalLocalAnalysis.invariant_subgroup (A : NaturalLocalAnalysis T L V d)
    (N : Subgroup G) (hNV : N ≤ V) (hLN : L ≤ normalizer (N : Set G)) :
    N = ⊥ ∨ N = V := by
  obtain ⟨e,f,hf⟩ := A.natural
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  obtain ⟨x,hxN,hx⟩ := SetLike.not_le_iff_exists.mp (mt le_bot_iff.mp hN)
  have hx1 : x ≠ 1 := by simpa using hx
  let z : V := ⟨x,hNV hxN⟩
  have hz : (f z).toAdd ≠ 0 := by
    intro hh
    exact hx1 (congrArg Subtype.val (f.injective (hh.trans f.map_one.symm)))
  apply le_antisymm hNV
  intro y hy
  by_cases hy1 : y = 1
  · exact hy1 ▸ N.one_mem
  let w : V := ⟨y,hy⟩
  have hw : (f w).toAdd ≠ 0 := by
    intro hh
    exact hy1 (congrArg Subtype.val (f.injective (hh.trans f.map_one.symm)))
  obtain ⟨k,hk⟩ := BinaryLinear.OuterCyclic.exists_linearEquiv_apply_eq hz hw
  let s := (BinaryLinear.OuterCyclic.slEquivLinear d).symm k
  have hs : Representation.specialLinearNatural d s (f z).toAdd = (f w).toAdd := by
    change BinaryLinear.OuterCyclic.slEquivLinear d s (f z).toAdd = _
    rw [MulEquiv.apply_symm_apply]
    exact hk
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm s)
  have he : e (QuotientGroup.mk' (pCore 2 L) l) = s := by rw [hl,e.apply_symm_apply]
  have hh := hf l z
  rw [he,hs] at hh
  change ((f.symm (f w)) : G) = _ at hh
  rw [f.symm_apply_apply] at hh
  rw [show y = (l : G) * x * (l : G)⁻¹ from hh]
  exact (mem_normalizer_iff.mp (hLN l.property) x).mp hxN

omit [Finite G] in
theorem NaturalLocalAnalysis.fixed_eq_bot (A : NaturalLocalAnalysis T L V d)
    (D : ChosenModule T L V) : V ⊓ centralizer (L : Set G) = ⊥ := by
  let C := V ⊓ centralizer (L : Set G)
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  rcases A.invariant_subgroup C inf_le_left (hLC.trans (Subgroup.centralizer_le_normalizer _)) with he | he
  · exact he
  · have hv : V ≤ centralizer (L : Set G) := he ▸ (inf_le_right : C ≤ _)
    exact (D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hv))).elim

open ChapterC in
theorem linearTwoBlock_of_commutator_eq
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) (hcomm : ⁅L.pCoreIn 2,L⁆ = V) :
    IsLinearTwoBlock L d := by
  have hU : (blockU L).map L.subtype = V := by
    rw [blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    exact hcomm
  let b : blockU L ≃* V := (equivMapOfInjective (blockU L) L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr hU)
  have hfix := A.fixed_eq_bot D
  have hi : blockU L ⊓ center L = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro u hu
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfix]
    refine ⟨hU ▸ mem_map_of_mem L.subtype hu.1, mem_centralizer_iff.mpr ?_⟩
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hu.2) ⟨l,hl⟩)
  have hf : blockFixed L = ⊥ := by
    apply map_injective (blockU L).subtype_injective
    rw [blockFixed_map,hi,Subgroup.map_bot]
  have hirr : BlockModuleIrreducible L := by
    constructor
    · rw [hi,bot_lt_iff_ne_bot]
      intro he
      apply D.ne_bot
      rw [← hU,he,Subgroup.map_bot]
    · intro N hN _ hNU
      let := hN
      have hNV : N.map L.subtype ≤ V := (map_mono hNU).trans_eq hU
      have hLN : L ≤ normalizer (N.map L.subtype : Set G) := by
        simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
          N.le_normalizer_map L.subtype
      rcases A.invariant_subgroup _ hNV hLN with hz | ht
      · left
        rw [hi]
        exact map_injective L.subtype_injective (hz.trans (Subgroup.map_bot L.subtype).symm)
      · right
        exact map_injective L.subtype_injective (ht.trans hU.symm)
  have hshort : IsShort L := {
    finite := inferInstance
    twoPerfect := h.maximal_faithful.2.1.2.1
    fitting := h.maximal_faithful.2.1.2.2
    elementary := by
      let := D.elementary
      exact IsElementaryAbelian.of_surjective b.symm.toMonoidHom b.symm.surjective
    central := by
      intro u hu q hq
      apply Subtype.ext
      have hqu : (q:G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hq
      have hcore : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
        pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer D.sylow_normalizes_component)
      have hc := D.core_centralizes (hcore hqu)
      exact ((mem_centralizer_iff.mp hc) u (hU ▸ mem_map_of_mem L.subtype hu)).symm
    quotient := Or.inl h.quasisimple
    irreducible := hirr }
  obtain ⟨e,f,hmodel⟩ := A.natural
  have hpos : 0 < d := by have := A.dimension.1; omega
  refine ⟨by have := A.dimension.1; omega,hshort,?_,?_⟩
  · exact ⟨ZMod 2,inferInstance,inferInstance,Nat.card_zmod 2,
      ⟨e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL hpos).symm⟩⟩
  · let m : BlockModule L ≃* Multiplicative (Fin d → ZMod 2) :=
      (((QuotientGroup.quotientMulEquivOfEq hf).trans QuotientGroup.quotientBot).trans b).trans f
    refine ⟨binaryNaturalAut d,⟨{ quotientIso := e, moduleIso := m, intertwining := ?_ }⟩,
      fun _ _ => rfl⟩
    intro l u
    change f (b (blockConjugate L l u)) = binaryNaturalAut d
      (e (QuotientGroup.mk' (pCore 2 L) l)) (f (b u))
    apply f.symm.injective
    apply Subtype.ext
    rw [f.symm_apply_apply]
    exact (hmodel l (b u)).symm



end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
