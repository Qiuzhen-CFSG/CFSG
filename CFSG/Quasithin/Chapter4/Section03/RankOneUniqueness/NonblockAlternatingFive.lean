module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionAction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFive.ContainingShort
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# Excluding the original nonblock configuration with an A₅ seed

The original full module is U(L) and lies in O₂(K). Restrict the actual L
and the Sylow intersection S∩K through K≤H≤G. C-component minimality
makes this nonsolvable seed normally generate K. The natural A₅ layer's
normal closure is then U(K), and its split chief structure makes K short.
Thus the original containing C-component is a block, contradicting the
nonblock branch without constructing MSData or assuming Hypothesis1223.

NonblockAlternatingFiveApplication supplies the original Baumann Input
and its full-module equality. General nonblock MS construction, secondary
core enlargement and terminal linear-four exclusion remain with
qt-d-1222-rankone-uniqueness-nonblock.
Source: Aschbacher--Smith C.1.7, C.1.13(c), pp.123--125;
original 4.3.8--10, pp.616--617, and 5.1.7(1), pp.633--634.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An original A₅ seed with the full source module forces the containing
constrained C-component to be a block. -/
theorem SourceConfiguration.block_of_alternatingFive
    (c : SourceConfiguration T L) (D : Chapter12.Section02.ChosenModule T L V)
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (hb : IsAlternatingBlock L 5)
    (hu : (blockU L).map L.subtype = Nonblock.W c) : IsBlock c.K := by
  let A := c.ordinaryLocal
  let e : A ≃* L := c.ordinaryLocalEquiv
  have hA : IsAlternatingBlock A 5 := hb.of_mulEquiv e.symm
  obtain ⟨P,hP⟩ := c.ordinary_component_sylow
  have hPA : (P : Subgroup c.K) ≤ normalizer (A : Set c.K) := by
    rw [hP]
    intro s hs l
    exact D.sylow_normalizes_component hs.1 ((l : c.H) : G)
  let f : c.K →* G := c.H.subtype.comp c.K.subtype
  have hfi : Function.Injective f := c.H.subtype_injective.comp c.K.subtype_injective
  have hUf : ((blockU A).map A.subtype).map f = Nonblock.W c := by
    rw [map_map]
    have heq : f.comp A.subtype = L.subtype.comp e.toMonoidHom := by ext x; rfl
    rw [heq,←map_map,RankOne.Solvable.blockU_map_equiv,hu]
  have hU : (blockU A).map A.subtype ≤ pCore 2 c.K := by
    apply (map_le_map_iff_of_injective hfi).mp
    rw [hUf]
    apply (Nonblock.fullModule_lt_core c hf).le.trans
    rw [Nonblock.core_eq_blockLayer]
    change ((blockU c.K).map c.K.subtype).map c.H.subtype ≤ _
    rw [map_map]
    exact map_mono (f := f) blockU_le_core
  have hgen : normalClosure (A : Set c.K) = ⊤ := by
    exact hA.normalClosure_eq_top_in_cComponent (le_refl c.K)
      (c.component.subgroupOf (le_refl c.K)) A
  let := c.component.perfect
  let := c.quotient
  exact ⟨inferInstance,hA.short_of_normalClosure_eq_top A P hPA hU hgen hf,c.component.subnormal⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness

