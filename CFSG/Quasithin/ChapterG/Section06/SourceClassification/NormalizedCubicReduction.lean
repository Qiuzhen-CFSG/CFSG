module

public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.EarlierSourceReduction
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.IrreducibleActors.Complete

/-!
# The original normalized-cubic source after quasisimple selection

The complete B.5 source induction and the full B.4 actor sieve now leave only
the literal two-factor action case. In every other source branch the same
ambient actor is S3 or S7. The earlier premises are precisely A.2, A.3.6 and
B.4 for the full known-simple catalogue, not a G.6 recognition hypothesis.

This is the remaining source reduction for Aschbacher–Smith C.5.12, p.163,
using G.6.4, pp.345–346. The two-factor case is retained with its actual
subgroups, multiplication isomorphism and quotient submodules.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.SourceInduction
open HighThreeRank.CoverCentralizer.SourceConstruction
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.normalized_cubic_source_reduction
    (hA : SemisimpleInput.{u} KnownSimple.IsKnownSimple)
    (h36 : Chapter1.Section02.A36Input.{u} KnownSimple.IsKnownSimple)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,v} KnownSimple.IsKnownSimple)
    (h : Hypotheses KnownSimple.IsKnownSimple ρ a q)
    (ht : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (S : Sylow 2 G) (c : G) (hc : c ^ 3 = 1) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) :
    (Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 7))) ∨
      Nonempty (SourceTwoFactorCase (ρ.comp (normalClosure ({a} : Set G)).subtype)) := by
  let := h.finite_group
  rcases h.rank_one_source_reduction hA h36 h4 ht with hd | ⟨hq, ⟨d⟩⟩ | hd
  · exact Or.inl (conclusion_models_of_normalized_inverted_cubic hd S c hc hcne hn
      h.involution hi ht)
  · exact Or.inl (Or.inr
      (h.quasisimple_actor_of_normalized_inverted_cubic ht S c hc hcne hi hn hq d))
  · exact Or.inr hd
end CFSG.Quasithin.ChapterG.Section06
