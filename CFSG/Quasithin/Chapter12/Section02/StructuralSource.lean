module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Consequences
public import CFSG.Quasithin.Chapter3.Section02.LocalModule
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Assembling the structural part of 12.2.2 from its surviving source branches

Normalization of L is supplied before selecting a module. For each original
chosen V, the two surviving branches of 3.2.5 say that N(L) normalizes V, or
that T normalizes V and C_V(L) is trivial. In either branch the Sylow orbit
is V itself. The earlier local FSU theorem therefore proves reducedness on
the literal subgroup of LT; the normal branch and the fixed-free TI theorem
give trivial intersections under the original N(L).

This is a conditional assembly: normalization and exclusion of the third
3.2.5 branch remain source inputs. The seven module alternatives and 12.2.13
are separate obligations and are not asserted by this structural theorem.
Source: Aschbacher--Smith, Theorem 12.2.2, printed pp.795--796, using
3.2.2(8), 3.2.5, 7.0.1, 10.0.1 and 12.1.11.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u

/-- The normalization input is independent of any chosen Irr⁺ module. -/
def SourceNormalization1222 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L : Subgroup X),
    Hypothesis1223 K T L → (T : Subgroup X) ≤ normalizer (L : Set X)

/-- The two surviving branches of 3.2.5 on every original chosen module.
This does not assume reducedness, TI or the existence of a chosen module. -/
def SourceBranches1222 (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X),
    Hypothesis1223 K T L → ChosenModule T L V →
      normalizer (L : Set X) ≤ normalizer (V : Set X) ∨
      ((T : Subgroup X) ≤ normalizer (V : Set X) ∧ V ⊓ centralizer (L : Set X) = ⊥)

namespace ChosenModule
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
include D h

/-- Invariance identifies the original Sylow orbit with the chosen V,
so 3.2.2(8) proves that V itself is reduced in LT. -/
theorem reduced_of_sylow_normalizes
    (hn : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) := by
  have horbit : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hn)
      (le_componentOrbit V T)
  have hr := (D.fundamentalSetup h).module_reduced
    (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      h.simpleQTKE T h.maximal_faithful.1)
  rw [D.fundamentalSetup_module h, horbit] at hr
  change IsPReduced 2 (V.subgroupOf
    (Chapter3.Section02.localOrbit T L ⊔ (T : Subgroup G))) at hr
  rwa [D.localOrbit_eq] at hr

/-- Both surviving branches give TI for the same V under the same N(L). -/
theorem ti_of_normalizer_or_fixedSpace
    (hb : normalizer (L : Set G) ≤ normalizer (V : Set G) ∨
      V ⊓ centralizer (L : Set G) = ⊥) :
    ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V := by
  intro g hg
  rcases hb with hn | hc
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mp (hn hg))
  · exact D.ti_of_centralizer_eq_bot h
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hc g hg

end ChosenModule

/-- Conditional assembly of the exact structural contract. The existence
step uses independent normalization, never normalization inferred from a choice. -/
theorem structural1222_of_source_branches
    (normalization : SourceNormalization1222 KnownSimple.IsKnownSimple.{u})
    (branches : SourceBranches1222 KnownSimple.IsKnownSimple.{u}) :
    Structural1222 KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ T L h
  have hn := normalization X T L h
  obtain ⟨V, hV⟩ := h.toHypothesis1221.exists_chosen_of_normalizes hn
  refine ⟨hn, ⟨⟨V, hV⟩⟩, ?_⟩
  intro W D
  have hb := branches X T L W h D
  have hTW : (T : Subgroup X) ≤ normalizer (W : Set X) := by
    rcases hb with hM | hW
    · exact hn.trans hM
    · exact hW.1
  have hcases : normalizer (L : Set X) ≤ normalizer (W : Set X) ∨
      W ⊓ centralizer (L : Set X) = ⊥ := hb.imp id And.right
  exact ⟨hTW, D.reduced_of_sylow_normalizes h.toHypothesis1221 hTW,
    D.ti_of_normalizer_or_fixedSpace h.toHypothesis1221 hcases, hcases⟩

end CFSG.Quasithin.Chapter12.Section02
