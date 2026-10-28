module

public import CFSG.Quasithin.Chapter12.Section02.SourceHypotheses
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The original ambient hypotheses and the first 13.1.2 consequences

Hypothesis 13.1.1 excludes rank-two groups over larger binary fields and
exactly the listed small linear, alternating and sporadic groups. It does
not exclude every Lie rank over those fields. A maximal faithful component
with quasisimple two-core quotient therefore satisfies 12.2.3. The genuine
universal 12.2.2 and 12.2.13 statements then construct a T-invariant chosen
module and an element whose ambient centralizer escapes N_G(L): all other
12.2.13 alternatives contradict the original ambient exclusions.

The five-model quotient classification in 13.1.2(3), its natural-module
clause and rigidity clause are separate source obligations. They are not
fields of this setup or conclusions of these two proved implications.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
Hypothesis 13.1.1 and Lemma 13.1.2(1--2), pp.865--866.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02

namespace CFSG.Quasithin.Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Exactly the original global exclusions in Hypothesis 13.1.1, with the
full known-simple catalogue and the actual ambient Sylow two-subgroup. -/
structure Hypothesis1311 (_T : Sylow 2 G) : Prop where
  simpleQTKE : IsSimpleQTKE KnownSimple.IsKnownSimple G
  no_rankTwo : ∀ f : ℕ, 1 < f → ¬ ClassificationModels.IsRankTwoModel G f
  no_linear : ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL G n 2
  no_A9 : ¬ Nonempty (G ≃* alternatingGroup (Fin 9))
  no_M22 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M22)
  no_M23 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M23)
  no_M24 : ¬ Nonempty (G ≃* Sporadic.Mathieu.M24)
  no_He : ¬ Nonempty (G ≃* KnownSimple.SporadicName.he.Carrier)
  no_J4 : ¬ Nonempty (G ≃* Janko4.Model)

/-- Lemma 13.1.2(1) on the original maximal faithful component. -/
theorem Hypothesis1311.hypothesis1223 {T : Sylow 2 G}
    (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    Hypothesis1223 KnownSimple.IsKnownSimple T L :=
  { simpleQTKE := h.simpleQTKE
    maximal_faithful := hL
    quasisimple := hq
    no_rankTwo := h.no_rankTwo
    no_M22 := h.no_M22
    no_M23 := h.no_M23
    no_J4 := h.no_J4 }

/-- The source ambient exclusions discharge every model alternative in
12.2.13, for the same original chosen module. -/
theorem Hypothesis1311.centralizer_escape
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    {T : Sylow 2 G} (h : Hypothesis1311 T) {L V : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (D : ChosenModule T L V) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  rcases earlier G T L V (h.hypothesis1223 hL hq) D with
    hv | ⟨d, hd, _, he⟩ | ⟨_, he⟩ | ⟨_, he⟩
  · exact hv
  · exact (h.no_linear (d + 1) (by rcases hd with rfl | rfl <;> omega) he).elim
  · exact (h.no_A9 he).elim
  · exact (h.no_M24 he).elim

/-- The T-invariant module and escaping centralizer in 13.1.2, constructed
from the actual universal earlier Chapter 12 statements. -/
theorem Hypothesis1311.exists_chosen_module_escape
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    {T : Sylow 2 G} (h : Hypothesis1311 T) {L : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hq : IsQuasisimple (L ⧸ pCore 2 L)) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) ∧
        (T : Subgroup G) ≤ normalizer (V : Set G) ∧
        ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨hTL, ⟨⟨V, ⟨D⟩⟩⟩, hmodule⟩ :=
    structural G T L (h.hypothesis1223 hL hq)
  exact ⟨hTL, V, ⟨D⟩, (hmodule V D).1, h.centralizer_escape earlier hL hq D⟩

end CFSG.Quasithin.Chapter13.Section01
