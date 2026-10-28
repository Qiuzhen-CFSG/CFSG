module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.QuasisimpleCase
/-!
# The simple case in the complete known-simple catalogue

The literal K-group hypothesis places a simple minimal counterexample in
the full carrier catalogue. The nonabelian source convention excludes its
cyclic branch, and the checked alternating ranks exclude every alternating
branch. The remaining Lie and sporadic cases retain their exact family owners.

Source: Aschbacher–Smith A.2.13 and A.2.16, printed pp.37–38.
-/

public section
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

theorem MinimalCounterexample.simple_knownCarrier
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G) (hs : IsSimpleGroup G) :
    KnownSimple.IsKnownSimpleCarrier G := by
  let := hs
  exact (h.simple_case hs).2.2.1.mem.2.2

theorem MinimalCounterexample.simple_not_cyclic
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G) (hs : IsSimpleGroup G) :
    ¬ KnownSimple.IsPrimeCyclicCarrier G := by
  rintro ⟨p, _, ⟨e⟩⟩
  apply (h.simple_case hs).1
  exact ⟨⟨fun a b => e.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩

theorem MinimalCounterexample.simple_not_alternating
    (h : MinimalCounterexample KnownSimple.IsKnownSimple G) (hs : IsSimpleGroup G)
    (n : ℕ) (e : G ≃* alternatingGroup (Fin n)) : False := by
  obtain ⟨hna, hq, hk, hb | ⟨hsq, hc⟩⟩ := h.simple_case hs
  · exact hb ((alternating_simple_models e hq).1)
  · exact hc ((alternating_simple_models e hq).2 hsq)
end CFSG.Quasithin.ChapterA.Section02
