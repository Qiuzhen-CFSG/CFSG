module
public import Theory.Representation.FirstCohomology
public import Theory.Representation.SubrepresentationLattice
/-!
# Fixed points of a nontrivial irreducible representation

A nonzero fixed vector spans an invariant line. Irreducibility makes that
line the whole space, contrary to dimension at least two. The terminal
natural A6 support uses this criterion before the Sylow orbit count.
Source application: Aschbacher--Smith, vector choice on printed p.1038.
-/

public section
namespace Representation.OneCohomology
variable {k A V : Type*} [Field k] [Group A] [AddCommGroup V] [Module k V]

theorem fixed_eq_bot_of_irreducible_finrank
    (ρ : Representation k A V) [ρ.IsIrreducible]
    (hdim : 2 ≤ Module.finrank k V) : fixed ρ = ⊥ := by
  apply bot_unique
  intro v hv
  let S : Subrepresentation ρ := {
    toSubmodule := Submodule.span k {v}
    apply_mem_toSubmodule := by
      intro a w hw
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_smul, hv a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp)) }
  rcases eq_bot_or_eq_top S with h | h
  · have hh := congrArg Subrepresentation.toSubmodule h
    have hvS : v ∈ S.toSubmodule := Submodule.subset_span (by simp)
    rw [hh] at hvS
    exact hvS
  · have hh := congrArg Subrepresentation.toSubmodule h
    have hi : Module.finrank k (Submodule.span k {v}) ≤ 1 := by
      simpa using (finrank_span_le_card (R := k) ({v} : Set V))
    change Module.finrank k S.toSubmodule ≤ 1 at hi
    rw [hh] at hi
    change Module.finrank k (⊤ : Submodule k V) ≤ 1 at hi
    rw [finrank_top] at hi
    omega
end Representation.OneCohomology
