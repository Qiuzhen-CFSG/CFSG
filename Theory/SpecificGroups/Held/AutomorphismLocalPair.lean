module

public import Theory.SpecificGroups.Held.AutomorphismLocalPair.Representative
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.SeedIdentification
public import Theory.SpecificGroups.Held.AutomorphismLocalPair.LiteralLocal
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Assembly of the canonical automorphism-invariant Held pair

For each Sylow two-subgroup T of the degree-2058 Held carrier, the explicit
pair is C_He(Z(T)) and N_He(E(T)), where E(T) joins all normal elementary
subgroups of order 64 in T. Both contain T and are invariant under every
automorphism preserving T, including those exchanging the two elementary
subgroups. Both have self-centralizing intrinsic two-cores and together
generate Held.

The checked representative calculation identifies E(T) with the join of
catalogue rows 20 and 21, bounds its ambient centralizer, and expresses the
two Held generators as words in the locals. Sylow conjugacy transports these
certificates to arbitrary T. Consequently the required fixed-subgroup join
holds for every automorphism, without additional assumptions on that actor.
The conditional transport interfaces are retained alongside the completed pair.
Source: Aschbacher--Smith 2.3.9(7), printed p.526, and GLS3 Table 5.3p.
-/

public section

namespace Held.AutomorphismLocalPair
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- Sylow conjugacy transports the literal generation certificate. -/
theorem locals_generate_of_representative
    (hseed : largeSeed representative = representativeLargeSeed)
    (hgen : centerLocal representative ⊔ representativeLargeLocal = ⊤)
    (T : Sylow 2 He) : centerLocal T ⊔ largeLocal T = ⊤ := by
  obtain ⟨g, hg⟩ := exists_conjugate_representative T
  rw [← hg, centerLocal_map, largeLocal_map, ← Subgroup.map_sup]
  have he : largeLocal representative = representativeLargeLocal := by
    rw [largeLocal, hseed]
    rfl
  rw [he, hgen, map_top_of_surjective _ (MulAut.conj g).surjective]

/-- The ambient centralizer certificate also transports through literal conjugation. -/
theorem largeSeed_selfCentralizing_of_representative
    (hseed : largeSeed representative = representativeLargeSeed)
    (hc : centralizer (representativeLargeSeed : Set He) ≤ representativeLargeSeed)
    (T : Sylow 2 He) : centralizer (largeSeed T : Set He) ≤ largeSeed T := by
  obtain ⟨g, hg⟩ := exists_conjugate_representative T
  rw [← hg, largeSeed_map, hseed,
    ← Theory.Quasithin.map_centralizer]
  exact map_mono hc

/-- Conditional assembly with all automorphism invariance proved, including outer actions.
The hypotheses concern the fixed literal seed; none assumes invariance or the requested pair. -/
theorem pair_of_representative_certificates
    (hseed : largeSeed representative = representativeLargeSeed)
    (hc : centralizer (representativeLargeSeed : Set He) ≤ representativeLargeSeed)
    (hgen : centerLocal representative ⊔ representativeLargeLocal = ⊤)
    (T : Sylow 2 He) (A : Subgroup (MulAut He))
    (hA : ∀ a ∈ A, (T : Subgroup He).map a.toMonoidHom = T)
    (α : MulAut He) :
    (T : Subgroup He) ≤ centerLocal T ∧ (T : Subgroup He) ≤ largeLocal T ∧
    centralizer (pCore 2 (centerLocal T) : Set (centerLocal T)) ≤
      pCore 2 (centerLocal T) ∧
    centralizer (pCore 2 (largeLocal T) : Set (largeLocal T)) ≤
      pCore 2 (largeLocal T) ∧
    (∀ a ∈ A, (centerLocal T).map a.toMonoidHom = centerLocal T) ∧
    (∀ a ∈ A, (largeLocal T).map a.toMonoidHom = largeLocal T) ∧
    α.fixedSubgroup ⊔ (centerLocal T ⊔ largeLocal T) = ⊤ := by
  refine ⟨le_centerLocal T, le_largeLocal T, centerLocal_selfCentralizingCore T,
    largeLocal_selfCentralizingCore T
      (largeSeed_selfCentralizing_of_representative hseed hc T),
    (fun a ha => (locals_invariant T a (hA a ha)).1),
    (fun a ha => (locals_invariant T a (hA a ha)).2), ?_⟩
  rw [locals_generate_of_representative hseed hgen T, sup_top_eq]

/-- The canonical locals generate the actual Held carrier for every Sylow two-subgroup. -/
theorem locals_generate (T : Sylow 2 He) : centerLocal T ⊔ largeLocal T = ⊤ :=
  locals_generate_of_representative representative_largeSeed representative_locals_generate T

/-- The invariant seed is self-centralizing in the ambient Held group. -/
theorem largeSeed_selfCentralizing (T : Sylow 2 He) :
    centralizer (largeSeed T : Set He) ≤ largeSeed T :=
  largeSeed_selfCentralizing_of_representative representative_largeSeed
    representativeLargeSeed_centralizer_le T

/-- The second canonical local has a self-centralizing intrinsic two-core. -/
theorem largeLocal_selfCentralizingCore_of_sylow (T : Sylow 2 He) :
    centralizer (pCore 2 (largeLocal T) : Set (largeLocal T)) ≤
      pCore 2 (largeLocal T) :=
  largeLocal_selfCentralizingCore T (largeSeed_selfCentralizing T)

/-- The explicit invariant Held pair, with every representative premise discharged.
Only setwise preservation of T is needed from the actor group. In particular this
applies to the source two-group containing the inner action of T and its specified
central inner involution fixing T pointwise. -/
theorem pair (T : Sylow 2 He) (A : Subgroup (MulAut He))
    (hA : ∀ a ∈ A, (T : Subgroup He).map a.toMonoidHom = T)
    (α : MulAut He) :
    (T : Subgroup He) ≤ centerLocal T ∧ (T : Subgroup He) ≤ largeLocal T ∧
    centralizer (pCore 2 (centerLocal T) : Set (centerLocal T)) ≤
      pCore 2 (centerLocal T) ∧
    centralizer (pCore 2 (largeLocal T) : Set (largeLocal T)) ≤
      pCore 2 (largeLocal T) ∧
    (∀ a ∈ A, (centerLocal T).map a.toMonoidHom = centerLocal T) ∧
    (∀ a ∈ A, (largeLocal T).map a.toMonoidHom = largeLocal T) ∧
    α.fixedSubgroup ⊔ (centerLocal T ⊔ largeLocal T) = ⊤ :=
  pair_of_representative_certificates representative_largeSeed
    representativeLargeSeed_centralizer_le representative_locals_generate T A hA α

end Held.AutomorphismLocalPair
