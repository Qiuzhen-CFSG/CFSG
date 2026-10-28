module
public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Components.DirectProduct
public import Theory.GroupTheory.GeneralizedFitting.SingleCenteredProduct
/-!
# The complete semisimple branch of A.2.12

The original counterexample has a centered component. The full local-rank
model sieve and the checked exceptional central product show that there
is at most one. All remaining components form a centerless direct complement.
The literal direct-product rank transfer then contradicts Theorem A's
failure witness. Therefore a semisimple source counterexample is quasisimple.

Only the original counterexample and proper-section simultaneous induction
remain. The nonsemisimple branch is a separate source reduction.

Source: Aschbacher–Smith A.2.12(I)–(III), printed pp.36–37.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {G S : Type u} [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

theorem CounterexampleToTheoremA.quasisimple_of_semisimple
    (h : CounterexampleToTheoremA KnownSimple.IsKnownSimple G S p)
    (ih : TheoremsOnProperSections KnownSimple.IsKnownSimple G)
    (hsemi : IsSemisimple G) : IsQuasisimple G := by
  by_contra hn
  obtain ⟨C, hC, hzC⟩ := h.source_exists_centered_component ih.theoremA hsemi
  have hcp : C ≠ ⊤ := by
    intro ht
    let : IsQuasisimple (⊤ : Subgroup G) := ht ▸ hC.2
    exact hn (IsQuasisimple.of_mulEquiv topEquiv)
  have hothers : ∀ D : Subgroup G, IsComponent G D → D ≠ C → center D = ⊥ := by
    intro D hD hne
    by_contra hzD
    exact hne (h.source_centered_components_eq ih hsemi hn hD hC hzD hzC)
  obtain ⟨B, hzB, ⟨D, hD, hDB⟩, ⟨e⟩⟩ :=
    hC.exists_centerless_direct_complement hsemi hcp hothers
  obtain ⟨Q, hQp, hQ⟩ := hD.exists_nontrivial_two_subgroup
  let R := Q.map (inclusion hDB)
  have hRp : IsPGroup 2 R := hQp.map _
  have hR : R ≠ ⊥ := fun hh => hQ
    ((map_eq_bot_iff_of_injective Q (inclusion_injective hDB)).mp hh)
  exact h.source_not_one_centered_direct_product ih hsemi hn hC hzC hzB
    ⟨normalizer (R : Set B), R, hR, hRp, rfl⟩ e

end CFSG.Quasithin.ChapterA.Section02
