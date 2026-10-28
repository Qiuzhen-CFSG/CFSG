module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalGeometry.PairGeometry

/-!
# Nested factors and the contrary-fusion branch of Aschbacher 3.4

For nested factors, strong closure of their union implies normalization of
the larger factor. It does not by itself imply normalization of the smaller
factor. Thus the union-preservation argument preceding source (b) does not
establish pair permutation in this case.

The global-closure consumer can avoid this issue: a nonidentity factor element
whose conjugate returns to S under an element outside H rules out nesting by
`Hypotheses.closed_of_nested`. The already proved nonnested pair geometry then
supplies both pair permutation and the unique fixed-coset property needed in
the contrary-fusion argument. In the nested branch, a mixed product is already
in the larger factor, so the full `FusionConclusion` follows directly as well.
No minimality or terminal recognition is used in these reductions. This module
does not assert the requested universal nested
minimal-counterexample pair-permutation theorem.

Source: M. Aschbacher, *On finite groups of component type*, Illinois J. Math.
19 (1975), Lemma 3.4(b), printed p.94, and the contrary-fusion paragraph on
p.95, DOI 10.1215/ijm/1256050927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75

open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1

universe u
variable {G : Type u} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- In the nested case the larger factor is normalized by S. This is the
conclusion justified by preservation of the union in the source argument. -/
theorem Hypotheses.conjugate_sup_eq_of_nested (h : Hypotheses S A₁ A₂)
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) (s : G) (hs : s ∈ S) :
    conjugate (A₁ ⊔ A₂) s = A₁ ⊔ A₂ := by
  have he : (A₁ : Set G) ∪ A₂ = ((A₁ ⊔ A₂ : Subgroup G) : Set G) := by
    rcases hn with hn | hn
    · rw [sup_eq_right.mpr hn, Set.union_eq_right.mpr hn]
    · rw [sup_eq_left.mpr hn, Set.union_eq_left.mpr hn]
  have hc := h.closed_of_nested hn
  rw [he] at hc
  have hle : conjugate (A₁ ⊔ A₂) s ≤ A₁ ⊔ A₂ := by
    rintro x ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact hc.2 a ha s (mem_top _) ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs) (hc.1 ha)) hs)
  exact eq_of_le_of_card_ge hle (by
    rw [show Nat.card (conjugate (A₁ ⊔ A₂) s) = Nat.card (A₁ ⊔ A₂ : Subgroup G) from
      card_map_of_injective (MulAut.conj s⁻¹).injective])

/-- The equal-factor branch of pair permutation does follow from nesting. -/
theorem Hypotheses.permutes_pair_of_eq (h : Hypotheses S A₁ A₂) (he : A₁ = A₂) :
    ∀ s ∈ S, (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁) := by
  subst A₂
  intro s hs
  have hc := h.conjugate_sup_eq_of_nested (Or.inl le_rfl) s hs
  simp only [sup_idem] at hc
  exact Or.inl ⟨hc, hc⟩

/-- The entire nested local-fusion branch, including the final product clause.
Every mixed product lies in the larger factor, so its unique conjugate
membership follows from global strong closure just as for a factor element.
This discharges the literal input to the terminal assembly without asserting
pair permutation or using any terminal recognition theorem. -/
theorem Hypotheses.fusionConclusion_of_nested (h : Hypotheses S A₁ A₂)
    (hn : A₁ ≤ A₂ ∨ A₂ ≤ A₁) : FusionConclusion S A₁ A₂ := by
  have hc := h.closed_of_nested hn
  refine ⟨hc, fun _ ha hne => h.unique_of_closed hc ha hne, ?_⟩
  intro a₁ ha₁ a₂ ha₂ _ _ hne
  apply h.unique_of_closed hc _ hne
  rcases hn with hn | hn
  · exact Or.inr (A₂.mul_mem (hn ha₁) ha₂)
  · exact Or.inl (A₁.mul_mem ha₁ (hn ha₂))

/-- The exact contrary-fusion witness on source p.95 forces incomparability.
This reduction applies to all nonidentity elements, in particular involutions. -/
theorem Hypotheses.nonnested_of_escaping_conjugate (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (hS : g⁻¹ * a * g ∈ S) :
    ¬ A₁ ≤ A₂ ∧ ¬ A₂ ≤ A₁ := by
  have hn : ¬ (A₁ ≤ A₂ ∨ A₂ ≤ A₁) := by
    intro hn
    exact hg (transporter_mem_intersectionGenerated ha hne
      ((h.closed_of_nested hn).2 a ha g (mem_top _) hS))
  exact ⟨fun hle => hn (Or.inl hle), fun hle => hn (Or.inr hle)⟩

/-- Application to the contrary-fusion consumer: its literal transporter
witness supplies source (b) and (c), including their original ambient maps.
The separate centralizer-induction assertion (d) remains with its producer. -/
theorem Hypotheses.local_pair_geometry_of_escaping_conjugate (h : Hypotheses S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (hne : a ≠ 1)
    (hg : g ∉ intersectionGenerated A₁ A₂) (hS : g⁻¹ * a * g ∈ S) :
    (∀ s ∈ S, (conjugate A₁ s = A₁ ∧ conjugate A₂ s = A₂) ∨
      (conjugate A₁ s = A₂ ∧ conjugate A₂ s = A₁)) ∧
    ∀ X : Subgroup G, (X ≤ A₁ ∨ X ≤ A₂) → 2 < Nat.card X →
      UniqueSubgroupConjugateMembership (intersectionGenerated A₁ A₂) X := by
  obtain ⟨hn₁, hn₂⟩ := h.nonnested_of_escaping_conjugate ha hne hg hS
  exact ⟨h.permutes_pair_of_nonnested hn₁ hn₂, h.unique_large⟩

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
