module

public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.Chapter2.Section01To03.Elementary

/-!
# Selecting a characteristic-two overgroup in the A₈ branch

The two proper overgroups in C₂ × S₈ generate that group, so at least one
lies outside M. If their common Sylow subgroup U is in β, this constructs
an actual local pair. The half-Sylow upper bound on members of Γ then puts
the selected overgroup in the subscript-star family and hence in Γe0.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569. Membership of U in β
and the upper bound are the earlier source inputs 2.3.10 and 2.3.7(1).
The intrinsic C₂ × S₈ geometry must construct the two overgroups and prove
their characteristic-two properties; none is inferred from a family label.
-/

namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The selection step uses the genuine Chapter 1 characteristic-two family
and constructs Γe0 membership from local pairs and an order bound. -/
public theorem exists_gammaEvenZero_of_generating_overgroups
    (M I U L₁ L₂ : Subgroup G)
    (hgen : L₁ ⊔ L₂ = I) (hout : ¬ I ≤ M)
    (hU : U ∈ beta M)
    (hUL₁ : U ≤ L₁) (hUL₂ : U ≤ L₂)
    (hL₁ : L₁ ∈ Chapter1.He G) (hL₂ : L₂ ∈ Chapter1.He G)
    (hcore₁ : twoCore L₁ ≠ ⊥) (hcore₂ : twoCore L₂ ≠ ⊥)
    (hbound : ∀ J ∈ gamma (Chapter1.He G) M, twoPart J ≤ Nat.card U) :
    ∃ L ∈ ({L₁, L₂} : Set (Subgroup G)), L ∈ gammaEvenZero (Chapter1.He G) M := by
  have hselect : ∀ L : Subgroup G, U ≤ L → L ∈ Chapter1.He G →
      twoCore L ≠ ⊥ → ¬ L ≤ M → L ∈ gammaEvenZero (Chapter1.He G) M := by
    intro L hUL hL hcore hLM
    have hp : (U, L) ∈ localPairs (Chapter1.He G) M := ⟨hU, hL, hcore, hUL, hLM⟩
    have hγ := localPair_snd_mem_gamma hp
    have hmax : L ∈ gammaMax (Chapter1.He G) M :=
      ⟨hγ, fun J hJ => (hbound J hJ).trans (beta_card_le_twoPart hU hUL)⟩
    exact ⟨Or.inr hmax, hL⟩
  by_cases h₁ : L₁ ≤ M
  · have h₂ : ¬ L₂ ≤ M := fun h₂ => hout (hgen ▸ sup_le h₁ h₂)
    exact ⟨L₂, by simp, hselect L₂ hUL₂ hL₂ hcore₂ h₂⟩
  · exact ⟨L₁, by simp, hselect L₁ hUL₁ hL₁ hcore₁ h₁⟩

end CFSG.Quasithin.Chapter2.A6ShadowRankOne
