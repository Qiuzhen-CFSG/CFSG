module

public import Theory.GroupTheory.SylowCentralizerUniqueConjugate
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source

/-!
# The Sylow upgrade in original 13.1.12(3)

For M=N_G(L) and the literal radical Ξ_p(L), original 13.1.11 supplies
unique conjugate containment for M∩C_G(u) from its radical action.
Consequently the selected local centralizer Sylow subgroup T∩C_G(u)
is Sylow in the full centralizer C_G(u).

The earlier model calculations of 13.1.10--12 remain explicit: selection of
u with local Sylow centralizer, its index at most two, irreducibility of the
radical action, and containment of centralizers of T-central conjugates.
This establishes the Sylow upgrade, not the subsequent C_G(u)≤M conclusion.

Source: Aschbacher--Smith, 13.1.12(3), printed p.873, using 13.1.11, p.872.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerSylow
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual selected subgroup T∩C_G(u) is Sylow in C_G(u).
The unique-conjugate premise is discharged for Ξ_p(L) by original 13.1.11. -/
theorem source_centralizer_sylow
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (u : G) (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hlocal : IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)))
    (hindex : ((centralizer ({u} : Set G)).subgroupOf (T : Subgroup G)).index ≤ 2)
    (hcentral : ∀ g : G,
      (T : Subgroup G) ≤ centralizer ({g * u * g⁻¹} : Set G) →
        centralizer ({g * u * g⁻¹} : Set G) ≤ normalizer (L : Set G))
    (hXMu : XiP p L ≤ normalizer (L : Set G) ⊓ centralizer ({u} : Set G))
    (hirr : ∀ A : Subgroup (XiFrattiniQuotient (XiP p L)),
      (∀ s : (normalizer (L : Set G) ⊓ centralizer ({u} : Set G) : Subgroup G),
        ∀ a ∈ A, xiFrattiniAction
          (normalizer (L : Set G) ⊓ centralizer ({u} : Set G)) (XiP p L)
          (XiP_invariant p inf_le_left) s a ∈ A) → A = ⊥ ∨ A = ⊤) :
    IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (centralizer ({u} : Set G)) := by
  let Mu := normalizer (L : Set G) ⊓ centralizer ({u} : Set G)
  have hlocal' : ∃ S : Sylow 2 Mu,
      (S : Subgroup Mu) = (T : Subgroup G).subgroupOf Mu := by
    obtain ⟨Q, hQ⟩ := hlocal
    refine ⟨Q, map_injective Mu.subtype_injective ?_⟩
    rw [hQ, subgroupOf_map_subtype]
    exact le_antisymm (fun x hx => ⟨hx.1, hTM hx.1, hx.2⟩)
      (fun x hx => ⟨hx.1, hx.2.2⟩)
  obtain ⟨S, hS⟩ := T.exists_sylow_centralizer_eq_of_unique_conjugate
    (normalizer (L : Set G)) hTM u hlocal' hindex hcentral (by
      intro g hg
      exact (RadicalConjugateRigidity.maximal_radical_unique_conjugate
        hG T hL hn ho hd _ hXMu inf_le_left hirr g hg).1)
  refine ⟨S, ?_⟩
  rw [hS, subgroupOf_map_subtype]

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerSylow
