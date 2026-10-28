module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.Components
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.NormalExclusion
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Simplicity.ProperSupplement

/-!
# The simple normal subgroup in GLS Lemma 4.9

Choose an actual minimal nontrivial normal subgroup. Two-central generation
and the trivial solvable radical make it simple, and the odd-order theorem
makes its order even. Fusion and Z-star exclude every normal subgroup in M;
the local strong-embedding argument then shows that adjoining z gives G.
If z already lay in that subgroup, G itself would be simple.

All intermediate premises are discharged from the literal preliminary and
local hypotheses supplied by the source consumer.
Source: GLS, Volume 4, Chapter 2, Lemma 4.9.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII Subgroup
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The simple normal subgroup, its even order, and the outer involution
supplement in the nonsimple branch of Lemma 4.9. -/
public theorem simple_normal_subgroup_of_nonsimple
    (h : IsProductDisconnected Z M) (hgen : closure Z = ⊤)
    (hclass : ∀ x ∈ Z, ∀ z ∈ Z, IsConj x z)
    (htwo : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hf : ∃ S : Sylow 2 G, (S : Subgroup G) ≤ M ∧ ControlsFusionIn M (S : Subgroup G))
    (hsol : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hlocal : ∀ H : Subgroup G, H ≠ ⊤ → ¬ H ≤ M →
      (∃ s ∈ Z, s ∈ H ∧ s ∈ M) →
      IsStronglyEmbedded ((M.comap H.subtype).comap
        (closure (H.subtype ⁻¹' Z)).subtype))
    {z : G} (hz : z ∈ Z) (hzM : z ∈ M) (hnot : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ IsSimpleGroup N ∧ Even (Nat.card N) ∧
      N ⊔ zpowers z = ⊤ ∧ z ∉ N := by
  have hrad : solvableRadical G = ⊥ := hsol _ inferInstance inferInstance
  have htop : (⊤ : Subgroup G) ≠ ⊥ := by
    intro he
    exact (h.involutions z hz).ne_one (mem_bot.mp (he ▸ mem_top z))
  obtain ⟨N, hN, _, hNne, hmin⟩ := exists_minimal_normal_le (⊤ : Subgroup G) inferInstance htop
  let : N.Normal := hN
  let : IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases he : K = ⊥
    · exact Or.inl he
    · exact Or.inr (hmin K hK hKN he)⟩
  let : IsSimpleGroup N := minimal_normal_simple_of_twoCentral_generation hrad hgen
    (fun w hw => let ⟨S, _, hS⟩ := htwo w hw; ⟨S, hS⟩) N hNne
  obtain ⟨S, hSM, hfus⟩ := hf
  have hnormal : ∀ K : Subgroup G, K.Normal → K ≤ M → K = ⊥ := by
    intro K hK hKM
    let : K.Normal := hK
    exact normal_eq_bot_of_productDisconnected_fusion h hgen S hSM hfus hrad K hKM
  have hsup := simple_normal_sup_zpowers_eq_top h hgen hclass hrad hnormal hlocal hz hzM N
  refine ⟨N, hN, inferInstance,
    even_card_of_nontrivial_normal_of_radicalFree hrad N hNne, hsup, ?_⟩
  intro hzN
  have hNtop : N = ⊤ := by simpa only [sup_of_le_left (zpowers_le.mpr hzN)] using hsup
  apply hnot
  have hs : IsSimpleGroup (⊤ : Subgroup G) := hNtop ▸ (inferInstance : IsSimpleGroup N)
  exact (Subgroup.topEquiv.isSimpleGroup_congr).mp hs

end BenderSuzuki.ZD
