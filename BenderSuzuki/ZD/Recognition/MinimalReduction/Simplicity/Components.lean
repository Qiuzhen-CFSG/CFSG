module

public import BenderSuzuki.ZD.Recognition.Interfaces
public import Theory.GroupTheory.CComponent.SylowCentral
public import FeitThompson.ChiefFactors.Core
public import FeitThompson.FinalTheorem

/-!
# The component step in the ZD simplicity reduction

The odd-order theorem gives even order for every C-component. Hence an element
centralizing a Sylow two-subgroup normalizes each component. If such elements
generate the ambient group, every component is normal. A nontrivial minimal
normal subgroup is nonsolvable when the radical is trivial; choose a component
inside it and use minimality to identify it with that component. Radical-free
components are simple. This avoids needing a chosen direct-product decomposition.

Source: GLS, Volume 4, Chapter 2, Lemma 4.9, first paragraph, citing Volume 1,
(4.6); `refs/KGroup/GLS4/Chapter2.tex`, line 672.
-/

open Subgroup
namespace BenderSuzuki.ZD
variable {G : Type*} [Group G] [Finite G] {Z : Set G}

/-- A Sylow-central element normalizes each C-component of a radical-free group. -/
public theorem component_normalized_of_twoCentral {L : Subgroup G}
    (hL : L.IsCComponent) (hrad : solvableRadical G = ⊥)
    (S : Sylow 2 G) {z : G} (hz : ∀ s : S, Commute z (s : G)) :
    z ∈ normalizer (L : Set G) := by
  apply hL.mem_normalizer_of_centralizes_sylow hrad _ S hz
  by_contra hdiv
  exact hL.not_isSolvable (odd_order_theorem L
    (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hdiv)))

/-- If Sylow-central elements generate a radical-free group, its C-components
are normal individually. -/
public theorem component_normal_of_twoCentral_generation {L : Subgroup G}
    (hL : L.IsCComponent) (hrad : solvableRadical G = ⊥)
    (hgen : closure Z = ⊤)
    (hc : ∀ z ∈ Z, ∃ S : Sylow 2 G, ∀ s : S, Commute z (s : G)) :
    L.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (closure_le _).mpr
  intro z hz
  obtain ⟨S, hS⟩ := hc z hz
  exact component_normalized_of_twoCentral hL hrad S hS

/-- A nontrivial minimal normal subgroup is simple when the radical is trivial
and Sylow-central elements generate the group. -/
public theorem minimal_normal_simple_of_twoCentral_generation
    (hrad : solvableRadical G = ⊥) (hgen : closure Z = ⊤)
    (hc : ∀ z ∈ Z, ∃ S : Sylow 2 G, ∀ s : S, Commute z (s : G))
    (A : Subgroup G) [A.Normal] [IsMinimalNormal A] (hne : A ≠ ⊥) :
    IsSimpleGroup A := by
  have hns : ¬ Group.IsSolvable A := by
    intro hs
    exact hne (le_bot_iff.mp (hrad ▸ le_solvableRadical A inferInstance hs))
  obtain ⟨L, hL⟩ := exists_isCComponent_of_not_isSolvable hns
  have hLA := hL.map_subtype (inferInstance : A.Normal).isSubnormal
  let := component_normal_of_twoCentral_generation hLA hrad hgen hc
  have he := IsMinimalNormal.eq_of_ne_bot A (L.map A.subtype)
    (map_subtype_le L) hLA.ne_bot
  exact he ▸ hLA.isSimpleGroup_of_solvableRadical_eq_bot hrad

/-- The odd core of a finite radical-free group is trivial. -/
public theorem oddCore_eq_bot_of_radicalFree
    {H : Type*} [Group H] [Finite H] (hrad : solvableRadical H = ⊥) :
    pPrimeCore 2 H = ⊥ := by
  apply le_bot_iff.mp
  rw [← hrad]
  apply le_solvableRadical _ inferInstance
  exact odd_order_theorem _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)

/-- Every nontrivial normal subgroup of a radical-free finite group has even order. -/
public theorem even_card_of_nontrivial_normal_of_radicalFree
    (hrad : solvableRadical G = ⊥) (A : Subgroup G) [A.Normal] (hne : A ≠ ⊥) :
    Even (Nat.card A) := by
  by_contra hodd
  have hs := odd_order_theorem A (Nat.not_even_iff_odd.mp hodd)
  exact hne (le_bot_iff.mp (hrad ▸ le_solvableRadical A inferInstance hs))

end BenderSuzuki.ZD
