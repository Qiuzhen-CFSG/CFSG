module
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.MarkedActions
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.CyclicFixed
public import CFSG.Quasithin.ChapterF.Section06.Noncyclic.SourceImplication.SupercriticalAction

/-!
# The class bound and concrete residual models in F.6.16

The cross-core involutions give the actual marked cubic action. Apply the
universal A.1.31(1) implication to the original SQTK cover and lift fixed
points to discharge every quotient fixed-subgroup bound. The marked
lower-central-series theorem now gives centrality of the derived subgroup.
Cubic generation supplies first omega, and the source rank bound supplies
rank two, so the proved A.1.24 theorem identifies the residual with E₉ or
the prime Heisenberg group.

These results assume the three-group branch explicitly. They do not assert
the full F.6.16 disjunction or identify the extension action. The final
source assembly must still exclude the other branch and identify G.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
Lemma F.6.16, printed p.308 (1 March 2004 manuscript).
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterF.Noncyclic
universe u
variable {G Ghat : Type u} [Group G] [Finite G] [Group Ghat] [Finite Ghat]
  {K : GroupClass.{u}} {G₁ G₂ : Subgroup G}

/-- The complete class bound in the four-group branch, with the fixed-point
premise discharged by the original cover and the exact universal A.1.31 input. -/
theorem residual_class_two_of_cover
    (source : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hL : IsPGroup 3 (pResidual 2 G)) (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    _root_.commutator (pResidual 2 G) ≤ center (pResidual 2 G) := by
  obtain ⟨t₁, t₂, _, _, ho₁, ho₂, _, hm⟩ := exists_residual_cubic_marking h hcore hL hnot
  exact hm.commutator_le_center hL (residual_frattini_plane h hL hn).1
    (residual_frattini_eq_derived h hL)
    (quotientCyclicFixed_of_fixed hL _ _ hm.left_sq hm.right_sq
      (residual_involution_fixed_cyclic source hhat e hcore hL t₁ ho₁)
      (residual_involution_fixed_cyclic source hhat e hcore hL t₂ ho₂))

/-- Cubic generation supplies the first-omega hypothesis of A.1.24. -/
theorem residual_omega_one_eq_top (h : IsGoldschmidtTriple G₁ G₂)
    (hL : IsPGroup 3 (pResidual 2 G)) : omega₁ (pResidual 2 G) (p := 3) = ⊤ := by
  let L := pResidual 2 G
  let A := ((pResidual 2 G₁).map G₁.subtype).subgroupOf L
  let B := ((pResidual 2 G₂).map G₂.subtype).subgroupOf L
  have hgen : A ⊔ B = ⊤ := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (map_pResidual_le 2 G₁.subtype),
      map_subgroupOf_eq_of_le (map_pResidual_le 2 G₂.subtype),
      ← MonoidHom.range_eq_map, range_subtype]
    exact h.twoResidual_eq_sup.symm
  have hcardA : Nat.card A = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_pResidual_le 2 G₁.subtype)).toEquiv]
    exact local_residual_card_three h hL
  have hcardB : Nat.card B = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (map_pResidual_le 2 G₂.subtype)).toEquiv]
    exact local_residual_card_three h.symm hL
  have hle (C : Subgroup L) (hc : Nat.card C = 3) : C ≤ omega₁ L (p := 3) := by
    intro x hx
    apply Subgroup.subset_closure
    change x ^ (3 ^ 1) = 1
    have he := pow_card_eq_one' (x := (⟨x, hx⟩ : C))
    rw [hc] at he
    exact congrArg Subtype.val he
  apply top_unique
  rw [← hgen]
  exact sup_le (hle A hcardA) (hle B hcardB)

/-- A.1.24 now identifies the residual as the actual elementary plane or
prime Heisenberg group; no exponent, class or rank premise remains. -/
theorem residual_models_of_cover
    (source : SectionCentralizerInput.{u,u})
    (hhat : IsSQTK K Ghat) (e : G ≃* (Ghat ⧸ pPrimeCore 3 Ghat))
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hL : IsPGroup 3 (pResidual 2 G)) (hn : ¬ IsCyclic (pCore 3 G))
    (hnot : ¬ Nonempty ((G₁ ⊓ G₂ : Subgroup G) ≃* Multiplicative (ZMod 2))) :
    (Nat.card (pResidual 2 G) = 9 ∧ Nonempty ((pResidual 2 G) ≃*
      (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)))) ∨
    (Nat.card (pResidual 2 G) = 27 ∧ IsExtraspecial 3 (pResidual 2 G) ∧
      Nonempty ((pResidual 2 G) ≃* HeisenbergPrime 3)) := by
  have hrle := (primeRank_subgroup_le 3 (pResidual 2 G)).trans (three_rank_le_two_of_cover hhat e)
  have hr : primeRank 3 (pResidual 2 G) = 2 := by
    have hgt : ¬ primeRank 3 (pResidual 2 G) ≤ 1 := by
      intro hr1
      apply residual_nocyclic hn
      apply hL.isCyclic_of_odd_of_elementary_card_le (by decide)
      intro E hE
      let : IsElementaryAbelian 3 E := hE
      exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E
    omega
  exact ChapterA.lemma_A_1_24 (by decide : 3 ≠ 2) hL (residual_omega_one_eq_top h hL)
    (residual_class_two_of_cover source hhat e h hcore hL hn hnot) hr

end CFSG.Quasithin.ChapterF.Noncyclic
