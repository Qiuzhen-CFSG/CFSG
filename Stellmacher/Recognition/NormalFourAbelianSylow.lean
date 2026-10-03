module

public import Stellmacher.MainDefs
public import Theory.GroupTheory.PGroup.RankTwoFour
public import Theory.GroupTheory.PGroup.AbelianOmegaFrattini
public import Theory.GroupTheory.AbelianSylowAutomizer
public import Theory.GroupTheory.PGroup.AbelianRankTwoHomocyclic
public import Theory.GroupTheory.Recognition.HomocyclicSylow
public import Theory.PPrimeCore

/-!
# The abelian normal-four Sylow reduction

The rank bound makes the given elementary four-group exactly first omega
of an abelian Sylow two-subgroup S. Squaring then shows that S has Klein
four Frattini quotient. Simplicity and Burnside transfer force the
normalizer's automorphism group on S to have order three.

The order-three automorphism makes S rank-two homocyclic. Brauer's
homocyclic Sylow theorem makes S normal if its exponent is at least four,
contradicting simplicity and nonsolvability. Thus S is elementary abelian
of order four. This proves the abelian case of Janko–Thompson,
Math. Z. 113 (1970), §6, p.394, without needing the N₂ hypothesis.
The saved source is
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`;
the case ordering is recorded in `normal-four-case-split.md` beside it.

The resulting four-group belongs to the dihedral alternative, as implemented by
`rank_two_sylow_alternative_of_elementary_card_four` in
`Stellmacher.Recognition.NormalFourSylowReduction`.
-/

namespace Stellmacher.Recognition.NormalFourAbelianSylow

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- The supplied elementary four-group is the entire first omega subgroup. -/
public theorem omega_one_eq_four
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    omega₁ S (p := 2) = E := by
  exact omega_one_eq_of_central_four_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
    (by rw [center_eq_top]; exact le_top)

/-- The Frattini quotient of the abelian Sylow subgroup is a Klein four-group. -/
public theorem frattini_quotient_isKleinFour
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    IsKleinFour (S ⧸ frattini S) := by
  apply S.isPGroup'.isKleinFour_frattini_quotient_of_card_omega_one_eq_four
  rw [omega_one_eq_four hrank S E hE, hE]

private theorem sylow_ne_bot
    (S : Sylow 2 G) (E : Subgroup S) (hE : Nat.card E = 4) :
    (S : Subgroup G) ≠ ⊥ := by
  intro hb
  have hle : Nat.card E ≤ Nat.card S := card_le_card_group E
  have hc : Nat.card S = 1 := by rw [hb, card_bot]
  omega

/-- The normalizer automizer has order three under the original rank bound. -/
public theorem card_automizer_eq_three [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    Nat.card (S : Subgroup G).normalizerMonoidHom.range = 3 := by
  let : IsKleinFour (S ⧸ frattini S) := frattini_quotient_isKleinFour hrank S E hE
  exact S.card_normalizer_action_eq_three_of_simple hns (sylow_ne_bot S E hE)

/-- An order-three automorphism is available for the homocyclic reduction. -/
public theorem exists_order_three_automorphism [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    ∃ a : MulAut S, orderOf a = 3 := by
  let : IsKleinFour (S ⧸ frattini S) := frattini_quotient_isKleinFour hrank S E hE
  obtain ⟨a, _, ha⟩ :=
    S.exists_order_three_normalizer_automorphism_of_simple hns (sylow_ne_bot S E hE)
  exact ⟨a, ha⟩

/-- The given four-group already forces the simple ambient group to have trivial odd core. -/
public theorem oddCore_eq_bot [IsSimpleGroup G]
    (S : Sylow 2 G) (E : Subgroup S) (hE : Nat.card E = 4) :
    pPrimeCore 2 G = ⊥ := by
  rcases (pPrimeCore_normal (p := 2) (G := G)).eq_bot_or_eq_top with hb | ht
  · exact hb
  · have hc := pPrimeCore_coprime_card (p := 2) (G := G)
    rw [ht, card_top] at hc
    have hd : 2 ∣ Nat.card G := (by norm_num : 2 ∣ 4).trans
      ((hE ▸ E.card_subgroup_dvd_card).trans (S : Subgroup G).card_subgroup_dvd_card)
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hc hd).elim

omit [Finite G] in
/-- Simplicity supplies the no-index-two hypothesis in Brauer's theorem. -/
public theorem no_normal_index_two [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hb | ht
  · have hc : Nat.card G = 2 := by simpa only [hb, index_bot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hc
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp only [ht, index_top] at hi
    omega

/-- A nontrivial abelian Sylow subgroup cannot be normal in a nonsolvable
simple group. This contradicts the conclusion of Brauer's homocyclic theorem. -/
public theorem not_normal [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) (hE : Nat.card E = 4) :
    ¬ (S : Subgroup G).Normal := by
  intro hn
  rcases hn.eq_bot_or_eq_top with hb | ht
  · exact sylow_ne_bot S E hE hb
  · have hcomm : IsMulCommutative (⊤ : Subgroup G) :=
      ht ▸ (inferInstance : IsMulCommutative S)
    let : IsMulCommutative (⊤ : Subgroup G) := hcomm
    exact hns (Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom)
      Subgroup.topEquiv.surjective)

/-- An elementary abelian Sylow containing the supplied four-group equals it. -/
public theorem eq_top_and_card_four_of_elementary
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsElementaryAbelian 2 S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    E = ⊤ ∧ Nat.card S = 4 := by
  have ht : omega₁ S (p := 2) = ⊤ := by
    apply top_unique
    intro x _
    exact Subgroup.subset_closure
      (by simpa only [Set.mem_ofPred_eq, pow_one] using (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 S) x))
  have he : E = ⊤ := (omega_one_eq_four hrank S E hE).symm.trans ht
  exact ⟨he, by simpa only [he, card_top] using hE⟩

/-- Once the Sylow order is four, the supplied elementary four-group fills it. -/
public theorem elementary_of_card_four
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hS : Nat.card S = 4) : IsElementaryAbelian 2 S := by
  have he : E = ⊤ := eq_of_le_of_card_ge le_top (by simp only [card_top, hE, hS, le_refl])
  refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  exact elemPow_eq_one_of_isElementaryAbelian (A := E) x (by rw [he]; trivial)

/-- The abelian Sylow case of the normal-four reduction: the Sylow subgroup
is an elementary four-group. The ambient N₂ hypothesis is not needed. -/
public theorem card_eq_four_and_elementary [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) [IsMulCommutative S]
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    Nat.card S = 4 ∧ IsElementaryAbelian 2 S := by
  have hfour : Nat.card (omega₁ S (p := 2)) = 4 := by
    rw [omega_one_eq_four hrank S E hE, hE]
  obtain ⟨a, ha⟩ := exists_order_three_automorphism hns hrank S E hE
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    S.isPGroup'.exists_equiv_prod_self_zmod_of_orderOf_aut_eq_three hfour a ha
  have hn1 : n = 1 := by
    by_contra hne
    exact not_normal hns S E hE
      (normal_homocyclic_sylow (oddCore_eq_bot S E hE) S (by omega) e)
  subst n
  have hS : Nat.card S = 4 := by
    simpa [Nat.card_prod] using Nat.card_congr e.toEquiv
  exact ⟨hS, elementary_of_card_four S E hE hS⟩

end Stellmacher.Recognition.NormalFourAbelianSylow
