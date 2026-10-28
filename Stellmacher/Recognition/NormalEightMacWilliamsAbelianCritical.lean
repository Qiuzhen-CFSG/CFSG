module

public import Theory.GroupTheory.SylowPGroupAutomizer
public import Theory.GroupTheory.PGroup.NormalEightAbelianCriticalAction
public import Theory.GroupTheory.PGroup.AbelianCriticalNormalizerAction
public import Theory.GroupTheory.PGroup.AbelianCriticalLargeExponent
public import Stellmacher.Recognition.NormalEightMacWilliamsAbelianIndexTwo
public import Stellmacher.Recognition.NormalEightMacWilliamsAbelianSixteen

/-!
# Involution centrality with an abelian critical subgroup

The nontrivial outer normalizer action rules out a two-group automorphism
group for the Sylow subgroup. An abelian critical subgroup has first omega
of order four, so its Klein four Frattini quotient detects an order-three
automorphism. The critical subgroup is consequently homocyclic, with both
cyclic factors of order at least four. The order-three automorphism fixes
no nonidentity element of that subgroup.

The stronger reduction realizes this automorphism by an element of the
ambient Sylow normalizer, so it can also be used in fusion arguments.

For exponent four, the order-sixteen extension and ambient fusion theorem
gives centrality. For exponent at least eight, the large-exponent theorem
makes the critical subgroup have index two, and the index-two fusion theorem
places every involution in its central first omega. Thus all Sylow
involutions are central under the nonsolvable simple ambient hypotheses.

Source: MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3, quoted in Janko–Thompson,
Math. Z. 113 (1970), Theorem 1.3, printed p.386, in
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightMacWilliamsAbelianCritical

/-- The homocyclic reduction with a cubic action realized by the ambient
normalizer. Only the induced automorphism is required to have order three. -/
public theorem homocyclic_critical_normalizer_action
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C] :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty
      (C ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n))))) ∧
    (∃ g : normalizer (S : Set G),
      orderOf ((S : Subgroup G).normalizerMonoidHom g) = 3 ∧
      ∀ c ∈ C, (S : Subgroup G).normalizerMonoidHom g c = c → c = 1) := by
  have hAut := S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm
  exact ⟨hC.homocyclic_large_of_not_isPGroup_mulAut S.isPGroup' hAut hnonab hno hZ,
    S.exists_normalizer_order_three_free_on_abelian_critical hnorm hC
      (hC.card_omega_one_eq_four hno hZ)⟩

/-- The abelian critical case supplies a homocyclic subgroup of exponent at
least four and an order-three automorphism acting freely on that subgroup. -/
public theorem homocyclic_critical_action
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C] :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty
      (C ≃* (Multiplicative (ZMod (2^n)) × Multiplicative (ZMod (2^n))))) ∧
    (∃ a : MulAut S, orderOf a = 3 ∧ ∀ c ∈ C, a c = c → c = 1) := by
  obtain ⟨hmodel, g, hg, hfree⟩ :=
    homocyclic_critical_normalizer_action S hnonab hZ hno hnorm C hC
  exact ⟨hmodel, (S : Subgroup G).normalizerMonoidHom g, hg, hfree⟩

/-- Every Sylow involution is central in the abelian critical-subgroup branch.
The homocyclic exponent separates the order-sixteen fusion case from the
large-exponent index-two case. -/
public theorem involution_mem_center
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C] :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  obtain ⟨⟨n, hn, ⟨e⟩⟩, a, ha, hfree⟩ :=
    homocyclic_critical_action S hnonab hZ hno hnorm C hC
  by_cases hn2 : n = 2
  · subst n
    have hcard : Nat.card C = 16 := by
      simpa [Nat.card_prod, Nat.card_eq_fintype_card] using Nat.card_congr e.toEquiv
    exact NormalEightMacWilliamsAbelianSixteen.involution_mem_center
      hns S hnonab hZ hno hnorm C hC hcard
  · have hi : C.index = 2 := hC.index_eq_two_of_large_homocyclic
      S.isPGroup' hnonab hno hZ n (by omega) e a ha hfree
    exact NormalEightMacWilliamsAbelianIndexTwo.involution_mem_center_of_index_two
      hns S hnonab hZ hno hnorm C hC hi

end Stellmacher.Recognition.NormalEightMacWilliamsAbelianCritical
