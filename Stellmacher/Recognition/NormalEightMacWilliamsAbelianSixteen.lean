module

public import Theory.GroupTheory.PGroup.AbelianCriticalNormalizerAction
public import Theory.GroupTheory.ElementaryEightIndexTwoGeometry
public import Theory.GroupTheory.ElementaryEightIndexTwoFusion
public import Theory.GroupTheory.PGroup.AbelianCriticalSixteenFixedAction
public import Theory.GroupTheory.PGroup.C4SquareCubicOutsideGeometry
public import Theory.GroupTheory.PGroup.AbelianCriticalSixteenExtension
public import Theory.GroupTheory.PGroup.C4SquareCubicInsideGeometry

/-!
# The order-sixteen abelian critical branch

The reduction supplies C₄ × C₄ coordinates and a free cubic action realized
in the ambient Sylow normalizer. If an involution is noncentral, the cubic
congruence calculation constructs an inverting extension with a core of
order sixty-four and index two. Its split/nonsplit involution calculation
gives the three elementary-eight normalizer cases in
`ElementaryEightIndexTwoGeometry`.

Ambient fusion exclusion, proved by `ElementaryEightIndexTwoGeometry.no_fusion`,
then lets transfer contradict simplicity. The final theorem discharges all
structural and fusion premises under the original hypotheses. In particular
no purely local index-two dichotomy for the critical subgroup is used.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, Lemma 3 and
(xxi)–(xxv), printed pp.380–385, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup

namespace Stellmacher.Recognition.NormalEightMacWilliamsAbelianSixteen

private theorem no_normal_index_two
    {G : Type*} [Group G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (K : Subgroup G) (hK : K.Normal) : K.index ≠ 2 := by
  intro hi
  rcases hK.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa only [hbot, index_bot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    let : CommGroup G := IsCyclic.commGroup
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp only [htop, index_top] at hi
    omega

/-- Order sixteen specializes the homocyclic reduction to C₄ × C₄. -/
public theorem nonempty_equiv_c4_square
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hcard : Nat.card C = 16) :
    Nonempty (C ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  have hAut := S.not_isPGroup_mulAut_of_normalizer_ne_sup_centralizer hnorm
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    hC.homocyclic_large_of_not_isPGroup_mulAut S.isPGroup' hAut hnonab hno hZ
  have hc : 2 ^ n * 2 ^ n = 16 := by
    simpa [Nat.card_prod, Nat.card_eq_fintype_card] using
      (Nat.card_congr e.toEquiv).symm.trans hcard
  have hn2 : n = 2 := by
    by_contra hne
    have hn3 : 3 ≤ n := by omega
    have hlarge : 8 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < 2) hn3
    nlinarith
  subst n
  exact ⟨e⟩

/-- The local geometry and ambient fusion inputs suffice for the requested
centrality conclusion. Both inputs remain explicit in this reduction. -/
public theorem involution_mem_center_of_structure_and_fusion
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hcard : Nat.card C = 16)
    (hstructure : ∀ (_e : C ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
      (a : MulAut S), orderOf a = 3 → (∀ c ∈ C, a c = c → c = 1) →
      (∀ x : S, orderOf x = 2 → x ∈ center S) ∨
        ∃ (R : Subgroup S) (t : S), ElementaryEightIndexTwoGeometry R t)
    (hfusion : ∀ (R : Subgroup S) (t : S), ElementaryEightIndexTwoGeometry R t →
      ∀ u : S, u ∈ R → orderOf u = 2 → ¬ IsConj (t : G) (u : G)) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  obtain ⟨e⟩ := nonempty_equiv_c4_square S hnonab hZ hno hnorm C hC hcard
  obtain ⟨g, hg, hfree⟩ := S.exists_normalizer_order_three_free_on_abelian_critical
    hnorm hC (hC.card_omega_one_eq_four hno hZ)
  rcases hstructure e ((S : Subgroup G).normalizerMonoidHom g) hg hfree with
    hcentral | ⟨R, t, hgeometry⟩
  · exact hcentral
  · exact (hgeometry.false_of_no_fusion S (no_normal_index_two hns)
      (hfusion R t hgeometry)).elim

/-- The proved ambient fusion theorem reduces order-sixteen centrality to
local extension geometry alone. -/
public theorem involution_mem_center_of_structure
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hcard : Nat.card C = 16)
    (hstructure : ∀ (_e : C ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)))
      (a : MulAut S), orderOf a = 3 → (∀ c ∈ C, a c = c → c = 1) →
      (∀ x : S, orderOf x = 2 → x ∈ center S) ∨
        ∃ (R : Subgroup S) (t : S), ElementaryEightIndexTwoGeometry R t) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  exact involution_mem_center_of_structure_and_fusion hns S hnonab hZ hno hnorm C hC
    hcard hstructure (fun _ _ h => h.no_fusion S)

/-- Every involution is central when the abelian critical subgroup has order
sixteen. A noncentral involution would yield the cubic inverting extension;
its elementary-eight geometry and ambient transfer contradict simplicity. -/
public theorem involution_mem_center
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (S : Sylow 2 G)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnorm : normalizer (S : Set G) ≠ (S : Subgroup G) ⊔ centralizer (S : Set G))
    (C : Subgroup S) (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
    (hcard : Nat.card C = 16) :
    ∀ x : S, orderOf x = 2 → x ∈ center S := by
  apply involution_mem_center_of_structure hns S hnonab hZ hno hnorm C hC hcard
  intro e a ha hfree
  by_cases hcentral : ∀ x : S, orderOf x = 2 → x ∈ center S
  · exact Or.inl hcentral
  · obtain ⟨R, t, h⟩ := hC.exists_cubicInvertingExtension_of_c4_square
      S.isPGroup' hnonab hno hZ e a ha hfree hcentral
    exact Or.inr ⟨R, t, h.geometry hC hno hZ e ha hfree⟩

end Stellmacher.Recognition.NormalEightMacWilliamsAbelianSixteen
