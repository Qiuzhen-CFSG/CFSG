module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleCubicNormalizer

public import Theory.GroupTheory.PermutingCubicCentralizerImage
public import Theory.GroupTheory.CyclicThreeNormalizer

/-!
# A Sylow inverter centralizing the selected cubic lift

In the original Goldschmidt quotient, the opposite vertex's four-core lies
in the selected PSL₂ component. It centralizes the complementary cubic,
but cannot centralize the Borel residual: otherwise both vertices would
normalize that nontrivial two-core, contradicting the zero ambient two-core.
Thus the common Sylow contains an element separating these two cubic actions.

Prime-free fixed-point lifting inside the permuting cubic Sylow supplement
puts this element in the original C_T(D), with the same D and the same
O₃′ quotient map. Its nontrivial action on the Borel residual of order three
is inversion. No change of cubic lift or quotient is made.

The subsequent comparison with the L/O₂(L) action and normal-closure
contradiction remain with the original source assembly. Source:
Aschbacher--Smith 13.2.7, printed pp.883--884; F.6.17(2), p.309.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization

private theorem opposite_core_moves_residual
    {M : Type*} [Group M] [Finite M] {A B : Subgroup M}
    (h : ChapterF.IsGoldschmidtTriple A B) (hz : pCore 2 M = ⊥)
    (hne : B.pCoreIn 2 ≠ ⊥) :
    ¬ B.pCoreIn 2 ≤ centralizer ((pResidual 2 A).map A.subtype : Set M) := by
  intro hc
  have hBN : B ≤ normalizer (B.pCoreIn 2 : Set M) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hAN : A ≤ normalizer (B.pCoreIn 2 : Set M) := by
    rw [←h.left_residual_sup_intersection]
    exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans hBN)
  let : (B.pCoreIn 2).Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [←h.generated]
    exact sup_le hAN hBN))
  have hh : B.pCoreIn 2 ≤ pCore 2 M := le_sSup ⟨inferInstance,isPGroup_pCoreIn 2 B⟩
  exact hne (bot_unique (hh.trans hz.le))

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H : Subgroup G}

/-- The original quotient Sylow separates the two cubic actions. -/
theorem single_quotient_separating_element
    (c : SingleQuotientProduct T L H)
    (hg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥) :
    let J := H ⊔ borelResidual T L
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    let A := ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q
    let B := (H.subgroupOf J).map q
    ∃ t : J ⧸ pPrimeCore 3 J, t ∈ A ⊓ B ∧
      t ∈ centralizer (c.cubic_lift.map q : Set _) ∧
      t ∉ centralizer ((pResidual 2 A).map A.subtype : Set _) := by
  intro J q A B
  let : Fact c.prime.Prime := ⟨c.prime_isPrime⟩
  have hp : 3 < c.prime := by
    rcases c.prime_congruence with hp | hp <;>
      have hm := Nat.mod_le c.prime 24 <;> omega
  obtain ⟨hQK,hQc,_,_,_,_⟩ := c.selected.right_vertex_and_overlap_of_prime_model
    hg hz (c.selected.left_not_characteristic_two hg hz) c.prime_odd hp c.first_model.some
  have hne : B.pCoreIn 2 ≠ ⊥ := by
    intro he
    change Nat.card (B.pCoreIn 2) = 4 at hQc
    rw [he,card_bot] at hQc
    omega
  obtain ⟨t,ht,hn⟩ := SetLike.not_le_iff_exists.mp (opposite_core_moves_residual hg hz hne)
  refine ⟨t,?_,?_,hn⟩
  · exact ⟨(hg.symm.local_twoCore_le_intersection ht).2,
      (hg.symm.local_twoCore_le_intersection ht).1⟩
  · rw [c.cubic_image]
    exact le_centralizer_iff.mp (show
      pResidual 2 (J ⧸ pPrimeCore 3 J) ⊓ centralizer (c.selected.component : Set _) ≤
        centralizer (c.selected.component : Set _) from inf_le_right) (hQK ht)

/-- The separating element lifts into the original Sylow centralizer of
exactly the selected cubic lift. -/
theorem single_original_separating_element
    (hTH : (T : Subgroup G) ≤ H)
    (c : SingleQuotientProduct T L H)
    (hg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hi : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q) ⊓
        ((H.subgroupOf J).map q) = ((T : Subgroup G).subgroupOf J).map q)
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥) :
    let J := H ⊔ borelResidual T L
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    let A := ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q
    ∃ t : J, (t : G) ∈ (T : Subgroup G) ∧
      (t : G) ∈ centralizer (c.cubic_lift.map J.subtype : Set G) ∧
      q t ∉ centralizer ((pResidual 2 A).map A.subtype : Set _) := by
  intro J q A
  let S := T.subtype (hTH.trans (show H ≤ J from le_sup_left))
  have hk : ¬ 3 ∣ Nat.card q.ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.prime_three.coprime_iff_not_dvd).mp pPrimeCore_coprime_card
  have hinj : Function.Injective (q.comp c.cubic_lift.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hn : (x : J) ∈ pPrimeCore 3 J := (QuotientGroup.eq_one_iff _).mp hx
    have hc : Nat.Coprime (Nat.card c.cubic_lift) (Nat.card (pPrimeCore 3 J)) := by
      rw [c.cubic_card]
      exact pPrimeCore_coprime_card
    exact Subtype.ext ((disjoint_of_coprime_natCard hc).le_bot ⟨x.property,hn⟩)
  have hm := permuting_cubic_sylow_centralizer_image S c.cubic_lift c.cubic_card
    c.cubic_permutes q hk hinj
  obtain ⟨t,ht,hc,hn⟩ := single_quotient_separating_element c hg hz
  have htS : t ∈ (S : Subgroup J).map q := hi ▸ ht
  have htC : t ∈ ((S : Subgroup J) ⊓ centralizer (c.cubic_lift : Set J)).map q :=
    hm.symm ▸ ⟨htS,hc⟩
  obtain ⟨s,hs,rfl⟩ := htC
  refine ⟨s,hs.1,?_,hn⟩
  rintro _ ⟨a,ha,rfl⟩
  exact congrArg J.subtype (hs.2 a ha)

private theorem cubic_inversion_of_noncentral
    {M : Type*} [Group M] [Finite M] (F : Subgroup M) (hc : Nat.card F = 3)
    (t : M) (ht : t ∈ normalizer (F : Set M))
    (hn : t ∉ centralizer (F : Set M)) :
    ∀ a ∈ F, t * a * t⁻¹ = a⁻¹ := by
  intro a ha
  by_cases ha1 : a = 1
  · simp only [ha1,mul_one,mul_inv_cancel,inv_one]
  rcases cyclicThree_normalizer_conjugates F hc a ha ha1 t ht with hfix | hinv
  · exfalso
    apply hn
    have hta : Commute t a := mul_inv_eq_iff_eq_mul.mp hfix
    intro b hb
    rw [←(cyclicThree_generator F hc a ha ha1).1] at hb
    obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hb
    exact (hta.zpow_right n).eq.symm
  · exact hinv

/-- The same original Sylow centralizer contains an inverter of the literal
Borel residual image, which has order three. -/
theorem single_original_cubic_inverter
    (hTH : (T : Subgroup G) ≤ H)
    (c : SingleQuotientProduct T L H)
    (hg : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      ChapterF.IsGoldschmidtTriple
        (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q)
        ((H.subgroupOf J).map q))
    (hi : let J := H ⊔ borelResidual T L
      let q := QuotientGroup.mk' (pPrimeCore 3 J)
      (((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q) ⊓
        ((H.subgroupOf J).map q) = ((T : Subgroup G).subgroupOf J).map q)
    (hz : pCore 2 ((H ⊔ borelResidual T L : Subgroup G) ⧸
      pPrimeCore 3 (H ⊔ borelResidual T L : Subgroup G)) = ⊥) :
    let J := H ⊔ borelResidual T L
    let q := QuotientGroup.mk' (pPrimeCore 3 J)
    let A := ((borelResidual T L ⊔ (T : Subgroup G)).subgroupOf J).map q
    let R := (pResidual 2 A).map A.subtype
    Nat.card R = 3 ∧ ∃ t : J, (t : G) ∈ (T : Subgroup G) ∧
      (t : G) ∈ centralizer (c.cubic_lift.map J.subtype : Set G) ∧
      q t ∉ centralizer (R : Set _) ∧
      ∀ a ∈ R, q t * a * (q t)⁻¹ = a⁻¹ := by
  intro J q A R
  let : c.selected.component.Normal := c.selected.normal
  have hc : Nat.card R = 3 := ChapterF.SourceAssembly.left_residual_card_three_of_normal_subgroup
    hg hz c.selected.component c.selected.left_contains c.selected.right_escapes
  obtain ⟨t,ht,htD,htR⟩ := single_original_separating_element hTH c hg hi hz
  refine ⟨hc,t,ht,htD,htR,cubic_inversion_of_noncentral R hc (q t) ?_ htR⟩
  apply hg.intersection_normalizes_left_residual
  rw [hi]
  exact mem_map_of_mem q ht

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
