module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.RankBounds
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.PrimeRankZero

/-!
# Eliminating multiple centerless components

Choose an actual cubic element in each factor's Borel theta subgroup.
The preceding normalizer calculation places all these elements in C.
Centerless commuting factors are independent, so multiplication embeds
the product of their order-three cyclic subgroups into C. Its order is
three to the number of factors. Rank one bounds that number by one.
Only this final step uses centerlessness; it must be applied after the
higher-rank model alternatives have been excluded.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
variable {D : Type*} [Group D] [Finite D]

/-- Independent commuting factors contribute independent cubic elements even
when all of those elements are required to lie in a specified subgroup. -/
private theorem card_le_rank_of_cubics {ι : Type*} [Fintype ι]
    (K : ι → Subgroup D) (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hz : ∀ i, center (K i) = ⊥) (C : Subgroup D)
    (x : ∀ i, K i) (hx : ∀ i, orderOf (x i) = 3) (hxc : ∀ i, (x i : D) ∈ C) :
    Fintype.card ι ≤ primeRank 3 C := by
  classical
  let E : ι → Subgroup D := fun i => zpowers (x i : D)
  have hEK (i : ι) : E i ≤ K i := zpowers_le.mpr (x i).property
  have hEC (i : ι) : E i ≤ C := zpowers_le.mpr (hxc i)
  have hxD (i : ι) : orderOf (x i : D) = 3 := (Subgroup.orderOf_coe (x i)).trans (hx i)
  let (i : ι) : IsElementaryAbelian 3 (E i) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (hxD i ▸ pow_orderOf_eq_one (x i : D))
  have hcomm : Pairwise fun i j => ∀ a b : D,
      a ∈ K i → b ∈ K j → Commute a b :=
    fun _ _ hij _a b ha hb => (hc hij ha b hb).symm
  have hind : iSupIndep E :=
    (iSupIndep_of_centerless_of_pairwise_commute K hz hcomm).mono hEK
  have hecomm : Pairwise fun i j => ∀ a b : D,
      a ∈ E i → b ∈ E j → Commute a b :=
    fun i j hij a b ha hb => hcomm hij a b (hEK i ha) (hEK j hb)
  let f := noncommPiCoprod hecomm
  have hf : Function.Injective f := injective_noncommPiCoprod_of_iSupIndep hind
  have hr : f.range ≤ C :=
    (show f.range = iSup E from noncommPiCoprod_range).le.trans (iSup_le hEC)
  let g : (∀ i, E i) →* C := f.codRestrict C (fun y => hr ⟨y, rfl⟩)
  have hg : Function.Injective g := by
    intro a b h
    exact hf (congrArg (fun z : C => (z : D)) h)
  let (i : ι) : CommGroup (E i) := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding (f := g) (hf := hg)
  · intro a
    funext i
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 (E i)) (a i)
  · simp only [Nat.card_pi, E, Nat.card_zpowers, hxD, Finset.prod_const,
      Finset.card_univ]

/-- Once the surviving factors are centerless, each nonzero cubic torus
contributes a separate dimension to C. Hence at most one factor survives. -/
theorem family_card_le_one {ι : Type*} [Fintype ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (hz : ∀ i, center (K i) = ⊥)
    (n : ℕ) (r : ι → ℕ) (hr : ∀ i, 1 ≤ r i)
    (hK : ∀ i, NormalizerData (K i) n (r i))
    (C : Subgroup D) (hC : CubicSylowControl D C) : Fintype.card ι ≤ 1 := by
  have he := family_even K hc hgen n r hK C hC
  obtain ⟨S, hn⟩ := hC.normalized
  have hBC := (family_borel K hc hgen n r hK C hC S hn).2.1
  have hθC : theta (normalizer (S : Set D)) ≤ C :=
    (theta_mono hBC).trans_eq hC.theta_normalizer
  have hex (i : ι) : ∃ x : K i, orderOf x = 3 ∧ (x : D) ∈ C := by
    obtain ⟨R, _, hR⟩ := Sylow.factor_normalizer_control K hc hgen S i
    have hpos := (hr i).trans ((hK i).rank he R)
    have hd : 3 ∣ Nat.card (theta (normalizer (R : Set (K i)))) := by
      by_contra hnot
      have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hnot
      omega
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := theta (normalizer (R : Set (K i)))) 3 hd
    refine ⟨x, (Subgroup.orderOf_coe x).trans hx, ?_⟩
    apply hθC
    have ht : (theta (normalizer (R : Set (K i)))).map (K i).subtype ≤
        theta (normalizer (S : Set D)) := by
      rw [theta_map_of_injective _ (K i).subtype_injective]
      exact theta_mono hR
    exact ht (mem_map_of_mem _ x.property)
  choose x hx hxc using hex
  exact (card_le_rank_of_cubics K hc hz C x hx hxc).trans_eq hC.rank

/-- A nonempty family of centerless surviving factors consists of the whole group. -/
theorem family_eq_top {ι : Type*} [Fintype ι] [Nonempty ι]
    (K : ι → Subgroup D)
    (hc : Pairwise fun i j => K i ≤ centralizer (K j : Set D))
    (hgen : iSup K = ⊤) (hz : ∀ i, center (K i) = ⊥)
    (n : ℕ) (r : ι → ℕ) (hr : ∀ i, 1 ≤ r i)
    (hK : ∀ i, NormalizerData (K i) n (r i))
    (C : Subgroup D) (hC : CubicSylowControl D C) : ∀ i, K i = ⊤ := by
  have hcard := family_card_le_one K hc hgen hz n r hr hK C hC
  let : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard
  intro i
  apply top_unique
  rw [← hgen]
  exact iSup_le fun j => (congrArg K (Subsingleton.elim j i)).le
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
