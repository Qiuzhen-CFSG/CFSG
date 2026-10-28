module
public import Theory.Quasithin.ComponentRanks.CentralProducts
public import Theory.Quasithin.CubicIntersectionLocalTwoRank
public import Theory.Quasithin.ProductLocalRank
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Local rank budgets for nonnormal ordinary components

A distinct conjugate commutes with the original component. For a centerless
component their product is direct, so local rank in one factor and ordinary
rank in the other add inside an actual two-local. For a cubic intersection,
the checked central-product inequality instead bounds local cubic rank by one.

Source: Aschbacher–Smith A.1.34 and A.3.8(1–2), printed pp.29–30 and45–46.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nonnormal component with at most cubic center and cubic rank at least
 two has local cubic rank at most one. -/
theorem IsComponent.local_threeRank_le_one_of_nonnormal
    {K : Subgroup G} (hK : IsComponent G K) (hG : IsQuasithin G)
    (hn : ¬ K.Normal) (hz : Nat.card (center K) ≤ 3)
    (hr : 2 ≤ primeRank 3 K) : twoLocalPrimeRank 3 K ≤ 1 := by
  classical
  have hN : normalizer (K : Set G) ≠ ⊤ :=
    fun he => hn (normalizer_eq_top_iff.mp he)
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  let C := K.map (MulAut.conj g).toMonoidHom
  have hne : K ≠ C := fun he => hg.2 (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : K ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne (hK.map_conj g) hne)
  have hi : K ⊓ C ≤ (center K).map K.subtype := by
    rintro x ⟨hx,hc'⟩
    refine ⟨⟨x,hx⟩,mem_center_iff.mpr (fun y => ?_),rfl⟩
    exact Subtype.ext (hc y.property x hc').symm
  have hcard : Nat.card (K ⊓ C : Subgroup G) ≤ 3 := by
    have hh := card_le_of_le hi
    rw [card_map_of_injective K.subtype_injective] at hh
    exact hh.trans hz
  have hrC : 2 ≤ primeRank 3 C :=
    hr.trans_eq (primeRank_equiv 3 ((MulAut.conj g).subgroupMap K))
  by_contra hh
  exact Theory.Quasithin.CubicIntersection.not_quasithin_of_local_two_ordinary_two
    K C hc hcard (by omega) hrC hG

/-- Local rank in a centerless nonnormal component and ordinary rank in its
 distinct conjugate contribute additively to an actual ambient two-local. -/
theorem IsComponent.local_add_ordinary_rank_le_two_of_nonnormal_centerless
    {K : Subgroup G} (hK : IsComponent G K) (hG : IsQuasithin G)
    (hn : ¬ K.Normal) (hz : center K = ⊥)
    (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    twoLocalPrimeRank p K + primeRank p K ≤ 2 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hN : normalizer (K : Set G) ≠ ⊤ :=
    fun he => hn (normalizer_eq_top_iff.mp he)
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hN)
  let C := K.map (MulAut.conj g).toMonoidHom
  have hne : K ≠ C := fun he => hg.2 (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have hc : K ≤ centralizer (C : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hK.commutator_eq_bot_of_ne (hK.map_conj g) hne)
  have hd : Disjoint K C := by
    apply disjoint_def.mpr
    intro x hx hy
    have hh : (⟨x,hx⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun y => Subtype.ext (hc y.property x hy).symm)
    have hx1 : (⟨x,hx⟩ : K) = 1 := mem_bot.mp (hz ▸ hh)
    exact congrArg (fun z : K => (z : G)) hx1
  let m : K × C →* G := K.subtype.noncommCoprod C.subtype
    (fun x y => (hc x.property y y.property).symm)
  have hm : Function.Injective m := Subgroup.mul_injective_of_disjoint hd
  obtain ⟨Q,hQ,hQne⟩ := hK.exists_nontrivial_two_subgroup
  have hl : ∃ M : Subgroup K, IsTwoLocal M :=
    ⟨normalizer (Q : Set K),Q,hQne,hQ,rfl⟩
  have hh := (Theory.Quasithin.ProductLocalRank.local_add_ordinary_le (B := C) p hl).trans
    (twoLocalPrimeRank_le_of_injective p m hm)
  have he : primeRank p K = primeRank p C := primeRank_equiv p ((MulAut.conj g).subgroupMap K)
  rw [← he] at hh
  exact hh.trans (isQuasithin_iff_twoLocalPrimeRank.mp hG p hp ho)

end Theory.GroupTheory
