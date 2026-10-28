module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Orbits
public import Mathlib.Data.List.FinRange

/-!
# Ordered χ-products from the outside-block source step

The join of all actual χ-blocks moved by J(T) is normal and has at most
two factors. If every proper overgroup of M misses such a block, that
join supplements M. Multiplication of the commuting block factors gives
the literal ordered element factorization needed in C.1.29.

The outside-block implication is exactly the earlier C.1.26–27 input;
this module proves the remaining product step and does not assert that
earlier implication. The solvable source application constructs it separately.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The canonical homomorphism of commuting factors is the specified ordered
product, with the original inclusions and the Fin ordering retained. -/
theorem ordered_product_of_mem_iSup {r : ℕ} (L : Fin r → Subgroup G)
    (hc : Pairwise fun i j => L i ≤ centralizer (L j : Set G))
    {g : G} (hg : g ∈ ⨆ i, L i) :
    ∃ b : ∀ i, L i, g = (List.ofFn (fun i => (b i : G))).prod := by
  classical
  have hcomm : Pairwise fun i j => ∀ x y : G,
      x ∈ L i → y ∈ L j → Commute x y :=
    fun _ _ hij _ _ hx hy => (mem_centralizer_iff.mp (hc hij hx) _ hy).symm
  have hg' : g ∈ (Subgroup.noncommPiCoprod hcomm).range := by
    rwa [Subgroup.noncommPiCoprod_range]
  obtain ⟨b, rfl⟩ := hg'
  refine ⟨b, ?_⟩
  rw [Subgroup.noncommPiCoprod_apply]
  simpa only [List.toFinset_finRange, List.ofFn_eq_map] using
    Finset.noncommProd_toFinset (List.finRange r) (fun i => (b i : G))
      (fun i _ j _ hij => hcomm hij _ _ (b i).property (b j).property)
      (List.nodup_finRange r)

/-- The finite-family part of C.1.28. Its earlier source input is an outside
moved block for each proper overgroup, never a product or recognition witness. -/
theorem ordered_product_of_outside_moved
    (hG : generalizedFitting G = pCore 2 G) (hr : primeRank 3 G ≤ 2)
    (T : Sylow 2 G) (M : Subgroup G)
    (hout : ∀ N : Subgroup G, M ≤ N → N ≠ ⊤ →
      ∃ L : Subgroup G, ¬ L ≤ N ∧ IsChiBlockIn L ∧
        L = ⁅L, elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsChiBlockIn (L i)) ∧
      (∀ i, L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆) ∧
      ∀ g : G, ∃ m : M, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod := by
  classical
  let I := {L : Subgroup G // IsChiBlockIn L ∧
    L = ⁅L, elementaryAbelianMaxJ (T : Subgroup G)⁆}
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let L : Fin r → Subgroup G := fun i => (e.symm i).val
  have hL (i) : IsChiBlockIn (L i) := (e.symm i).property.1
  have hm (i) : L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
    (e.symm i).property.2
  have hi : Function.Injective L := by
    intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  have hguard := blockCommutationHypothesis_of_fitting hG
  have hr' : r ≤ 2 := by
    have hh := (card_le_threeRank hguard L hi hL).trans hr
    simpa only [Fintype.card_fin] using hh
  let X := movedLayer (T : Subgroup G)
  let : X.Normal := movedLayer_normal hG hr T
  have hLX : (⨆ i, L i) = X := by
    apply le_antisymm
    · exact iSup_le fun i => le_movedLayer _ (hL i) (hm i)
    · apply iSup_le
      intro K
      apply iSup_le
      intro hK
      have he : L (e ⟨K, hK⟩) = K := by
        change (e.symm (e ⟨K, hK⟩)).val = K
        rw [e.symm_apply_apply]
      exact he ▸ le_iSup L (e ⟨K, hK⟩)
  have hgen : M ⊔ X = ⊤ := by
    by_contra hn
    obtain ⟨K, hk, hK, hmove⟩ := hout (M ⊔ X) le_sup_left hn
    exact hk ((le_movedLayer _ hK hmove).trans le_sup_right)
  have hc : Pairwise fun i j => L i ≤ centralizer (L j : Set G) :=
    fun i j hij => commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute hguard (hL i).1 (hL j).1 (fun he => hij (hi he)))
  refine ⟨r, hr', L, hL, hm, fun g => ?_⟩
  obtain ⟨m, hmM, x, hx, he⟩ := mem_sup_of_normal_right.mp
    (show g ∈ M ⊔ X by rw [hgen]; exact mem_top g)
  obtain ⟨b, hb⟩ := ordered_product_of_mem_iSup L hc (hLX.symm ▸ hx)
  exact ⟨⟨m, hmM⟩, b, he.symm.trans (congrArg (fun x => m * x) hb)⟩

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct
