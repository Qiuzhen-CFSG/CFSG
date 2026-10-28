module
public import Theory.GroupTheory.SylowNormalRestriction
/-!
# Divisors from the Borel of a normal layer

Let P be the intersection of a quotient Sylow with a normal layer. The
normalizer of P contains the full quotient Sylow. If P is not normal in
the layer, that normalizer is proper, so its inverse image lies in every
subgroup containing all proper overgroups of the original Sylow. The
intrinsic layer normalizer contributes its full order to that subgroup.

This retains a possible semilinear extension and the whole quotient kernel.
Source application: Aschbacher--Smith 10.2.3(4), printed p.746.
-/
public section
open Subgroup
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]
set_option backward.isDefEq.respectTransparency false in
theorem layer_sylow_normalizer_card_dvd_of_proper_overgroups
    (S : Sylow 2 G) (q : G →* Q) (hq : Function.Surjective q)
    (L : Subgroup Q) [L.Normal] (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = (S.mapSurjective hq : Subgroup Q) ⊓ L)
    (hPN : normalizer (P : Set L) ≠ ⊤)
    (M : Subgroup G)
    (hM : ∀ J : Subgroup G, (S : Subgroup G) ≤ J → J ≠ ⊤ → J ≤ M) :
    Nat.card (normalizer (P : Set L)) ∣ Nat.card M := by
  let T := S.mapSurjective hq
  let U := (P : Subgroup L).map L.subtype
  let N := normalizer (U : Set Q)
  have hTN : (T : Subgroup Q) ≤ N := by
    change (T : Subgroup Q) ≤ normalizer ((P : Subgroup L).map L.subtype : Set Q)
    rw [hP]
    exact (le_inf (T : Subgroup Q).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hN : N ≠ ⊤ := by
    intro hn
    apply hPN
    apply top_unique
    intro a ha
    have haN : (a:Q) ∈ N := hn.symm ▸ mem_top _
    have hh : a ∈ (normalizer ((P : Subgroup L).map L.subtype : Set Q)).comap L.subtype := haN
    rw [comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective L.subtype_injective] at hh
    exact hh
  let J := N.comap q
  have hSJ : (S : Subgroup G) ≤ J := by
    intro s hs
    exact hTN (mem_map_of_mem q hs)
  have hJ : J ≠ ⊤ := by
    intro hj
    apply hN
    rw [←map_comap_eq_self_of_surjective hq N]
    change J.map q = ⊤
    rw [hj,map_top_of_surjective _ hq]
  have hJM := hM J hSJ hJ
  have hLN : (normalizer (P : Set L)).map L.subtype ≤ N :=
    (P : Subgroup L).le_normalizer_map L.subtype
  have hd : Nat.card (normalizer (P : Set L)) ∣ Nat.card N := by
    rw [←card_map_of_injective (K := normalizer (P : Set L)) L.subtype_injective]
    exact card_dvd_of_le hLN
  have hdJ : Nat.card N ∣ Nat.card J := by
    have hh := card_map_dvd J q
    rwa [show J.map q = N from map_comap_eq_self_of_surjective hq N] at hh
  exact hd.trans (hdJ.trans (card_dvd_of_le hJM))
end Subgroup
