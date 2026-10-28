module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.FullFusion.Geometry

/-!
# Full Aut(A₆) fusion in the proof of 16.4.9(2)

The actual Sylow action on A₆ has kernel ⟨z⟩. Its two elementary
eight-groups lift to exactly the two maximal elementary sixteen-groups
A and Aˢ, with s in T outside A T_L interchanging them. The relative
normalizer N_T(A) has order 32, hence index two over A.

Sylow conjugacy inside C_G(z) proves transitivity on its maximal
elementary family. The exact incidence equivalence A.1.7(1) then gives
normalizer transitivity on β = zᴳ ∩ A. The Sylow bound on N_G(A), together
with the independently computed order-six point stabilizer, rules out
four points. The published binary classification forces the total product
into zᴳ and gives five points, yielding the order-thirty contradiction.

The supplied product model, its Sylow placement, the product exclusions,
and the order-six stabilizer are the authorized independent inputs to
this branch. Their construction and the final Δ₀-nonemptiness assembly
remain with the owning Six development. In particular, none of the
family, transitivity, normalizer-index, or five-point conclusions is
assumed here. The corrected β uses A, as explained in SixSetCorrection.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z r : G}

theorem maximal_subgroups_swapped (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    ∃ s ∈ (T : Subgroup G), s ∉ elementary M ⊔ componentSylow T L ∧
      (elementary M).conjBy s ≠ elementary M ∧
      ((elementary M).conjBy s).conjBy s = elementary M ∧
      Stellmacher.elementaryAbelianMaxSubgroups (T : Subgroup G) =
        {elementary M, (elementary M).conjBy s} := by
  obtain ⟨s, hs, hsout, hne, hfamily, _⟩ := full_sylow_geometry h e M hAT hfull hTC
  have hconjT (E : Subgroup G) (hET : E ≤ T) : E.conjBy s ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hs (hET ha))
      ((T : Subgroup G).inv_mem hs)
  let A₁ := (elementary M).conjBy s
  let A₂ := A₁.conjBy s
  let : IsElementaryAbelian 2 A₁ := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A₂ := IsElementaryAbelian.map _
  have hA₂c : Nat.card A₂ = 16 := by
    dsimp [A₂, A₁, conjBy]
    rw [card_map_of_injective (MulAut.conj s).injective,
      card_map_of_injective (MulAut.conj s).injective, elementary_card]
  have hm := (full_maximal_iff h e M hAT hfull hTC A₂).mpr
    ⟨hconjT A₁ (hconjT _ hAT), inferInstance, hA₂c⟩
  rw [hfamily] at hm
  have hswap : A₂ = elementary M := by
    rcases hm with hm | hm
    · exact hm
    · exact (hne ((map_injective (MulAut.conj s).injective) hm)).elim
  exact ⟨s, hs, hsout, hne, hswap, hfamily⟩

theorem sylowFamilyTransitive_of_full (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) : SylowFamilyTransitive T M := by
  obtain ⟨s, hs, _, hpair, _⟩ := full_sylow_pair h e M hAT hfull hTC
  exact sylowFamilyTransitive_of_pair T M s hs hpair

theorem relative_normalizer_index_of_full (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    (elementary M).relIndex
      ((T : Subgroup G) ⊓ normalizer (elementary M : Set G)) = 2 := by
  obtain ⟨_, _, _, _, hN⟩ := full_sylow_pair h e M hAT hfull hTC
  exact relative_normalizer_index T M hAT hN

theorem centralizer_elementary_card_bound (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hEC : E ≤ centralizer ({z} : Set G)) : Nat.card E ≤ 16 := by
  let C := centralizer ({z} : Set G)
  let : IsElementaryAbelian 2 (E.subgroupOf C) := IsElementaryAbelian.subgroupOf hEC
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup 2 (E.subgroupOf C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C P (T.subtype h.sylow_centralizes)
  have hEt : E.conjBy (c : G) ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    have hp : (MulAut.conj c) (⟨a, hEC ha⟩ : C) ∈
        ((c • P : Sylow 2 C) : Subgroup C) := ⟨⟨a, hEC ha⟩, hEP ha, rfl⟩
    rw [hc] at hp
    exact hp
  let : IsElementaryAbelian 2 (E.conjBy (c : G)) := IsElementaryAbelian.map _
  have hb := full_elementary_card_bound h e hfull hTC (E.conjBy (c : G)) hEt
  rwa [conjBy, card_map_of_injective (MulAut.conj (c : G)).injective] at hb

theorem centralizer_maximal_family_transitive (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) :
    ∀ E ∈ Stellmacher.elementaryAbelianMaxSubgroups (centralizer ({z} : Set G)),
      ∃ c ∈ centralizer ({z} : Set G), (elementary M).conjBy c = E := by
  rintro E ⟨hEC, hEe, hmax⟩
  let : IsElementaryAbelian 2 E := hEe
  have hlo := hmax (elementary M) (hAT.trans h.sylow_centralizes) inferInstance
  rw [elementary_card] at hlo
  have hEc : Nat.card E = 16 := le_antisymm
    (centralizer_elementary_card_bound h e hfull hTC E hEC) hlo
  exact centralizer_elementary_family T M h.sylow_centralizes
    (sylowFamilyTransitive_of_full h e M hAT hfull hTC) E hEc hEC

theorem normalizerTransitive_of_full (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z) : NormalizerTransitive M :=
  normalizerTransitive_of_sylowFamily T M h.sylow_centralizes
    (sylowFamilyTransitive_of_full h e M hAT hfull hTC)

theorem beta_card_ne_four_of_full (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hr : IsConj z r) (hfull : FullAutomorphismCase e)
    (hTC : commutingSylow T L = zpowers z)
    (hs : Nat.card (normalizerStabilizer M) = 6) : Nat.card (beta M) ≠ 4 := by
  obtain ⟨_, _, _, _, hN⟩ := full_sylow_pair h e M hAT hfull hTC
  exact beta_card_ne_four_of_sylow_bound M hr
    (normalizerTransitive_of_full h e M hAT hfull hTC) hs
    (normalizer_sylow_card_le T M (sylowFamilyTransitive_of_full h e M hAT hfull hTC) hN)

theorem fusion (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hr : IsConj z r) (hex : ProductExclusions M)
    (hfull : FullAutomorphismCase e) (hTC : commutingSylow T L = zpowers z)
    (hs : Nat.card (normalizerStabilizer M) = 6) :
    NormalizerTransitive M ∧ IsConj z (total M) ∧ Nat.card (beta M) = 5 := by
  have ht := total_conjugate_of_beta_card_ne_four M hr hex
    (beta_card_ne_four_of_full h e M hAT hr hfull hTC hs)
  exact ⟨normalizerTransitive_of_full h e M hAT hfull hTC, ht,
    beta_card_of_total_conjugate M hr hex.1 hex.2 ht⟩

theorem contradiction (h : StandardSetup T z L)
    (e : L ≃* alternatingGroup (Fin 6)) (M : AlternatingProductModel L z r 6)
    (hAT : elementary M ≤ T) (hr : IsConj z r) (hex : ProductExclusions M)
    (hfull : FullAutomorphismCase e) (hTC : commutingSylow T L = zpowers z)
    (hs : Nat.card (normalizerStabilizer M) = 6) : False := by
  obtain ⟨htrans, _, hb⟩ := fusion h e M hAT hr hex hfull hTC hs
  exact contradiction_of_five_points M hb htrans hs

end CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
