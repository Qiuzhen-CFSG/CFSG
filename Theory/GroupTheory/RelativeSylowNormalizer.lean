module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index

/-!
# Promoting a relative Sylow subgroup using its normalizer

Let R be Sylow in K ≤ H. If N_H(R) lies in K, then R is Sylow in H.
The normalizer index is prime to two, and the normalizer-index congruence
shows that the index in H is also prime to two. All subgroup images are
retained literally, so the conclusion needs no conjugation of R.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
the first reduction in 12.4.6, printed p.814, with H=C_G(v) and K=C_M(v).
-/

public section
namespace Subgroup

/-- A Sylow subgroup in K is Sylow in H if its H-normalizer lies in K. -/
theorem exists_sylow_eq_of_relative_normalizer_le {G : Type*} [Group G] [Finite G]
    {R H K : Subgroup G} (hR : ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = R)
    (hKH : K ≤ H) (hn : H ⊓ normalizer (R : Set G) ≤ K) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = R := by
  obtain ⟨P,hP⟩ := hR
  have hRK : R ≤ K := hP ▸ map_subtype_le _
  have hRH := hRK.trans hKH
  have hp : IsPGroup 2 R := hP ▸ P.isPGroup'.map K.subtype
  have hi : ¬ 2 ∣ R.relIndex K := by
    rw [← hP]
    have heq : ((P : Subgroup K).map K.subtype).relIndex K = (P : Subgroup K).index := by
      simpa only [← MonoidHom.range_eq_map, K.range_subtype, relIndex_top_right] using
        relIndex_map_map_of_injective (P : Subgroup K) ⊤ K.subtype_injective
    rw [heq]
    exact P.not_dvd_index
  let RH := R.subgroupOf H
  have hpn : IsPGroup 2 RH := hp.comap_subtype
  have hmapN : (normalizer (RH : Set H)).map H.subtype =
      H ⊓ normalizer (R : Set G) := by
    rw [← subgroupOf_normalizer_eq hRH, subgroupOf_map_subtype, inf_comm]
  have hh : RH.relIndex (normalizer (RH : Set H)) =
      R.relIndex (H ⊓ normalizer (R : Set G)) := by
    have hh := relIndex_map_map_of_injective RH (normalizer (RH : Set H)) H.subtype_injective
    rw [hmapN, show RH.map H.subtype = R from map_subgroupOf_eq_of_le hRH] at hh
    exact hh.symm
  have hdiv : R.relIndex (H ⊓ normalizer (R : Set G)) ∣ R.relIndex K := by
    exact dvd_of_mul_right_eq _ (relIndex_mul_relIndex R _ K
      (le_inf hRH R.le_normalizer) hn)
  have hnot : ¬ 2 ∣ RH.relIndex (normalizer (RH : Set H)) := by
    rw [hh]
    exact fun h => hi (h.trans hdiv)
  obtain ⟨n, hn⟩ := hpn.exists_card_eq
  have hmod := Sylow.card_quotient_normalizer_modEq_card_quotient hn
  have hnot' : ¬ 2 ∣ RH.index := fun h => hnot ((hmod.dvd_iff dvd_rfl).mpr h)
  refine ⟨hpn.toSylow hnot', ?_⟩
  exact map_subgroupOf_eq_of_le hRH


end Subgroup
