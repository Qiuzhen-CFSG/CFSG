module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Mathlib.GroupTheory.Index

/-!
# Lifting inner quotient actions through coprime kernels

If a subgroup has order coprime to the kernel of a homomorphism, containment
of its image in the image of a normal subgroup lifts to containment. Modulo
the normal subgroup, its image lies in the kernel image and has coprime order.

Applied to the literal normalizer action on a characteristic quotient of K,
this places an inner actor in K itself. Normality is only inside N_G(K).
This is the lifting step in Aschbacher--Smith 5.1.18, printed p.642; its
source centralizer being a three-prime group is a separate hypothesis.
-/

@[expose] public noncomputable section

open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]

/-- Containment in a normal subgroup lifts across a kernel of coprime order. -/
theorem le_of_map_le_of_coprime_ker (f : G →* D) (C N : Subgroup G) [N.Normal]
    (hc : Nat.Coprime (Nat.card C) (Nat.card f.ker))
    (hm : C.map f ≤ N.map f) : C ≤ N := by
  let q := QuotientGroup.mk' N
  have hC : C ≤ N ⊔ f.ker := by
    rw [← comap_map_eq]
    exact map_le_iff_le_comap.mp hm
  have hN : N.map q = ⊥ := (map_eq_bot_iff N).mpr (by simp [q])
  have hi : C.map q ≤ f.ker.map q := by
    have hh := map_mono (f := q) hC
    rwa [map_sup, hN, bot_sup_eq] at hh
  have hcard : Nat.card (C.map q) = 1 :=
    Nat.eq_one_of_dvd_coprimes hc (card_map_dvd C q)
      ((card_dvd_of_le hi).trans (card_map_dvd f.ker q))
  have hh := (map_eq_bot_iff C).mp (card_eq_one.mp hcard)
  simpa only [q, QuotientGroup.ker_mk'] using hh

variable (K : Subgroup G) (N : Subgroup K) [N.Characteristic]
/-- The actual conjugation action of N_G(K) on a characteristic quotient of K. -/
def normalizerQuotientAction : normalizer (K : Set G) →* MulAut (K ⧸ N) :=
  (quotientAut N).comp K.normalizerMonoidHom

/-- Elements of K induce their own inner automorphisms on the quotient. -/
theorem normalizerQuotientAction_inner (k : K) :
    normalizerQuotientAction K N ⟨k, K.le_normalizer k.property⟩ =
      MulAut.conj (QuotientGroup.mk' N k) := by
  ext x
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
  simp only [normalizerQuotientAction, MonoidHom.comp_apply,
    quotientAut_apply_mk, MulAut.conj_apply]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg (QuotientGroup.mk' N)
  apply Subtype.ext
  exact normalizerMonoidHom_apply_apply_coe K ⟨k, K.le_normalizer k.property⟩ y

/-- The image of the original K is exactly the inner automorphism subgroup. -/
theorem normalizerQuotientAction_map_self :
    (K.subgroupOf (normalizer (K : Set G))).map (normalizerQuotientAction K N) =
      (MulAut.conj : (K ⧸ N) →* MulAut (K ⧸ N)).range := by
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    exact ⟨QuotientGroup.mk' N ⟨k, hk⟩, (normalizerQuotientAction_inner K N ⟨k, hk⟩).symm⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨⟨k, K.le_normalizer k.property⟩, k.property,
      normalizerQuotientAction_inner K N k⟩

/-- An inner actor with order coprime to the action kernel lies in K. -/
theorem le_of_normalizerQuotientAction_inner (C : Subgroup G)
    (hCN : C ≤ normalizer (K : Set G))
    (hc : Nat.Coprime (Nat.card C) (Nat.card (normalizerQuotientAction K N).ker))
    (hi : (C.subgroupOf (normalizer (K : Set G))).map (normalizerQuotientAction K N) ≤
      (MulAut.conj : (K ⧸ N) →* MulAut (K ⧸ N)).range) : C ≤ K := by
  have hn : (K.subgroupOf (normalizer (K : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer le_rfl
  have hh := le_of_map_le_of_coprime_ker (normalizerQuotientAction K N)
    (C.subgroupOf (normalizer (K : Set G))) (K.subgroupOf (normalizer (K : Set G)))
    (by simpa only [Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] using hc)
    (by rwa [normalizerQuotientAction_map_self])
  intro c hcc
  exact hh (show (⟨c, hCN hcc⟩ : normalizer (K : Set G)) ∈ C.subgroupOf _ from hcc)
end Subgroup
