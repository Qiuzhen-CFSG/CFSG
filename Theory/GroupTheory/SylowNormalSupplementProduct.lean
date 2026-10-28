module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow subgroups in a normal supplement

A p-subgroup containing the embedded Sylow subgroups of N and D is Sylow
in N join D, when N is normal and the p-subgroup lies in that join.
In particular this applies to the product of commuting Sylow subgroups.

Inside the join, the index of T factors as [N : N intersect T] times
[G : NT]. The first factor divides the index of the chosen Sylow of N.
The second divides the index of the chosen Sylow of D, by mapping D onto
G/N. Both are prime to p. The resulting Sylow retains its actual ambient
image, so callers can centralize that exact product.

Source: the product-of-Sylows step in GLS II, Chapter B, Lemma 5.3
(`refs/KGroup/GLS2/ChapterB.tex`, final paragraph of the proof).
-/

open Subgroup

private theorem index_sup_of_normal
    {G : Type*} [Group G] [Finite G] (N T : Subgroup G) [N.Normal] :
    T.relIndex (N ⊔ T) = T.relIndex N := by
  have hmul : N.relIndex T * T.relIndex (N ⊔ T) = N.relIndex T * T.relIndex N := by
    calc
      N.relIndex T * T.relIndex (N ⊔ T) = (T ⊓ N).relIndex (N ⊔ T) := by
        rw [← inf_relIndex_left (H := T) (K := N)]
        exact relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (T ⊓ N).relIndex N * N.relIndex (N ⊔ T) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = N.relIndex T * T.relIndex N := by
        simp [inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (index_ne_zero_of_finite : N.relIndex T ≠ 0)) hmul

private theorem not_dvd_index_of_normal_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N D T : Subgroup G) [N.Normal] (hcover : N ⊔ D = ⊤)
    (hTN : ¬ p ∣ T.relIndex N) (hTD : ¬ p ∣ T.relIndex D) :
    ¬ p ∣ T.index := by
  let q := QuotientGroup.mk' N
  let f := q.comp D.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have h := congrArg (Subgroup.map q) hcover
    simpa only [f, q, MonoidHom.range_comp, range_subtype, Subgroup.map_sup,
      QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using h
  have hle : (T.subgroupOf D).map f ≤ T.map q := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_map_of_mem q hx
  have hqindex : ¬ p ∣ (T.map q).index := by
    intro h
    exact hTD ((h.trans (index_dvd_of_le hle)).trans
      ((T.subgroupOf D).index_map_dvd hf))
  have hsupindex : ¬ p ∣ (N ⊔ T).index := by
    have hi := (T.map q).index_comap_of_surjective (QuotientGroup.mk'_surjective N)
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_comm T N] at hi
    rwa [hi]
  have hmul := relIndex_mul_index (show T ≤ N ⊔ T from le_sup_right)
  rw [index_sup_of_normal N T] at hmul
  intro h
  rw [← hmul] at h
  exact ((Fact.out : p.Prime).dvd_mul.mp h).elim hTN hsupindex

/-- A p-subgroup containing Sylow subgroups of a normal subgroup and its
supplement is Sylow in their join. -/
public theorem IsPGroup.exists_sylow_sup_of_normal_sylow_images
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N D T : Subgroup G) [N.Normal] (hT : IsPGroup p T) (hTle : T ≤ N ⊔ D)
    (P : Sylow p N) (Q : Sylow p D)
    (hPT : (P : Subgroup N).map N.subtype ≤ T)
    (hQT : (Q : Subgroup D).map D.subtype ≤ T) :
    ∃ S : Sylow p (N ⊔ D : Subgroup G),
      (S : Subgroup (N ⊔ D : Subgroup G)).map (N ⊔ D : Subgroup G).subtype = T := by
  let L := N ⊔ D
  let NL := N.subgroupOf L
  let DL := D.subgroupOf L
  let TL := T.subgroupOf L
  have hcover : NL ⊔ DL = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self L
  have hTN : ¬ p ∣ TL.relIndex NL := by
    rw [relIndex_subgroupOf (show N ≤ L from le_sup_left)]
    refine fun h => P.not_dvd_index (h.trans (index_dvd_of_le ?_))
    intro x hx
    exact hPT (mem_map_of_mem N.subtype hx)
  have hTD : ¬ p ∣ TL.relIndex DL := by
    rw [relIndex_subgroupOf (show D ≤ L from le_sup_right)]
    refine fun h => Q.not_dvd_index (h.trans (index_dvd_of_le ?_))
    intro x hx
    exact hQT (mem_map_of_mem D.subtype hx)
  have hindex := not_dvd_index_of_normal_supplement NL DL TL hcover hTN hTD
  have hpTL : IsPGroup p TL := hT.comap_subtype
  refine ⟨hpTL.toSylow hindex, ?_⟩
  change TL.map L.subtype = T
  exact map_subgroupOf_eq_of_le hTle
