module
public import Mathlib.GroupTheory.Sylow

/-!
# A Sylow subgroup in a normalized supplement

In a finite group, let the `p`-group `T` normalize `K`. If `K` has a subgroup
`D` of index prime to `p` whose ambient image lies in `T`, then `T` is the
ambient image of a Sylow `p`-subgroup of `K ⊔ T`.

The proof works inside the join, where `K` is normal. Multiplicativity of
relative indices and the normal subgroup diamond formula give
`[K ⊔ T : T] = [K : K ∩ T]`. The latter index divides `[K : D]`, so it is
prime to `p`, and the Sylow index criterion applies to `T`.

This is the standard finite-group product/index argument used for the
centralizer supplement in Stellmacher (6.4), Journal of Algebra 190 (1997).
The statement is independent of the campaign and requires no normality of `D`.
-/

private theorem index_sup_of_normal
    {G : Type*} [Group G] [Finite G] (K T : Subgroup G) [K.Normal] :
    T.relIndex (K ⊔ T) = T.relIndex K := by
  have hmul :
      K.relIndex T * T.relIndex (K ⊔ T) = K.relIndex T * T.relIndex K := by
    calc
      K.relIndex T * T.relIndex (K ⊔ T) =
          (T ⊓ K).relIndex (K ⊔ T) := by
        rw [← Subgroup.inf_relIndex_left (H := T) (K := K)]
        exact Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_right
      _ = (T ⊓ K).relIndex K * K.relIndex (K ⊔ T) :=
        (Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_left).symm
      _ = K.relIndex T * T.relIndex K := by
        simp [Subgroup.inf_relIndex_right, Nat.mul_comm]
  exact Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite : K.relIndex T ≠ 0)) hmul

/-- A `p`-group normalizing a subgroup and containing an image of a subgroup
of coprime index is Sylow in their join. -/
public theorem IsPGroup.exists_sylow_sup_of_coprime_index
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K T : Subgroup G) (hT : IsPGroup p T) (hnorm : T ≤ Subgroup.normalizer K)
    (D : Subgroup K) (hDindex : ¬ p ∣ D.index) (hDT : D.map K.subtype ≤ T) :
    ∃ S : Sylow p ↑(K ⊔ T),
      (S : Subgroup ↑(K ⊔ T)).map (K ⊔ T : Subgroup G).subtype = T := by
  let L := K ⊔ T
  have hKL : K ≤ L := le_sup_left
  have hTL : T ≤ L := le_sup_right
  let KL := K.subgroupOf L
  let TL := T.subgroupOf L
  have : KL.Normal := Subgroup.normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer hnorm)
  have hsup : KL ⊔ TL = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKL hTL]
    exact Subgroup.subgroupOf_self L
  have hindex : TL.index = T.relIndex K := by
    calc
      TL.index = TL.relIndex (KL ⊔ TL) := by rw [hsup, Subgroup.relIndex_top_right]
      _ = TL.relIndex KL := index_sup_of_normal KL TL
      _ = T.relIndex K := Subgroup.relIndex_subgroupOf hKL
  have hDle : D ≤ T.subgroupOf K := by
    intro x hx
    exact hDT (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hTindex : ¬ p ∣ TL.index := by
    rw [hindex]
    exact fun hdvd => hDindex (hdvd.trans (Subgroup.index_dvd_of_le hDle))
  have hp : IsPGroup p TL :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  refine ⟨hp.toSylow hTindex, ?_⟩
  rw [IsPGroup.toSylow_coe]
  exact Subgroup.map_subgroupOf_eq_of_le hTL
