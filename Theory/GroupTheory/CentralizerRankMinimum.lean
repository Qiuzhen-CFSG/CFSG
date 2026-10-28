module

public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Minimum quotient rank detected by a larger centralizer

For a finite abelian subgroup `U` of an arbitrary group and another subgroup
`R`, consider the ranks of `U/A` for `A ≤ U` whose centralizer in `R` properly
contains `C_R(U)`. This set is nonempty exactly when `C_R(U) < R`; its infimum
is then an attained minimum. An isomorphism transports both the centralizers
and the actual quotients, so it preserves the minimum.

The final centralizer lemma gives the witness `A = C_V(U)` when `U ≤ R`
and `V` does not centralize `U`. Applied to a conjugate `V = Uˣ`, this is the
rank argument of Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), C.6.3(2), printed p. 166.
-/

open scoped IsMulCommutative
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

private instance finite_map_equiv (U : Subgroup G) [Finite U] (e : G ≃* H) :
    Finite (U.map (e : G →* H)) := Finite.of_equiv U (e.subgroupMap U).toEquiv

/-- The genuine set of quotient ranks for which the relative centralizer enlarges. -/
@[expose] public noncomputable def centralizerRankValues (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] : Set ℕ :=
  {n | ∃ A : Subgroup G, A ≤ U ∧
    R ⊓ centralizer (U : Set G) < R ⊓ centralizer (A : Set G) ∧
    Group.rank (U ⧸ A.subgroupOf U) = n}

/-- The minimum centralizer-detecting quotient rank, denoted `m(R,U)` in C.6.3.
It is an attained minimum when `C_R(U) < R`; on the empty set it is zero. -/
@[expose] public noncomputable def centralizerRankMinimum (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] : ℕ := sInf (centralizerRankValues R U)

public theorem centralizerRankValues_nonempty (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] (h : R ⊓ centralizer (U : Set G) < R) :
    (centralizerRankValues R U).Nonempty := by
  refine ⟨_, ⊥, bot_le, ?_, rfl⟩
  have hbot : centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    ext g
    simp [mem_centralizer_iff]
  simpa only [hbot, inf_top_eq] using h

public theorem centralizerRankMinimum_mem (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] (h : R ⊓ centralizer (U : Set G) < R) :
    centralizerRankMinimum R U ∈ centralizerRankValues R U :=
  Nat.sInf_mem (centralizerRankValues_nonempty R U h)

public theorem centralizerRankMinimum_le (R U A : Subgroup G) [Finite U]
    [IsMulCommutative U] (hAU : A ≤ U)
    (hC : R ⊓ centralizer (U : Set G) < R ⊓ centralizer (A : Set G)) :
    centralizerRankMinimum R U ≤ Group.rank (U ⧸ A.subgroupOf U) :=
  Nat.sInf_le ⟨A, hAU, hC, rfl⟩

public theorem centralizerRankValues_nonempty_iff (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] :
    (centralizerRankValues R U).Nonempty ↔ R ⊓ centralizer (U : Set G) < R := by
  constructor
  · rintro ⟨n, A, _, hC, _⟩
    exact hC.trans_le inf_le_left
  · exact centralizerRankValues_nonempty R U

public theorem centralizerRankMinimum_isLeast (R U : Subgroup G) [Finite U]
    [IsMulCommutative U] (h : R ⊓ centralizer (U : Set G) < R) :
    IsLeast (centralizerRankValues R U) (centralizerRankMinimum R U) := by
  refine ⟨centralizerRankMinimum_mem R U h, ?_⟩
  intro n hn
  exact Nat.sInf_le hn

private theorem map_relative_centralizer (e : G ≃* H) (R A : Subgroup G) :
    (R ⊓ centralizer (A : Set G)).map (e : G →* H) =
      R.map (e : G →* H) ⊓ centralizer (A.map (e : G →* H) : Set H) := by
  rw [map_inf _ _ _ e.injective]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ z hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact (e.map_mul a x).symm.trans ((congrArg e (hx a ha)).trans (e.map_mul x a))
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro a ha
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hy (e a) (mem_map_of_mem _ ha)

private theorem quotient_rank_map (e : G ≃* H) (U A : Subgroup G) (hAU : A ≤ U)
    [Finite U] [IsMulCommutative U] :
    Group.rank (U ⧸ A.subgroupOf U) =
      Group.rank (U.map (e : G →* H) ⧸
        (A.map (e : G →* H)).subgroupOf (U.map (e : G →* H))) := by
  have hsub : (A.subgroupOf U).map (e.subgroupMap U) =
      (A.map (e : G →* H)).subgroupOf (U.map (e : G →* H)) := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [mem_subgroupOf]
      exact mem_map_of_mem (e : G →* H) (mem_subgroupOf.mp ha)
    · intro hy
      have ha : e.symm y ∈ A := mem_map_equiv.mp (mem_subgroupOf.mp hy)
      refine ⟨⟨e.symm y, hAU ha⟩, mem_subgroupOf.mpr ha, ?_⟩
      exact Subtype.ext (e.apply_symm_apply (y : H))
  rw [← hsub]
  exact Group.rank_congr (QuotientGroup.congr _ _ (e.subgroupMap U) rfl)

private theorem centralizerRankValues_map_mem (e : G ≃* H) (R U : Subgroup G)
    [Finite U] [IsMulCommutative U] {n : ℕ}
    (hn : n ∈ centralizerRankValues R U) :
    n ∈ centralizerRankValues (R.map (e : G →* H)) (U.map (e : G →* H)) := by
  obtain ⟨A, hAU, hC, rfl⟩ := hn
  refine ⟨A.map (e : G →* H), map_mono hAU, ?_, (quotient_rank_map e U A hAU).symm⟩
  rw [← map_relative_centralizer, ← map_relative_centralizer]
  exact (e.mapSubgroup.strictMono hC)

public theorem centralizerRankValues_map (e : G ≃* H) (R U : Subgroup G)
    [Finite U] [IsMulCommutative U] :
    let : Finite (U.map (e : G →* H)) := Finite.of_equiv U (e.subgroupMap U).toEquiv
    centralizerRankValues (R.map (e : G →* H)) (U.map (e : G →* H)) =
      centralizerRankValues R U := by
  ext n
  constructor
  · intro hn
    have hh := centralizerRankValues_map_mem e.symm _ _ hn
    have he : (e.symm : H →* G).comp (e : G →* H) = MonoidHom.id G := by
      ext x
      simp
    have hU : (U.map (e : G →* H)).map (e.symm : H →* G) = U := by
      rw [map_map, he, map_id]
    have hR : (R.map (e : G →* H)).map (e.symm : H →* G) = R := by
      rw [map_map, he, map_id]
    have hRvals :
        centralizerRankValues (map (e.symm : H →* G) (map (e : G →* H) R))
            (map (e.symm : H →* G) (map (e : G →* H) U)) =
          centralizerRankValues R (map (e.symm : H →* G) (map (e : G →* H) U)) := by
      congr 1
    have hUvals : centralizerRankValues R (map (e.symm : H →* G) (map (e : G →* H) U)) =
        centralizerRankValues R U := by
      congr 1
    exact hUvals ▸ hRvals ▸ hh
  · exact centralizerRankValues_map_mem e R U

public theorem centralizerRankMinimum_map (e : G ≃* H) (R U : Subgroup G)
    [Finite U] [IsMulCommutative U] :
    let : Finite (U.map (e : G →* H)) := Finite.of_equiv U (e.subgroupMap U).toEquiv
    centralizerRankMinimum (R.map (e : G →* H)) (U.map (e : G →* H)) =
      centralizerRankMinimum R U := by
  exact congrArg sInf (centralizerRankValues_map e R U)

public theorem centralizerRankMinimum_conj (R U : Subgroup G) {x : G} [Finite U]
    [IsMulCommutative U] (hx : x ∈ normalizer (R : Set G)) :
    let : Finite (U.map (MulAut.conj x⁻¹ : G →* G)) :=
      Finite.of_equiv U ((MulAut.conj x⁻¹).subgroupMap U).toEquiv
    centralizerRankMinimum R (U.map (MulAut.conj x⁻¹ : G →* G)) =
      centralizerRankMinimum R U := by
  have hR : R.map (MulAut.conj x⁻¹ : G →* G) = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hx)
  simpa only [hR] using centralizerRankMinimum_map (MulAut.conj x⁻¹) R U

/-- Below the minimum quotient rank, a subgroup has the same centralizer. -/
public theorem centralizer_eq_of_quotient_rank_lt_minimum (R U A : Subgroup G)
    [Finite U] [IsMulCommutative U] (hAU : A ≤ U)
    (hrank : Group.rank (U ⧸ A.subgroupOf U) < centralizerRankMinimum R U) :
    R ⊓ centralizer (A : Set G) = R ⊓ centralizer (U : Set G) := by
  have hle : R ⊓ centralizer (U : Set G) ≤ R ⊓ centralizer (A : Set G) :=
    inf_le_inf_left R (centralizer_le hAU)
  by_contra hne
  have hlt := lt_of_le_of_ne hle (Ne.symm hne)
  exact (not_lt_of_ge (centralizerRankMinimum_le R U A hAU hlt)) hrank

/-- The smaller subgroup `C_V(U)` has a strictly larger centralizer in `R`
whenever `U ≤ R` and `V` does not centralize `U`. -/
public theorem centralizer_lt_centralizer_inf_of_not_le (R U V : Subgroup G)
    (hUR : U ≤ R) (hnot : ¬ V ≤ centralizer (U : Set G)) :
    R ⊓ centralizer (V : Set G) <
      R ⊓ centralizer (V ⊓ centralizer (U : Set G) : Set G) := by
  refine lt_iff_le_not_ge.mpr ⟨inf_le_inf_left R (centralizer_le inf_le_left), ?_⟩
  intro hle
  apply hnot
  apply le_centralizer_iff.mp
  intro u hu
  apply (hle ?_).2
  refine ⟨hUR hu, ?_⟩
  intro a ha
  exact (ha.2 u hu).symm

end Subgroup
