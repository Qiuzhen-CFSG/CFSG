module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Normalization
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalCore
public import Theory.GroupTheory.SylowLocalCore
public import Theory.GroupTheory.PResidual.PerfectLift
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Sylow selection and normalization from the local A₆ quotient

Extend T_v first to a Sylow subgroup of N_Gv(L_v), then to a Sylow subgroup
S of G_v. This constructs the source alignment while retaining the original
v and T_v. The core O₂(KS) lies in S and acts trivially in the star quotient,
so it lies in the original R. The ambient Sylow T bounds |S:T_v|; the proved
intersection R ∩ T_v = R_v then bounds |R:R_v|.

The actual A₆ equivalence gives centerlessness and perfection of L_v,
including its equality with the separate solvable residual of C_L(v).
Together these results discharge the kernel, perfection and small-index
premises in the existing proof of all three clauses of Lemma 12.6.5.

The preceding source constructions still have to identify L_v/O₂(L_v) as A₆,
place T_v in Syl₂(C_LT(v)), give |T:T_v|=4, and embed L_v in the canonical K_v.
These are explicit model/component inputs, not consequences asserted here.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Section 12.6 and Lemmas 12.6.3--5, printed pp.823--824.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The source choice of S is possible without changing the original v or Tv. -/
theorem exists_sylow_with_Lv_normalizer (T : Sylow 2 G) (L : Subgroup G)
    (hT : (T : Subgroup G) ≤ M L) (v : G) :
    ∃ S : Sylow 2 (Gv v),
      Tv T v ≤ (S : Subgroup (Gv v)).map (Gv v).subtype ∧
      ∃ P : Sylow 2 (Gv v ⊓ normalizer (Lv L v : Set G) : Subgroup G),
        (P : Subgroup (Gv v ⊓ normalizer (Lv L v : Set G) : Subgroup G)).map
          (Gv v ⊓ normalizer (Lv L v : Set G)).subtype =
        (S : Subgroup (Gv v)).map (Gv v).subtype ⊓ normalizer (Lv L v : Set G) := by
  let N := (normalizer (Lv L v : Set G)).subgroupOf (Gv v)
  have hTvN : Tv T v ≤ Gv v ⊓ normalizer (Lv L v : Set G) :=
    le_inf inf_le_right ((inf_le_inf hT le_rfl).trans (Mv_le_normalizer_Lv L v))
  let A := (Tv T v).subgroupOf (Gv v)
  have hp : IsPGroup 2 A := (T.isPGroup'.to_le (show Tv T v ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  obtain ⟨P, hP⟩ := (hp.comap_subtype (K := N)).exists_le_sylow
  obtain ⟨S, hS⟩ := P.exists_comap_subtype_eq
  have hAS : A ≤ S := by
    intro a ha
    have haN : a ∈ N := (hTvN ha).2
    have hs := hP (show (⟨a, haN⟩ : N) ∈ A.subgroupOf N from ha)
    rwa [← hS] at hs
  have hTvS : Tv T v ≤ (S : Subgroup (Gv v)).map (Gv v).subtype := by
    intro a ha
    exact ⟨⟨a, ha.2⟩, hAS ha, rfl⟩
  let e : N ≃* (Gv v ⊓ normalizer (Lv L v : Set G) : Subgroup G) := {
    toFun n := ⟨n.1.1, n.1.2, n.2⟩
    invFun n := ⟨⟨n.1, n.2.1⟩, n.2.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨S, hTvS, P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rw [← hS] at hz
    exact ⟨⟨z.val, hz, rfl⟩, z.property⟩
  · rintro ⟨⟨y, hy, rfl⟩, hn⟩
    exact ⟨⟨y, y.property, hn⟩, ⟨⟨y, hn⟩, hS ▸ hy, rfl⟩, rfl⟩

omit [Finite G] in
/-- The kernel of the actual star quotient lies in R by construction. -/
theorem core_le_R_of_sylow (L K : Subgroup G) (v : G)
    (S : Sylow 2 (Gv v)) (hK : K ≤ Gv v) :
    (K ⊔ (S : Subgroup (Gv v)).map (Gv v).subtype).pCoreIn 2 ≤
      R L K ((S : Subgroup (Gv v)).map (Gv v).subtype) v := by
  let S₀ := (S : Subgroup (Gv v)).map (Gv v).subtype
  let H := K ⊔ S₀
  have hH : H ≤ Gv v := sup_le hK (map_subtype_le _)
  obtain ⟨P, hP⟩ := S.exists_map_subtype_eq_of_le hH (show S₀ ≤ H from le_sup_right)
  have hcS : H.pCoreIn 2 ≤ S₀ := (pCoreIn_le_sylow H P).trans hP.le
  intro x hx
  refine ⟨hcS hx, ?_⟩
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ?_, rfl⟩
  change QuotientGroup.mk' (pCore 2 H) a ∈ coreQuotientCentralizer (starImage H (Lv L v))
  have hq : QuotientGroup.mk' (pCore 2 H) a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
  rw [hq]
  exact one_mem _

/-- An ambient Sylow bounds the index of Tv in every two-subgroup containing it. -/
theorem Tv_relIndex_le (T : Sylow 2 G) (v : G) (S : Subgroup G)
    (hp : IsPGroup 2 S) (hTvS : Tv T v ≤ S) :
    (Tv T v).relIndex S ≤ (Tv T v).relIndex (T : Subgroup G) := by
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hcard : Nat.card S ≤ Nat.card (T : Subgroup G) :=
    (card_le_of_le hP).trans_eq (Nat.card_congr (P.equiv T).toEquiv)
  have h₁ := relIndex_mul_relIndex (⊥ : Subgroup G) (Tv T v) S bot_le hTvS
  have h₂ := relIndex_mul_relIndex (⊥ : Subgroup G) (Tv T v) (T : Subgroup G) bot_le inf_le_left
  simp only [relIndex_bot_left] at h₁ h₂
  exact (Nat.mul_le_mul_left_iff (Nat.card_pos (α := Tv T v))).mp
    (h₁.trans_le (hcard.trans_eq h₂.symm))

/-- Both index inequalities in 12.6.4, with the literal R and Rv. -/
theorem nonsingular_local_index_bounds (T : Sylow 2 G) (L K : Subgroup G) (v : G)
    (S : Sylow 2 (Gv v))
    (hTvS : Tv T v ≤ (S : Subgroup (Gv v)).map (Gv v).subtype)
    (hRv : Rv T L v = R L K ((S : Subgroup (Gv v)).map (Gv v).subtype) v ⊓ Tv T v)
    (hi : (Tv T v).relIndex (T : Subgroup G) = 4) :
    (Tv T v).relIndex ((S : Subgroup (Gv v)).map (Gv v).subtype) ≤ 4 ∧
      (Rv T L v).relIndex (R L K ((S : Subgroup (Gv v)).map (Gv v).subtype) v) ≤ 4 := by
  have hs := Tv_relIndex_le T v _ (S.isPGroup'.map _) hTvS
  rw [hi] at hs
  refine ⟨hs, ?_⟩
  rw [hRv, inf_relIndex_left]
  exact (relIndex_le_of_le_right (R_le_S _ _ _ _) index_ne_zero_of_finite).trans hs

end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

theorem Lv_isPerfect_of_A6 (L : Subgroup G) (v : G)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6)) : Group.IsPerfect (Lv L v) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Star (Lv L v)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hp : IsPPerfect 2 (Lv L v) := isPPerfect_embedded_pResidual 2 (CLv L v)
  apply hp.isPerfect_of_surjective_pGroup_kernel
    (QuotientGroup.mk' (pCore 2 (Lv L v))) (QuotientGroup.mk'_surjective _)
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup

omit [Finite G] in
theorem Lv_coreQuotient_center_eq_bot_of_A6 (L : Subgroup G) (v : G)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6)) : center (Star (Lv L v)) = ⊥ := by
  apply bot_unique
  intro x hx
  have hc : e x ∈ center (alternatingGroup (Fin 6)) := by
    rw [mem_center_iff] at hx ⊢
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx z)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at hc
  exact mem_bot.mpr (e.injective (hc.trans e.map_one.symm))

theorem Lv_eq_LvInfinity_of_A6 (L : Subgroup G) (v : G)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6)) : Lv L v = LvInfinity L v := by
  let := Lv_isPerfect_of_A6 L v e
  apply le_antisymm
  · exact le_map_solvableResidual_of_isPerfect (Lv L v) (CLv L v) (map_subtype_le _)
  · apply map_mono
    let : Group.IsNilpotent (CLv L v ⧸ pResidual 2 (CLv L v)) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact solvableResidual_le_of_solvable_quotient _
end CFSG.Quasithin.Chapter12.Section06

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- All three clauses of 12.6.5 from the preceding A₆/component and Sylow
inputs. In particular neither the small R-index nor the core containment
nor the intersection R∩T_v=R_v is supplied as an independent hypothesis. -/
theorem nonsingular_normalization_of_A6 (T : Sylow 2 G) (L K : Subgroup G) (v : G)
    (hT : (T : Subgroup G) ≤ M L) (hK : K ≤ Gv v) (hLK : Lv L v ≤ K)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 (LT T L ⊓ Gv v : Subgroup G))
    (hP : (P : Subgroup (LT T L ⊓ Gv v : Subgroup G)).map
      (LT T L ⊓ Gv v).subtype = Tv T v)
    (hi : (Tv T v).relIndex (T : Subgroup G) = 4)
    (S : Sylow 2 (Gv v))
    (hTvS : Tv T v ≤ (S : Subgroup (Gv v)).map (Gv v).subtype) :
    let S₀ := (S : Subgroup (Gv v)).map (Gv v).subtype
    R L K S₀ v ≤ normalizer (Lv L v : Set G) ∧
      ⁅Lv L v, R L K S₀ v⁆ ≤ (Lv L v).pCoreIn 2 ∧
      R L K S₀ v = S₀ ⊓ coreQuotientCentralizer (Lv L v) := by
  let S₀ := (S : Subgroup (Gv v)).map (Gv v).subtype
  let := Lv_isPerfect_of_A6 L v e
  have hcore := core_le_R_of_sylow L K v S hK
  have hRv : Rv T L v = R L K S₀ v ⊓ Tv T v :=
    (R_inf_Tv_eq_Rv T L K S₀ v hT hLK hTvS P hP
      (Lv_coreQuotient_center_eq_bot_of_A6 L v e)).symm
  have hindex := (nonsingular_local_index_bounds T L K v S hTvS hRv hi).2
  exact ⟨R_le_normalizer_Lv T L K S₀ v hT hLK hcore hindex,
    commutator_Lv_R_le_core T L K S₀ v hT hLK hcore hindex,
    R_eq_S_inf_coreQuotientCentralizer T L K S₀ v hT hLK hcore hindex⟩

/-- Application to the literal canonical K_v. The Sylow subgroup is constructed,
and the quotient centralizer is identified without replacing its definition. -/
theorem exists_nonsingular_sylow_normalization (T : Sylow 2 G) (L : Subgroup G) (v : G)
    (hT : (T : Subgroup G) ≤ M L) (hLK : Lv L v ≤ Kv v)
    (e : Star (Lv L v) ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 (LT T L ⊓ Gv v : Subgroup G))
    (hP : (P : Subgroup (LT T L ⊓ Gv v : Subgroup G)).map
      (LT T L ⊓ Gv v).subtype = Tv T v)
    (hi : (Tv T v).relIndex (T : Subgroup G) = 4) :
    ∃ S : Sylow 2 (Gv v),
      let S₀ := (S : Subgroup (Gv v)).map (Gv v).subtype
      Tv T v ≤ S₀ ∧
      (∃ N : Sylow 2 (Gv v ⊓ normalizer (Lv L v : Set G) : Subgroup G),
        (N : Subgroup (Gv v ⊓ normalizer (Lv L v : Set G) : Subgroup G)).map
          (Gv v ⊓ normalizer (Lv L v : Set G)).subtype =
          S₀ ⊓ normalizer (Lv L v : Set G)) ∧
      R L (Kv v) S₀ v ≤ normalizer (Lv L v : Set G) ∧
      ⁅Lv L v, R L (Kv v) S₀ v⁆ ≤ (Lv L v).pCoreIn 2 ∧
      R L (Kv v) S₀ v = S₀ ⊓ coreQuotientCentralizer (Lv L v) := by
  obtain ⟨S, hTvS, hN⟩ := exists_sylow_with_Lv_normalizer T L hT v
  exact ⟨S, hTvS, hN, nonsingular_normalization_of_A6 T L (Kv v) v hT
    (Kv_le_Gv v) hLK e P hP hi S hTvS⟩
end CFSG.Quasithin.Chapter12.Section06
