module

public import CFSG.Quasithin.ChapterE.Section05.RankBridge

/-!
# The rank argument in the no-FF alternative

A Thompson subgroup contained in a normal subgroup of its Sylow group is
normal: each conjugate of a defining elementary subgroup has the same order
and remains in the Sylow group. Thus failure of normality supplies a maximum
elementary subgroup escaping the two-core.

For the core-generated subgroup W, the existing E-member rank bridge puts
A ∩ O₂(G) in W. The elementary product bound then gives the sharper inequality
m(E/C_E(A)) ≤ m(AO₂(G)/O₂(G)), with E = Ω₁(Z(W)). This is the numerical input
to the chief-section argument; no action on a chief section is assumed here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.5.4,
printed p.244, using the last paragraph of E.5.2 on p.243.
-/

open Subgroup Stellmacher

namespace CFSG.Quasithin.ChapterE.NoFFAlternative
open ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- Containment in a normal subgroup inside P makes any fixed-rank Thompson
subgroup normal. In particular this applies to O₂(G). -/
public theorem thompsonJ_normal_of_le_normal (P Q : Subgroup G) [Q.Normal]
    (i : ℕ) (hQP : Q ≤ P) (hJ : thompsonJ P i ≤ Q) :
    (thompsonJ P i).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hmap : (thompsonJ P i).map (MulAut.conj g).toMonoidHom ≤ thompsonJ P i := by
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    rw [← map_le_iff_le_comap]
    apply le_sSup
    let _ : IsElementaryAbelian 2 A := hA.2.1
    refine ⟨?_, IsElementaryAbelian.map _, hA.2.2.1, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact hQP ((inferInstance : Q.Normal).conj_mem a (hJ ((le_sSup hA) ha)) g)
    · rw [card_map_of_injective (MulAut.conj g).injective]
      exact hA.2.2.2
  exact hmap (mem_map_of_mem _ hx)

/-- The first paragraph of E.5.4 supplies an actual maximum elementary
subgroup with nontrivial image modulo the two-core. -/
public theorem exists_maximum_escaping_core (P : Sylow 2 G)
    (hJ : ¬ (thompsonJ (P : Subgroup G) 0).Normal) :
    ∃ A ∈ thompsonFamily (P : Subgroup G) 0, ¬ A ≤ pCore 2 G := by
  classical
  by_contra! h
  exact hJ (thompsonJ_normal_of_le_normal (P : Subgroup G) (pCore 2 G) 0
    (pCore_isPGroup.le_sylow_of_normal P) (sSup_le h))

omit [Finite G] in
/-- The intrinsic two-core of the top subgroup maps to the ambient two-core. -/
public theorem top_core_map :
    (pCore 2 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = pCore 2 G :=
  pCore_map_iso 2 Subgroup.topEquiv

/-- The elementary group used in E.5.4 is normal before invoking E.5.1. -/
public theorem core_center_normal (P : Sylow 2 G) (j : ℕ) :
    (omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) ⊤ j)).Normal := by
  let W := higherThompsonCore (P : Subgroup G) ⊤ j
  have hWP : (pCore 2 (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype ≤
      (P : Subgroup G) := by
    rw [top_core_map]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hn : (⊤ : Subgroup G) ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (higherThompsonCore_le (P : Subgroup G) ⊤ j)).mp
      (higherThompsonCore_normal (P : Subgroup G) ⊤ j hWP)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  have hg := hn (mem_top g)
  rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
  change W.map (MulAut.conj g).toMonoidHom = W at hg
  change (omegaOneCenterAmbient W).map (MulAut.conj g).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective, hg]

/-- The rank-degenerate case already gives both clauses of alternative (2). -/
public theorem residual_centralizes_and_normal_of_rank_le (P : Sylow 2 G)
    (j : ℕ) (hj : twoRank (P : Subgroup G) ≤ j) :
    pResidual 2 G ≤ centralizer (higherThompsonCenter (P : Subgroup G) j : Set G) ∧
      (higherThompsonCenter (P : Subgroup G) j).Normal := by
  have he := higherThompsonCenter_eq_bot_of_rank_le (P : Subgroup G) j hj
  have hc : pResidual 2 G ≤ centralizer (higherThompsonCenter (P : Subgroup G) j : Set G) := by
    rw [he, centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup G) ≤ center G from bot_le)]
    exact le_top
  exact ⟨hc, higherThompsonCenter_normal_of_residual_centralizes P j hc⟩

/-- Sharp displacement bound before passage to a chief section. The right
side is the actual image rank, not merely its upper bound j. -/
public theorem core_center_displacement_le (P : Sylow 2 G) (A K : Subgroup G)
    (j : ℕ) (hj : j < twoRank (P : Subgroup G))
    (hA : A ∈ thompsonFamily (P : Subgroup G) 0)
    (hK : IsEMemberAt j (P : Subgroup G) A K) :
    let E := omegaOneCenterAmbient (higherThompsonCore (P : Subgroup G) K j)
    Nat.log 2 ((E ⊓ centralizer (A : Set G)).relIndex E) ≤
      Nat.log 2 ((A ⊓ (pCore 2 K).map K.subtype).relIndex A) := by
  let W := higherThompsonCore (P : Subgroup G) K j
  let E := omegaOneCenterAmbient W
  let B := A ⊓ (pCore 2 K).map K.subtype
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian W
  have hBW : B ≤ W := by
    simpa only [Nat.zero_add] using
      inf_core_le_higherThompsonCore (P : Subgroup G) A K 0 j hA
        (by simpa only [Nat.zero_add] using hj) hK.core_rank_le
  have hWE : W ≤ centralizer (E : Set G) := by
    apply le_centralizer_iff.mp
    intro e he
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff W e).mp he).2.2
  have hEP : E ≤ (P : Subgroup G) := by
    intro e he
    exact hK.1.core_le (higherThompsonCore_le_core (P : Subgroup G) K j
      ((mem_omegaOneCenterAmbient_iff W e).mp he).1)
  have hr := elementary_relativeIndex_le_of_thompsonFamily (P : Subgroup G) A B E
    hA inf_le_left (le_rfl : Nat.log 2 (B.relIndex A) ≤ Nat.log 2 (B.relIndex A))
    hEP (hBW.trans hWE)
  have hBC : B ≤ centralizer (A : Set G) :=
    inf_le_left.trans (le_centralizer_iff_isMulCommutative.mpr
      (inferInstance : IsMulCommutative A))
  have hi : (E ⊓ centralizer (A : Set G)).relIndex E ≤ (E ⊓ B).relIndex E :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero ((E ⊓ B).subgroupOf E).index_ne_zero_of_finite)
      (relIndex_dvd_of_le_left E (inf_le_inf_left E hBC))
  exact (Nat.log_mono_right hi).trans (by simpa only [Nat.zero_add] using hr)

end CFSG.Quasithin.ChapterE.NoFFAlternative
