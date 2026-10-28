module

public import CFSG.Quasithin.ChapterE.Section05.Defs
public import Theory.ElementaryAbelian.BinaryQuotientRank

/-!
# Elementary steps of the higher Thompson weak-closure argument

The core-generated subgroup `W` is normal in the local group `K`: conjugating
a defining elementary subgroup preserves its order and keeps it in `O₂(K) ≤ P`.
This proves the normality clause of E.5.1 without any extra centralizer bound.
The omega-center of the higher Thompson subgroup lies in the local E-member
because it centralizes the original elementary subgroup and hence lies in tau.
Indices at or beyond the two-rank give the trivial Thompson subgroup.

The remaining E.5.1 assertion, containment of that omega-center in `Ω₁(Z(W))`,
is not asserted here. The quotient-dimension bridge at the end identifies the
small-index condition used in E.5.2 with its source meaning.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, first paragraph of the proof of E.5.1, printed p.242.
-/

open Subgroup Stellmacher CFSG.Quasithin.ChapterB
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

public theorem higherThompsonCenter_le (P : Subgroup G) (k : ℕ) :
    higherThompsonCenter P k ≤ P := by
  intro x hx
  exact thompsonJ_le P k ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1

public theorem higherThompsonCenter_centralizes (P : Subgroup G) (k : ℕ) :
    higherThompsonCenter P k ≤ centralizer (thompsonJ P k : Set G) := by
  intro x hx
  exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2

public theorem thompsonJ_eq_bot_of_rank_le (P : Subgroup G) (k : ℕ) (hk : twoRank P ≤ k) :
    thompsonJ P k = ⊥ := by
  apply bot_unique
  apply sSup_le
  intro A hA
  have hcard : Nat.card A = 1 := by
    rw [hA.2.2.2, Nat.sub_eq_zero_of_le hk, pow_zero]
  exact le_of_eq ((Subgroup.card_eq_one).mp hcard)

public theorem higherThompsonCenter_eq_bot_of_rank_le (P : Subgroup G) (k : ℕ)
    (hk : twoRank P ≤ k) : higherThompsonCenter P k = ⊥ := by
  apply bot_unique
  intro x hx
  have hxJ := ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  rwa [thompsonJ_eq_bot_of_rank_le P k hk] at hxJ

public theorem higherThompsonCore_le_core (P K : Subgroup G) (k : ℕ) :
    higherThompsonCore P K k ≤ (pCore 2 K).map K.subtype :=
  sSup_le fun _ hB => hB.2

public theorem higherThompsonCore_le (P K : Subgroup G) (k : ℕ) :
    higherThompsonCore P K k ≤ K :=
  (higherThompsonCore_le_core P K k).trans (map_subtype_le _)

public theorem higherThompsonCore_le_thompsonJ (P K : Subgroup G) (k : ℕ) :
    higherThompsonCore P K k ≤ thompsonJ P k :=
  sSup_le fun _ hB => le_sSup hB.1

private theorem map_higherThompsonCore_le (P K : Subgroup G) (k : ℕ)
    (hQP : (pCore 2 K).map K.subtype ≤ P) (x : G) (hx : x ∈ K) :
    (higherThompsonCore P K k).map (MulAut.conj x).toMonoidHom ≤
      higherThompsonCore P K k := by
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro B hB
  rw [← map_le_iff_le_comap]
  have hBc : B.map (MulAut.conj x).toMonoidHom ≤ (pCore 2 K).map K.subtype := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hB.2 hb
    refine ⟨(⟨x, hx⟩ : K) * q * (⟨x, hx⟩ : K)⁻¹, ?_, rfl⟩
    exact (inferInstance : (pCore 2 K).Normal).conj_mem q hq ⟨x, hx⟩
  apply le_sSup
  let _ : IsElementaryAbelian 2 B := hB.1.2.1
  refine ⟨⟨hBc.trans hQP, IsElementaryAbelian.map _, hB.1.2.2.1, ?_⟩, hBc⟩
  rw [card_map_of_injective (MulAut.conj x).injective]
  exact hB.1.2.2.2

public theorem higherThompsonCore_normal (P K : Subgroup G) (k : ℕ)
    (hQP : (pCore 2 K).map K.subtype ≤ P) :
    ((higherThompsonCore P K k).subgroupOf K).Normal := by
  apply (normal_subgroupOf_iff (higherThompsonCore_le P K k)).mpr
  intro w x hw hx
  exact map_higherThompsonCore_le P K k hQP x hx (mem_map_of_mem _ hw)

public theorem IsEMember.core_le {P A K : Subgroup G} (hK : IsEMember P A K) :
    (pCore 2 K).map K.subtype ≤ P := by
  obtain ⟨S, hS⟩ := hK.2.2.2.2.1
  have hq : pCore 2 K ≤ P.subgroupOf K := by
    rw [← hS]
    exact pCore_isPGroup.le_sylow_of_normal S
  rintro _ ⟨q, hq', rfl⟩
  exact hq hq'

public theorem proposition_E_5_1_normality (P : Sylow 2 G) (A K : Subgroup G) (i j : ℕ)
    (hK : IsEMemberAt j (P : Subgroup G) A K) :
    ((higherThompsonCore (P : Subgroup G) K (i + j)).subgroupOf K).Normal :=
  higherThompsonCore_normal _ K (i + j) hK.1.core_le

public theorem normalizer_le_normalizer_thompsonJ (P : Subgroup G) (i : ℕ) :
    normalizer (P : Set G) ≤ normalizer (thompsonJ P i : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change P.map (MulAut.conj x).toMonoidHom = P at hx
  have h := thompsonJ_map_equiv (MulAut.conj x) P i
  rw [hx] at h
  exact h.symm

public theorem normalizer_le_normalizer_higherThompsonCenter (P : Subgroup G) (i : ℕ) :
    normalizer (P : Set G) ≤ normalizer (higherThompsonCenter P i : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq] at hx ⊢
  change P.map (MulAut.conj x).toMonoidHom = P at hx
  change (omegaOneCenterAmbient (thompsonJ P i)).map (MulAut.conj x).toMonoidHom = _
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj x).injective,
    ← thompsonJ_map_equiv, hx]
  rfl

public theorem higherThompsonCenter_le_centralizer (P A : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hij : i + j < twoRank P) :
    higherThompsonCenter P (i + j) ≤ centralizer (A : Set G) := by
  apply (higherThompsonCenter_centralizes P (i + j)).trans
  apply centralizer_le
  exact (show A ≤ thompsonJ P i from le_sSup hA).trans
    (lemma_B_2_3_1 P (Nat.le_add_right i j) hij)

public theorem higherThompsonCenter_le_member (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hK : IsEMember P A K)
    (hij : i + j < twoRank P) : higherThompsonCenter P (i + j) ≤ K := by
  have hDC : higherThompsonCenter P (i + j) ≤ P ⊓ centralizer (A : Set G) :=
    le_inf (higherThompsonCenter_le P (i + j))
      (higherThompsonCenter_le_centralizer P A i j hA hij)
  have hDtau : higherThompsonCenter P (i + j) ≤ tau P A := by
    intro d hd
    obtain ⟨hdP, hdC⟩ := hDC hd
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hdP, fun a ha => ?_⟩
    have hc := mem_centralizer_iff.mp hdC a ha
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
    exact (pCore 2 G).one_mem
  exact hDtau.trans (hK.2.2.2.1.trans inf_le_right)

/-- The small-index condition is exactly the dimension bound on the
actual elementary abelian quotient `D/D₁`. -/
public theorem mem_smallIndexSubgroups_iff_quotient_finrank (D D₁ : Subgroup G)
    [IsElementaryAbelian 2 D] (k : ℕ) :
    D₁ ∈ smallIndexSubgroups D k ↔ D₁ ≤ D ∧
      Module.finrank (ZMod 2) (Additive (D ⧸ D₁.subgroupOf D)) ≤ k := by
  change (D₁ ≤ D ∧ Nat.log 2 (D₁.relIndex D) ≤ k) ↔ _
  rw [log_relIndex_eq_quotient_finrank]

end CFSG.Quasithin.ChapterE
