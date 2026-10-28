module

public import CFSG.Quasithin.ChapterE.Section05.RankBridge

/-!
# Thompson generation inside the local two-core

The E-member rank bound makes A ∩ O₂(K) large enough to contain the
fixed-rank elementary subgroups defining W. Every maximum elementary
subgroup of O₂(K) is at least this large, so J(O₂(K)) lies in W.
The omega-centralizer identity from B.2.3 then puts D ∩ O₂(K) in W.
Since O₂(K) normalizes D and D lies in K, this proves [D,O₂(K)] ≤ W,
without assuming D lies in O₂(K).

Source: Aschbacher–Smith, Proposition E.5.1, printed p.242.
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterE
open ChapterB
variable {G : Type*} [Group G] [Finite G]

/-- The ordinary Thompson subgroup of the local core lies in W. -/
public theorem maxJ_core_le_higherThompsonCore (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hij : i + j < twoRank P)
    (hK : IsEMemberAt j P A K) :
    elementaryAbelianMaxJ ((pCore 2 K).map K.subtype) ≤
      higherThompsonCore P K (i + j) := by
  let Q := (pCore 2 K).map K.subtype
  let B := A ⊓ Q
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le
    (show B ≤ A from inf_le_left)
  obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 B).exists_card_eq
  have hrank := ((mem_thompsonFamily_iff_rank P A i).mp hA).2.2
  have hdiff := log_card_sub_log_card_eq_log_relIndex A B inf_le_left
  have hr := hK.core_rank_le
  change Nat.log 2 (B.relIndex A) ≤ j at hr
  rw [← hdiff, hb, Nat.log_pow Nat.one_lt_two] at hr
  have hcard : 2 ^ (twoRank P - (i + j)) ≤ Nat.card B := by
    rw [hb]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  apply sSup_le
  intro C hC
  let _ : IsElementaryAbelian 2 C := hC.2.1
  have hcardC := hcard.trans (hC.2.2 B inf_le_right inferInstance)
  intro x hx
  obtain ⟨F, hFC, heF, hcardF, hxF⟩ :=
    IsElementaryAbelian.exists_two_power_subgroup_mem C (by omega) hcardC x hx
  exact (le_sSup (show F ∈ {F : Subgroup G |
      F ∈ thompsonFamily P (i + j) ∧ F ≤ Q} from
    ⟨⟨hFC.trans (hC.1.trans hK.1.core_le), heF, hij.le, hcardF⟩,
      hFC.trans hC.1⟩)) hxF

/-- The first omega subgroup of the core centralizer of W lies in W. -/
public theorem omegaCentralizer_core_le_higherThompsonCore (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hij : i + j < twoRank P)
    (hK : IsEMemberAt j P A K) :
    omegaOneAmbient ((pCore 2 K).map K.subtype ⊓
      centralizer (higherThompsonCore P K (i + j) : Set G)) ≤
      higherThompsonCore P K (i + j) := by
  have hJ := maxJ_core_le_higherThompsonCore P A K i j hA hij hK
  have hle := omegaOneAmbient_mono (inf_le_inf_left ((pCore 2 K).map K.subtype)
    (centralizer_le hJ))
  rw [omegaCentralizer_thompson] at hle
  exact hle.trans (fun x hx => hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)

/-- The intersection D ∩ O₂(K) lies in W. -/
public theorem higherThompsonCenter_inf_core_le (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hij : i + j < twoRank P)
    (hK : IsEMemberAt j P A K) :
    higherThompsonCenter P (i + j) ⊓ (pCore 2 K).map K.subtype ≤
      higherThompsonCore P K (i + j) := by
  intro d hd
  apply omegaCentralizer_core_le_higherThompsonCore P A K i j hA hij hK
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl d
  · exact ⟨hd.2, (centralizer_le (higherThompsonCore_le_thompsonJ P K (i + j)))
      (higherThompsonCenter_centralizes P (i + j) hd.1)⟩
  · exact ((mem_omegaOneCenterAmbient_iff _ _).mp hd.1).2.1

/-- The higher Thompson center acts trivially on O₂(K)/W. -/
public theorem higherThompsonCenter_commutator_core_le (P A K : Subgroup G) (i j : ℕ)
    (hA : A ∈ thompsonFamily P i) (hij : i + j < twoRank P)
    (hK : IsEMemberAt j P A K) :
    ⁅higherThompsonCenter P (i + j), (pCore 2 K).map K.subtype⁆ ≤
      higherThompsonCore P K (i + j) := by
  apply le_trans _ (higherThompsonCenter_inf_core_le P A K i j hA hij hK)
  apply le_inf
  · exact le_normalizer_iff_commutator_le_left.mp (hK.1.core_le.trans
      (P.le_normalizer.trans (normalizer_le_normalizer_higherThompsonCenter P (i + j))))
  · apply le_normalizer_iff_commutator_le_right.mp
    apply (higherThompsonCenter_le_member P A K i j hA hK.1 hij).trans
    exact (normal_subgroupOf_iff_le_normalizer (map_subtype_le (pCore 2 K))).mp
      (by
        rw [subgroupOf, comap_map_eq_self_of_injective K.subtype_injective]
        infer_instance)

end CFSG.Quasithin.ChapterE
