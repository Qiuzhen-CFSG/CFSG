module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Basic
public import Theory.GroupTheory.NormalFourCentralizerSeparation

/-!
# Maximal-local Sylow promotion in the terminal amalgam

The geometry supplies a generation statement: a two-subgroup of `M`
properly containing `T_E`, together with `Y_F`, generates `M`. If such
a two-subgroup lies in a maximal two-local overgroup `K` of `G₀`, then
`M ≤ K`, so maximality gives `K = M`. This contradicts `X_E ≤ K` and
`X_E ≰ M`. Thus `T_E` is Sylow in `M ∩ K`. The earlier bound
`N_G(T_E) ≤ M` then promotes it to a Sylow subgroup of `K`.

The generation statement remains an explicit geometric input to this
reduction. It is not a maximal-local Sylow assumption. `K` belongs to
the genuine family of maximal two-local subgroups containing `G₀`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 15.3.68(3), printed p.1154, PDF p.1171.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
variable {G : Type*} [Group G] [Finite G]

/-- The local generation calculation rules out every larger two-subgroup in the
intersection with `M`; normalizer control then promotes Sylow maximality. -/
private theorem sylow_in_maximalLocal_of_generation (A B D H M K : Subgroup G)
    (hAH : A ≤ H) (hBH : B ≤ H) (hDH : D ≤ H) (hDM : D ≤ M)
    (hpD : IsPGroup 2 D) (hN : normalizer (D : Set G) ≤ M)
    (hM : IsMaximalTwoLocal M) (hB : ¬ B ≤ M)
    (hgen : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → D < U → M ≤ A ⊔ U)
    (hK : K ∈ Theory.GroupTheory.maximalTwoLocalOvergroups H) :
    Stellmacher.IsSylowSubgroupIn D K := by
  let L := M ⊓ K
  have hDK : D ≤ K := hDH.trans hK.2
  have hDL : D ≤ L := le_inf hDM hDK
  obtain ⟨S, hS⟩ := (hpD.comap_subtype (K := L)).exists_le_sylow
  let U : Subgroup G := (S : Subgroup L).map L.subtype
  have hDU : D ≤ U := by
    intro x hx
    exact mem_map.mpr ⟨⟨x, hDL hx⟩, hS hx, rfl⟩
  have hUL : U ≤ L := map_subtype_le _
  have hUD : U = D := by
    by_contra hne
    have hMK : M ≤ K := (hgen U (hUL.trans inf_le_left)
      (S.isPGroup'.map L.subtype) (lt_of_le_of_ne hDU (Ne.symm hne))).trans
        (sup_le (hAH.trans hK.2) (hUL.trans inf_le_right))
    have hMK' : M = K := hM.eq_of_le hK.1.1 hMK
    exact hB ((hBH.trans hK.2).trans_eq hMK'.symm)
  have hiL : ¬ 2 ∣ D.relIndex L := by
    rw [← hUD]
    change ¬ 2 ∣ (((S : Subgroup L).map L.subtype).comap L.subtype).index
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    exact S.not_dvd_index
  have hiK := not_dvd_relIndex_of_normalizer_inf_le D L K hpD hDK hiL
    (le_inf (inf_le_left.trans hN) inf_le_right)
  exact ⟨(hpD.comap_subtype (K := K)).toSylow hiK, map_subgroupOf_eq_of_le hDK⟩

/-- Specialization to the terminal Section 15.3 generators. -/
theorem amalgam_sylow_in_maximalLocals (Y T E F M : Subgroup G)
    (hpT : IsPGroup 2 T) (hTM : T ≤ M)
    (hN : normalizer (lineT T E : Set G) ≤ M)
    (hM : IsMaximalTwoLocal M) (hX : ¬ lineX E ≤ M)
    (hgen : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → lineT T E < U →
      M ≤ lineY Y F ⊔ U) :
    ∀ K ∈ Theory.GroupTheory.maximalTwoLocalOvergroups (amalgamGroup Y T E F),
      Stellmacher.IsSylowSubgroupIn (lineT T E) K := by
  intro K hK
  exact sylow_in_maximalLocal_of_generation (lineY Y F) (lineX E) (lineT T E)
    (amalgamGroup Y T E F) M K (le_sup_left.trans le_sup_left)
    (le_sup_left.trans le_sup_right) (le_sup_right.trans le_sup_left)
    (inf_le_left.trans hTM) (hpT.to_le inf_le_left) hN hM hX hgen hK

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore
