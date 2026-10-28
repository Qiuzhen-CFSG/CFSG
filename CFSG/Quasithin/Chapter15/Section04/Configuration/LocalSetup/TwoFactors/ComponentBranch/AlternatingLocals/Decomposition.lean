module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.Lifting
/-!
# The corrected centralizer product

The source central line C_Z(Y) has order two and is disjoint from C_{T_I}(L)
by the faithful Z-action on L. It commutes with that centralizer because Z
centralizes T_I. The model index therefore makes their product all of
C_{T_I}(Y), with multiplication as the explicit isomorphism.

This uses the odd central line detected in S₆, rather than the printed
Z ∩ L, which fails the canonical model calculation. Source: Aschbacher–Smith
15.4.18, combined manuscript, printed p.1163.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates

/-- The central line C_Z(Y), rather than the printed Z ∩ L, gives the
internal direct product compatible with the actual S₆ calculation. -/
theorem factor_centralizer_product
    {I : Type*} [Group I] [Finite I] {L : Subgroup I} (d : QuotientCoordinates L)
    (T : Sylow 2 I) (Y Z : Subgroup I)
    (hY : IsPPerfect 2 Y) (hn : (T : Subgroup I) ≤ normalizer (Y : Set I))
    (hi : (T : Subgroup I).relIndex (Y ⊔ (T : Subgroup I)) = 3)
    (hZT : Z ≤ (T : Subgroup I)) (hTZ : (T : Subgroup I) ≤ centralizer (Z : Set I))
    (hd : Disjoint Z (centralizer (L : Set I)))
    (hc : Nat.card (Z ⊓ centralizer (Y : Set I) : Subgroup I) = 2) :
    ∃ e : ↥((T : Subgroup I) ⊓ centralizer (L : Set I)) ×
        ↥(Z ⊓ centralizer (Y : Set I)) ≃*
        ↥((T : Subgroup I) ⊓ centralizer (Y : Set I)),
      ∀ b z, (e (b, z) : I) = (b : I) * (z : I) := by
  let A := (T : Subgroup I) ⊓ centralizer (Y : Set I)
  let B := (T : Subgroup I) ⊓ centralizer (L : Set I)
  let D := Z ⊓ centralizer (Y : Set I)
  have hBA : B ≤ A := inf_le_inf_left _ (centralizer_le (d.factor_le_component Y hY))
  have hDA : D ≤ A := inf_le_inf hZT le_rfl
  have hBD : Disjoint B D := hd.symm.mono inf_le_right inf_le_left
  have hcomm : B ≤ centralizer (D : Set I) :=
    (inf_le_left.trans hTZ).trans (centralizer_le (show D ≤ Z from inf_le_left))
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting B D hBD hcomm
  have hgen : B ⊔ D = A := by
    apply eq_of_le_of_card_ge (sup_le hBA hDA)
    have hm := relIndex_mul_relIndex (⊥ : Subgroup I) B A bot_le hBA
    rw [relIndex_bot_left, relIndex_bot_left,
      d.factor_centralizer_index T Y hY hn hi] at hm
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hc]
    exact hm.ge
  exact ⟨e.trans (MulEquiv.subgroupCongr hgen), he⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.QuotientCoordinates
