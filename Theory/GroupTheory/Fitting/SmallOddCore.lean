module
public import Theory.GroupTheory.SmallFittingResidual
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Odd core with a small three-group Fitting subgroup

If F(D) = O₃(D) has order at most three and the odd core is solvable,
then O(D) = O₃(D). Subnormal monotonicity embeds the odd core's Fitting
subgroup into F(D). Its automorphism group is a two-group, so the odd
core centralizes it. Fitting self-centralization then makes the entire
odd core a three-group.

Source application: Aschbacher–Smith, 14.7.28, printed p.1055,
refs/quasithin.pdf. Solvability of the odd core is retained as an input
so this finite-group lemma does not depend on a classification campaign.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

theorem oddCore_eq_threeCore_of_small_fitting
    {D : Type*} [Group D] [Finite D]
    (hs : Group.IsSolvable (pPrimeCore 2 D))
    (hf : fittingSubgroup D = pCore 3 D) (hc : Nat.card (pCore 3 D) ≤ 3) :
    pPrimeCore 2 D = pCore 3 D := by
  let O := pPrimeCore 2 D
  let B := fittingSubgroup O
  have hBD : B.map O.subtype ≤ pCore 3 D := by
    rw [←hf]
    exact le_sSup ⟨fittingSubgroupOf_normal O inferInstance, fittingSubgroupOf_isNilpotent O⟩
  have hB3 : IsPGroup 3 B := (pCore_isPGroup.to_le hBD).of_equiv
    (equivMapOfInjective B O.subtype O.subtype_injective).symm
  have hBc : Nat.card B = 1 ∨ Nat.card B = 3 := by
    have hb := (card_le_of_le hBD).trans hc
    rw [card_map_of_injective O.subtype_injective] at hb
    obtain ⟨n,hn⟩ := hB3.exists_card_eq
    by_cases hz : n = 0
    · exact Or.inl (by rw [hn,hz,pow_zero])
    · right
      exact le_antisymm hb (Nat.le_of_dvd Nat.card_pos (hn ▸ dvd_pow_self 3 hz))
  have hOp : IsPPerfect 2 O := by
    apply (pResidual_eq_top_iff 2 O).mp
    apply top_unique
    intro x _
    exact mem_pResidual_of_orderOf_coprime
      (pPrimeCore_coprime_card.of_dvd_right (orderOf_dvd_natCard x))
  have ha := hOp.hom_eq_one_of_isPGroup (aut_two_of_card_one_or_three B hBc)
    (MulAut.conjNormal : O →* MulAut B)
  have hcentral : centralizer (B : Set O) = ⊤ := by
    rw [←MulAut.conjNormal_ker_eq_centralizer,ha]
    exact MonoidHom.ker_one
  have hBtop : B = ⊤ := top_unique (hcentral ▸
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hs)
  have hO3 : IsPGroup 3 O := (hBtop ▸ hB3).of_equiv (topEquiv : (⊤ : Subgroup O) ≃* O)
  have hOP : O ≤ pCore 3 D := le_sSup ⟨inferInstance,hO3⟩
  have hcop : Nat.Coprime 2 (Nat.card (pCore 3 D)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := D)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n
  exact le_antisymm hOP
    (le_sSup ⟨inferInstanceAs ((pCore 3 D).Normal),hcop⟩)

end Theory.GroupTheory
