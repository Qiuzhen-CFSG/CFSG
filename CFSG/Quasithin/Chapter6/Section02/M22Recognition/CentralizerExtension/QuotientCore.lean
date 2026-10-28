module
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.InvariantEight.QuotientData
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# The two-core detected by the compatible symmetric-five quotient

In the literal quotient M/V ≃ S₅, the image of L is A₅. If V is a
two-group contained in L, restricting that same quotient map to L
shows V = O₂(L), since A₅ has trivial two-core. The proof preserves
the marking and does not use a splitting or a block classification.

This discharges the core-equality input in the Chapter 6 centralizer
construction once its compatible quotient is supplied.
Source: Aschbacher–Smith, Proposition 6.2.13, printed pp.687–688.
-/
public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
private theorem alternatingFive_twoCore : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 5))
      (N := pCore 2 (alternatingGroup (Fin 5))) with h | h
  · exact h
  · have hc : Nat.card (pCore 2 (alternatingGroup (Fin 5))) = 60 := by
      rw [h, Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin]
      decide
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))).exists_card_eq
    have hd : 3 ∣ 2 ^ n := hn ▸ hc.symm ▸ (by decide : 3 ∣ 60)
    exact False.elim ((by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))

/-- The marked alternating-five preimage has exactly the given binary kernel. -/
theorem CompatibleSymmetricFiveQuotient.kernel_eq_layer_twoCore
    {M : Type*} [Group M] [Finite M] {V L : Subgroup M} [V.Normal]
    (hq : CompatibleSymmetricFiveQuotient V L) (hV : IsPGroup 2 V) :
    V = L.pCoreIn 2 := by
  obtain ⟨e, hL⟩ := hq.quotient
  let q := e.toMonoidHom.comp (QuotientGroup.mk' V)
  have hk : q.ker = V :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' V) e).trans (QuotientGroup.ker_mk' V)
  let f := q.subgroupMap L
  have hf : Function.Surjective f := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hfk : f.ker = V.subgroupOf L := by
    change (q.subgroupMap L).ker = V.subgroupOf L
    rw [L.ker_subgroupMap q, hk]
  have hp : IsPGroup 2 f.ker := hfk ▸ hV.comap_subtype
  have htarget : pCore 2 (L.map q) = ⊥ := by
    rw [hL]
    exact alternatingFive_twoCore
  have he := f.comap_pCore_of_ker_isPGroup hf hp
  rw [htarget, MonoidHom.comap_bot, hfk] at he
  rw [pCoreIn, ← he, map_subgroupOf_eq_of_le hq.kernel_le_layer]
end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
