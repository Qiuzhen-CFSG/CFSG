module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Simple two-core quotients of chi-zero blocks

The block models identify the actual quotient by O₂ with SL₂ in
characteristic two, A₃ or A₅. The rank-one model is centerless by the scalar
matrix calculation; its short-group quasisimplicity clause then gives
simplicity. The two alternating cases use their genuine model equivalences.

This allows a nontrivial quotient of a χ₀ core quotient to be compared by
an isomorphism, rather than by divisibility of orders alone. It is used by
the sextet branch of the M₂₄ local obstruction.

Source: Aschbacher–Smith C.1.7 and C.1.12, printed pp.123–124.
-/

public section

namespace CFSG.Quasithin.ChapterC
open Subgroup Theory.GroupTheory

private theorem simple_of_short_centerless_quotient {B : Type*} [Group B]
    (h : IsShort B) (hz : center (B ⧸ pCore 2 B) = ⊥) :
    IsSimpleGroup (B ⧸ pCore 2 B) := by
  rcases h.quotient with hq | hq
  · let := hq
    let := IsQuasisimple.simple (G := B ⧸ pCore 2 B)
    exact ((QuotientGroup.quotientMulEquivOfEq hz).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  · exact isSimpleGroup_of_prime_card hq

/-- All three χ₀ models have simple quotient by their actual two-core. -/
theorem IsChiZeroBlock.quotient_simple {B : Type*} [Group B]
    (h : IsChiZeroBlock B) : IsSimpleGroup (B ⧸ pCore 2 B) := by
  rcases h with ⟨n, _, hs, F, _, _, hF, _, hm⟩ | h | h
  · obtain ⟨e⟩ := hm.quotient_iso
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply simple_of_short_centerless_quotient hs
    apply eq_bot_iff.mpr
    intro b hb
    have hc := (centerCongr e ⟨b, hb⟩).property
    change e b ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hc
    rw [Theory.PSL2.sl2_center_eq_bot] at hc
    apply mem_bot.mpr
    apply e.injective
    exact (mem_bot.mp hc).trans (map_one e).symm
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    apply isSimpleGroup_of_prime_card (p := 3)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  · obtain ⟨e⟩ := h.2.2.quotient_iso
    let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
end CFSG.Quasithin.ChapterC

end
