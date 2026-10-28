module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.QuotientCardSixty

/-!
# The module size of a chi-block with quotient A5

An actual core quotient of order sixty forces a natural even-field block
to have field order four, or an odd alternating block to have degree five.
Both defining module models have order sixteen. This is a statement about
U/C_U(L); it does not discard the possible central covering kernel.

Source: Aschbacher–Smith C.1.12 and 5.1.13, printed pp.124,638.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
/-- Either chi type with quotient order sixty has a sixteen-element module. -/
theorem IsChiBlock.module_card_of_quotient_card_sixty {R : Type*} [Group R]
    (hb : IsChiBlock R) (hq : Nat.card (R ⧸ pCore 2 R) = 60) :
    Nat.card (BlockModule R) = 16 := by
  rcases hb with ⟨m,hm⟩ | ⟨m,ho,hm⟩
  · have hh := (hm.four_of_quotient_card hq).module_card
    exact hh
  · have hm2 : 2 ≤ m := by have := hm.1; omega
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm2
    obtain ⟨e⟩ := hm.2.2.quotient_iso
    have hc : Nat.factorial m / 2 = 60 := by
      rw [←hq,Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    have hm5 : m = 5 := by
      have hlo : 5 ≤ m := by
        by_contra hn
        have hh := Nat.factorial_le (show m ≤ 4 by omega)
        norm_num at hh
        omega
      have hhi : m ≤ 5 := by
        by_contra hn
        have hh := Nat.factorial_le (show 6 ≤ m by omega)
        norm_num at hh
        omega
      omega
    subst m
    exact hm.module_card_odd ho

end CFSG.Quasithin.ChapterC
