module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSeparation
public import Theory.PPrimeCore
/-!
# The complete SL2(5) branch of the larger C.5.12 embedding sieve

The actual central-cover image eliminates each of the twenty-two A.3.12
rows except equality, the rank-two residual equality, and the signed
three-dimensional groups over the field of order five. Quasisimplicity
of the larger component excludes its odd-core noncentral rows. The
original source supplies quasisimplicity and the actual J4 obstruction.
Source: Aschbacher--Smith A.3.12 pp.47--48 and C.5.12 p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

theorem select_sl2_five_rows (B L : Subgroup G)
    [IsQuasisimple B] [IsQuasisimple L]
    (hB : IsSL B 2 5) (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hBL : B ≤ L) (hJ4 : ¬ Nonempty (L ≃* Janko4.Model))
    (hrows : A312Embedding B L)
    (hRankTwo : RankTwoTheoremC L → IsParabolicResidual B L true → B = L) :
    B = L ∨ ∃ unitary, IsPSLSign L unitary 3 5 ∨ IsSLSign L unitary 3 5 := by
  have hm' : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 (2^2) := by simpa using hm
  have hc := sl2_five_card hB
  have ho : pPrimeCore 2 L ≤ center L := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 L) with hz | ht
    · exact hz
    · have hd : 2 ∣ Nat.card L := by
        have hb : 2 ∣ Nat.card B := by rw [hc]; decide
        exact hb.trans (card_dvd_of_le hBL)
      have hco := pPrimeCore_coprime_card (p := 2) (G := L)
      rw [ht,card_top] at hco
      exact (Nat.Prime.not_dvd_one Nat.prime_two
        ((Nat.dvd_gcd (dvd_refl 2) hd).trans (by rw [hco.gcd_eq_one]))).elim
  have hcomm : ⁅pPrimeCore 2 L,(⊤ : Subgroup L)⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (by simpa only [coe_top,centralizer_univ] using ho)
  cases hrows with
  | one he => exact .inl he
  | two _ _ _ hl hr => exact .inl (hRankTwo hl hr)
  | three m hml hs _ _ => exact (binary_not_suzuki hm' m (by omega) hs).elim
  | four hs _ _ => exact (binary_not_linear_three_two (by decide : 0<2) hm' hs).elim
  | five hs _ _ => exact (binary_not_linear_four_two (by decide : 0<2) hm' hs).elim
  | six hs _ =>
      rcases hs with hs | hs
      · exact (sl2_five_not_alternating hB 5 (Or.inl rfl) hs).elim
      · exact (sl2_five_not_psl3 hB 2 (Or.inl rfl) hs).elim
  | seven hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
      · exact (sl2_five_not_alternating hB 6 (Or.inr rfl) hs).elim
      · exact (sl2_five_not_three_cover hB 6 hs).elim
  | eight hs =>
      rcases hs with ⟨p,_,_,_,hs,_⟩ | ⟨_,_,hs,_⟩
      · exact (sl2_five_not_psl2 hB p hs).elim
      · exact (sl2_five_not_alternating hB 5 (Or.inl rfl) hs).elim
  | nine hs =>
      rcases hs with ⟨p,u,_,_,hp,hs,hl⟩ | ⟨hs,_⟩ | ⟨hs,_⟩
      · have he := sl2_five_parameter hB hp hs
        subst p
        exact .inr ⟨u,hl⟩
      · exact (sl2_five_not_alternating hB 6 (Or.inr rfl) hs).elim
      · exact (sl2_five_not_three_cover hB 6 hs).elim
  | ten p hp _ _ hs _ => exact (sl2_five_no_elementary_extension hB hp.one_lt (by decide : 2≤2) _ hs).elim
  | eleven hs _ => exact (sl2_five_not_alternating hB 6 (Or.inr rfl) hs).elim
  | twelve hs =>
      rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩ <;>
        exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤4) _ hs).elim
  | thirteen _ hs =>
      rcases hs with hs | hs | hs | hs
      · exact (sl2_five_not_mathieu_twenty_two hB hs).elim
      · exact (sl2_five_not_psl3 hB 4 (Or.inr rfl) hs).elim
      · exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤4) _ hs).elim
      · exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤3) _ hs).elim
  | fourteen _ hs =>
      rcases hs with hs | hs | hs
      · exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤4) _ hs).elim
      · exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤6) _ hs).elim
      · exact (sl2_five_no_extraspecial_extension hB (by decide : 1≤3) _ hs).elim
  | fifteen hs _ => exact (sl2_five_not_alternating hB 5 (Or.inl rfl) hs).elim
  | sixteen hs _ => exact (sl2_five_no_extraspecial_extension hB (by decide : 1≤2) _ hs).elim
  | seventeen hl _ => exact (hJ4 hl).elim
  | eighteen _ hs =>
      rcases hs with hs | hs
      · exact (sl2_five_no_cyclic_extraspecial_extension hB 2 _ hs).elim
      · exact (sl2_five_no_homocyclic_four_extension hB _ hs).elim
  | nineteen _ hs =>
      rcases hs with hs | hs
      · exact (sl2_five_no_extraspecial_extension hB (by decide : 1≤3) _ hs).elim
      · exact (sl2_five_no_elementary_extension hB (by decide : 1<2) (by decide : 2≤6) _ hs).elim
  | twenty _ _ hk =>
      have hb := (pCore 2 B).card_le_card_group
      rw [hk,hc] at hb
      norm_num at hb
  | twenty_one _ _ _ hn _ _ => exact (hn hcomm).elim
  | twenty_two _ _ hn _ _ => exact (hn hcomm).elim
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
