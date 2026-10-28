module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.GroupTheory.SmallSylowObstructions
public import Theory.SpecificGroups.ProjectiveLinear.EvenOrderFour
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Excluding the remaining binary linear source models

Every binary PSL3 model contains the actual projective unipotent element
of order four, incompatible with an elementary Sylow. In dimensions four
and five over the two-element field, the fraction-free order formula gives
a multiple of sixteen, incompatible with a Sylow subgroup of order at most
eight. All witnesses are transported through the original model maps.

Source: Aschbacher--Smith Theorem C and F.6.17, printed pp.33,309.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
variable {G : Type*} [Group G] [Finite G]

theorem not_linear_three_binary_of_elementary_sylow
    (P : Sylow 2 G) [IsElementaryAbelian 2 P] {f : ℕ} :
    ¬ ClassicalGroup.IsPSL G 3 (2 ^ f) := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  obtain ⟨x, hx⟩ := Matrix.ProjectiveSpecialLinearGroup.exists_order_four_of_char_two (F := F)
  apply elementary_sylow_no_order_four P (e.symm x)
  simpa only [MulEquiv.orderOf_eq] using hx

theorem not_binary_four_or_five_of_small_sylow
    (P : Sylow 2 G) (hP : Nat.card P ≤ 8) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL G n 2 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  apply not_sixteen_dvd_of_sylow_le_eight P hP
  rw [Nat.card_congr e.toEquiv]
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    norm_num
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF] at hc
    norm_num [Fin.prod_univ_succ] at hc
    rw [hc]
    norm_num

end CFSG.Quasithin.ChapterF.SourceAssembly.ComponentSieve
