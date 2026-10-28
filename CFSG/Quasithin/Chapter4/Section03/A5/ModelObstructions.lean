module
public import CFSG.Quasithin.Chapter4.Section03.A5.SourceModule
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
/-!
# The actual A₅ module excludes an A₇ block with the same layer

The marked augmentation core gives the original V exactly sixteen elements.
An A₇ block has a module quotient of order sixty-four, so its full block
layer cannot equal V. This is the literal C.4.6 equality U(K)=U(L) needed
by the specialized source proof, including arbitrary central fixed layers.

Source: Aschbacher–Smith C.4.1(1), C.4.6 and 4.3.7, pp.151–152,615–616,
with the original A₅ block and module of 5.1.7.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- Cardinality comes from the original source action marking. -/
theorem module_card_sixteen : Nat.card V = 16 := by
  have he : Nat.card d.flag.module.map.range =
      Nat.card (Multiplicative BinaryPermutation.FiveCentralizerGeometry.Space) :=
    Nat.card_congr (MonoidHom.ofInjective d.flag.module.injective).symm.toEquiv
  rw [d.flag.module.range_eq] at he
  rw [he]
  change Nat.card (BinaryPermutation.core (Fin 5)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_core]
  rfl

/-- The actual equality of block layers excludes the A₇ row. -/
theorem not_sevenBlock_same_module (K : Subgroup G)
    (hU : (ChapterC.blockU K).map K.subtype = V) :
    ¬ ChapterC.IsAlternatingBlock K 7 := by
  intro hk
  have hc : Nat.card (ChapterC.BlockModule K) = 64 :=
    hk.module_card_odd (by decide)
  have hcard : Nat.card (ChapterC.blockU K) = 16 := by
    rw [← card_map_of_injective K.subtype_injective, hU]
    exact d.module_card_sixteen
  have hd : Nat.card (ChapterC.BlockModule K) ∣ Nat.card (ChapterC.blockU K) :=
    card_quotient_dvd_card (ChapterC.blockFixed K)
  rw [hc,hcard] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
