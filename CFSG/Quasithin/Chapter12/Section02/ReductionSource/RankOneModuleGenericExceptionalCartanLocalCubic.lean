module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalCubic
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.HallPlane
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Cubic containing-row exclusions on the original Chapter 12 module

The original wholeReduced module supplies the universal source Input.
An escaping cubic forces a proper normal containing C-component whose
literal two-core quotient is neither an odd-prime PSL₂ nor PSL₂(25).
At field degree two the left Cartan itself supplies that cubic, using
only the original failure of normalization in the local overgroup.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.636–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal wholeReduced input excludes prime and twenty-five containing rows. -/
theorem rankOne_local_cartan_cubic_escape_container_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hCA : C ≤ A) (hCY : C ≤ Y) (hCc : Nat.card C = 3)
    (hC : ¬ C ≤ normalizer (residual H : Set G)) :
    residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X ∧
        (∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25 :=
  localCartan_cubic_escape_container_exclusions
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hpar c hY hCA hCY hCc hC

/-- At the original degree two, the escaping left Cartan is already cubic. -/
theorem rankOne_local_cartan_degree_two_escape_container_exclusions
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 4)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    A ≤ Y ∧ residual H ∈ Chapter1.L G (T : Subgroup G) ∧
      ∃ X : Subgroup G, X ≤ Y ∧ (X.subgroupOf Y).IsCComponent ∧
        (X.subgroupOf Y).Normal ∧ residual H < X ∧
        (∀ p : ℕ, p.Prime → Odd p → ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (X ⧸ pCore 2 X) 2 25 :=
  localCartan_degree_two_escape_container_exclusions
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany (by decide : 1 < 2) hpsl)
    hH hpar c hY hescape

/-- The original input identifies the actual order-nine plane in an A₇ configuration. -/
theorem rankOne_local_cartan_a7_hall_plane
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    {X K : Subgroup G} (a : LocalA7Configuration T L H X K)
    (d : LocalCartanWitness T H A Y X C) :
    let P := ((B ⊔ C).subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))
    IsElementaryAbelian 3 P ∧ Nat.card P = 9 :=
  a.hall_cubic_plane_quotient d
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hpar c

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
