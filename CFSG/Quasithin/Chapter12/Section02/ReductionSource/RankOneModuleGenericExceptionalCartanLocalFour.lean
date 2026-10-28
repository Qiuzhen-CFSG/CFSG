module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The local four-space and characteristic control on the original Chapter 12 input

The chosen-module adapter supplies the universal Input on wholeReduced.
The four-dimensional alternative retains the original residual action,
omega fixed subgroups and whole local two-core quotient. The characteristic
subgroup statement retains normality inside the two original Sylow joins.
No degree-two assumption or replacement module coordinates are introduced.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.637–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The original Chapter 12 input identifies the entire four-dimensional action. -/
theorem rankOne_local_cartan_a7_four_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K)
    (d : LocalCartanWitness T H A Y X C)
    (hc : Nat.card (localOmegaModule T K) = 16) :
    localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  obtain ⟨hf,hq⟩ := a.four_geometry hi d hc
  exact ⟨hf,hq,a.four_omega_fixed_eq hi d hc,a.four_omega_intersection_card_two hi d hc⟩

/-- The common characteristic alternative is excluded on the original two joins. -/
theorem rankOne_local_cartan_common_characteristic_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (E : Subgroup (ChapterB.baumann (T : Subgroup G))) [E.Characteristic]
    (hLE : ((E.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal)
    (hRE : ((E.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (residual H ⊔ (T : Subgroup G))).Normal) : E = ⊥ := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact hi.common_characteristic_baumann_eq_bot hH E hLE hRE

/-- The original omega-center has no common fixed involution for these components. -/
theorem rankOne_local_cartan_a7_omega_common_fixed_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (a : LocalA7Configuration T L H X K)
    (d : LocalCartanWitness T H A Y X C) :
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) ⊓
      centralizer (K : Set G) = ⊥ :=
  a.omega_common_fixed_eq_bot
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH d

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
