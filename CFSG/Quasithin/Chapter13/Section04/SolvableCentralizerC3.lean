module

public import CFSG.Quasithin.ChapterI.Section04To05.C3Recognition.FullImage
public import Theory.GroupTheory.GeneratedLocalChamberCore

/-!
# The literal C₃ recognition step in 13.4.9

The source generates E from M, the full centralizer of z, and H₀. Its
five-dimensional normal two-module V already gives |O₂(M)| ≥ 32, so the
I.5.15 core bound is discharged here using the original module. The actual
first vertex in E is M restricted to E; the core transport is proved through
that literal subgroup equivalence. This recognizes E as the concrete Sp₆(2).

Earlier 13.4.7–8 must still construct the C₃ family. Earlier I.5.8–14 must
provide its incidence conclusions. The final E=G argument of 13.4.9 uses
involution fusion and product-disconnection and is a separate remaining
source step. Neither E=G nor ambient recognition is asserted below.

Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
open Subgroup
open Quasithin.I5
open Quasithin.I5.C3Recognition
open Theory.SpecificGroups.SymplecticSix
variable {G : Type*} [Group G]

/-- The literal generated subgroup of 13.4.9. -/
def generated (M : Subgroup G) (z : G) (H₀ : Subgroup G) : Subgroup G :=
  M ⊔ centralizer ({z} : Set G) ⊔ H₀

theorem first_le_generated (M : Subgroup G) (z : G) (H₀ : Subgroup G) :
    M ≤ generated M z H₀ := le_sup_of_le_left le_sup_left

theorem original_five_module_core_bound [Finite G]
    (M V : Subgroup G) (hV : IsPGroup 2 V) (hVM : V ≤ M)
    (hMN : M ≤ normalizer (V : Set G)) (hcard : Nat.card V = 32) :
    32 ≤ Nat.card (pCore 2 M) := by
  have hvcore := le_pCoreIn_of_normalizes hV hVM hMN
  have hc := card_le_of_le hvcore
  rw [hcard, pCoreIn, card_map_of_injective M.subtype_injective] at hc
  exact hc

/-- Source13.4.9's generated subgroup is Sp₆(2), using its original V and cosets. -/
def generated_equiv_sp6 [Finite G]
    (M V H₀ : Subgroup G) (z : G)
    (hV : IsPGroup 2 V) (hVM : V ≤ M)
    (hMN : M ≤ normalizer (V : Set G)) (hcard : Nat.card V = 32)
    (S : DSystem .C3 (generated M z H₀))
    (hfirst : S.family 0 = M.subgroupOf (generated M z H₀))
    (d : GeometryData S) : generated M z H₀ ≃* Sp (ZMod 2) := by
  let e : S.family 0 ≃* M :=
    (MulEquiv.subgroupCongr hfirst).trans
      (subgroupOfEquivOfLe (first_le_generated M z H₀))
  have hc : Nat.card (pCore 2 (S.family 0)) = Nat.card (pCore 2 M) := by
    rw [← pCore_map_iso 2 e, card_map_of_injective e.injective]
  apply equivSp6_of_geometry S d
  rw [hc]
  exact original_five_module_core_bound M V hV hVM hMN hcard

/-- The source uniqueness of the maximal two-local overgroup verifies D4 in E. -/
theorem original_chamber_core_free
    (M H₀ T : Subgroup G) (z : G) (hT : IsPGroup 2 T)
    (houtside : ¬ centralizer ({z} : Set G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsPGroup 2 N → N ≠ ⊥ → N ≤ T →
      M ≤ normalizer (N : Set G) → normalizer (N : Set G) ≤ M) :
    (T.subgroupOf (generated M z H₀)).normalCore = ⊥ :=
  chamber_core_free_of_unique_twoLocal M _ H₀ T hT houtside hunique

end CFSG.Quasithin.Chapter13.Section04.SolvableCentralizerC3
