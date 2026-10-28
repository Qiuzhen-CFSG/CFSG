module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.GlobalTI
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Fusion of the distinguished point in 12.2.27

The original elementary V is normal in each point centralizer, and hence
lies in its two-core. Its natural coordinates and rank at least three give
a second nonzero vector. Transitivity supplies a conjugating element in L,
so the original point is not weakly closed in that actual two-core.

This discharges the fusion hypothesis in the terminal recognition, rather
than adding it to the source configuration.
Source: Aschbacher--Smith, 12.2.27 and I.4.6, printed pp.807,417;
Aschbacher, Sporadic Groups, Section 39, p.213.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}
namespace SplitLinearConfiguration
variable (C : SplitLinearConfiguration L V d) (D : ChosenModule T L V)
include C D

omit [Finite G] in
/-- The original seed is contained in the two-core of each point centralizer. -/
theorem seed_le_point_core (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    V ≤ (centralizer ({v} : Set G)).pCoreIn 2 := by
  let := D.elementary
  have hCL : centralizer ({v} : Set G) ≤ L := by
    rw [← C.self_normalizing]
    exact hnone v hv hv1
  have hVC : V ≤ centralizer ({v} : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
      (centralizer_le (Set.singleton_subset_iff.mpr hv))
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V) hVC
    (hCL.trans D.normalizes)

/-- The distinguished involution is not weakly closed in its centralizer's
actual two-core. The conjugator is constructed in the original L. -/
theorem point_fused_in_core (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ l ∈ L, l * v * l⁻¹ ∈ (centralizer ({v} : Set G)).pCoreIn 2 ∧
      l * v * l⁻¹ ≠ v := by
  classical
  obtain ⟨_,f,_⟩ := C.natural
  have hc : Nat.card V = 2 ^ d := by
    calc
      Nat.card V = Nat.card (Fin d → ZMod 2) := Nat.card_congr f.toEquiv
      _ = 2 ^ d := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  let := Fintype.ofFinite V
  have h3 : 3 ≤ ENat.card V := by
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_eq_nat_card, hc]
    rcases C.rank with rfl | rfl <;> norm_num
  obtain ⟨w, hw1, hwv⟩ := ENat.exists_ne_ne_of_three_le h3 (1 : V) ⟨v,hv⟩
  have hw1' : (w : G) ≠ 1 := fun he => hw1 (Subtype.ext he)
  obtain ⟨l,hl,he⟩ := natural_vector_transitive C.natural hv w.property hv1 hw1'
  refine ⟨l, hl, ?_, ?_⟩
  · rw [he]
    exact C.seed_le_point_core D hnone hv hv1 w.property
  · rw [he]
    exact fun he' => hwv (Subtype.ext he')

end SplitLinearConfiguration
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
