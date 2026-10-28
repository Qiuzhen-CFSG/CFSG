module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalCoordinates
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# A permitted Cartan containing the actual odd subgroup

The source normalizer has two-core kernel and abelian torus quotient, hence
is solvable. Hall containment extends any odd subgroup in this normalizer
to an actual source Cartan. Applied to D₀ this constructs a new Cartan;
normalization of the original inner Sylow is a remaining Hall-geometry input.

Source: Aschbacher--Smith, 11.3.7(5), printed p.773.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {F : BinaryField}

theorem exists_cartan_containing_odd (c : Coordinates D F)
    (A : Subgroup G) (ho : Odd (Nat.card A))
    (hA : A ≤ cartanNormalizer T L) :
    ∃ X : Subgroup G, IsCartan T L X ∧ A ≤ X := by
  let N := cartanNormalizer T L
  have hquot : Group.IsSolvable (N ⧸ pCore 2 N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := c.cartanNormalizerQuotientEquiv.toMonoidHom)
      c.cartanNormalizerQuotientEquiv.injective
  let : Group.IsNilpotent (pCore 2 N) := pCore_isPGroup.isNilpotent
  have hsolv : Group.IsSolvable N :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 N)).mpr ⟨inferInstance, hquot⟩
  obtain ⟨X, hAX, hXN, hX⟩ := OddHall.exists_hall_containing_odd N A hsolv hA ho
  exact ⟨X, ⟨hXN,hX⟩, hAX⟩

theorem source_cartan_choice (c : Coordinates D F) (A H : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G))))
    (hL : oddCartanPart A ≤ L)
    (hn : oddCartanPart A ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)) :
    ∃ X : Subgroup G, IsCartan T L X ∧ oddCartanPart A ≤ X := by
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  apply exists_cartan_containing_odd c _
    (ho.of_dvd_nat (card_dvd_of_le (oddCartanPart_le A)))
  rw [cartanNormalizer_eq_intersection_normalizer]
  exact le_inf hL hn
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
