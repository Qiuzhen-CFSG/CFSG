module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.SingularCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module consumers of long-root invariance

The original whole reduced module supplies the prepared hypotheses for
the exact inner fixed-line identity. For the maximizing degree-two outer
involution, the long-root intersection of the FULL C_T(f) center–derived
subgroup is invariant under its ambient normalizer. The same escaping
two-group forces this intersection to be trivial. Its source-geometric
nontriviality is the remaining contradiction, not a new assumed premise.

Source: Aschbacher–Smith F.4.35,37 and the Chapter12 application, printed
pp.292–293,795. Both orientations, q=4 and the original catalogue remain.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G}
variable (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {A C : Subgroup G} (d : Global.Preparation T L H A C (residual H))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
include D h hmany hn hpsl hH d hp hm hc

theorem rankOne_unitaryFour_inner_fixed_core_eq_right_center :
    L.pCoreIn 2 ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) =
      (center (residual H)).map (residual H).subtype :=
  d.unitaryFour_inner_fixed_core_eq_right_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc

theorem rankOne_unitaryFour_long_intersection_normalizer
    (Z : Subgroup G) (hZQ : Z ≤ L.pCoreIn 2)
    (u : G) (hu : u ∈ (T : Subgroup G) ⊓ L) (huQ : u ∉ L.pCoreIn 2)
    (huZ : u ∈ centralizer (Z : Set G)) :
    normalizer (Z : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) :=
  d.unitaryFour_long_intersection_normalizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc Z hZQ u hu huQ huZ

omit hc in
theorem rankOne_unitaryFour_degreeTwo_maximal_long_intersection_normalizer
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse))
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L)
    (hmax : ∀ g : T, orderOf g=2 → g.val ∉ L →
      Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({u} : Set T))) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    normalizer (P : Set G) ≤
      normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) :=
  d.unitaryFour_degreeTwo_maximal_long_intersection_normalizer
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he u hu ho hmax

omit hc in
theorem rankOne_unitaryFour_degreeTwo_selected_singular_center
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T,
      (∀ g : T, orderOf g=2 → g.val ∉ L →
        Nat.card (centralizer ({g} : Set T)) ≤ Nat.card (centralizer ({f} : Set T))) ∧
      orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
      (∀ i : Fin 2, Chapter1.IsSylowIn 2
        ((T : Subgroup G) ⊓ centralizer ({f.val} : Set G))
        (normalizer (![L,residual H] i : Set G) ⊓ centralizer ({f.val} : Set G))) ∧
      ∃ V : Subgroup G, IsPGroup 2 V ∧
        (T : Subgroup G) ⊓ centralizer ({f.val} : Set G) < V ∧
        V ≤ centralizer ({f.val} : Set G) ∧
        V ≤ normalizer (((T : Subgroup G) ⊓ centralizer ({f.val} : Set G) : Subgroup G) : Set G) ∧
        (∀ i : Fin 2, ¬ V ≤ normalizer (![L,residual H] i : Set G)) ∧
        Nat.card (L.pCoreIn 2 ⊓ centralizer ({f.val} : Set G) : Subgroup G) = (2^m)^3 ∧
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Z ≤ L.pCoreIn 2 ∧
          V ≤ normalizer (Z : Set G) ∧
          normalizer (P : Set G) ≤
            normalizer ((Z ⊓ (center (residual H)).map (residual H).subtype : Subgroup G) : Set G) ∧
          Z ⊓ (center (residual H)).map (residual H).subtype = ⊥ :=
  d.unitaryFour_degreeTwo_selected_singular_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
