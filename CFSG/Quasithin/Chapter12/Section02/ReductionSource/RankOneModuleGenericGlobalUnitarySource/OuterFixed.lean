module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.SelectedCenter
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module consumers of the full outer fixed centralizer

The whole reduced module supplies the original prepared hypotheses. Each
outer involution fixes exactly q³ elements of the Hermitian core, and the
center–derived subgroup of its full T-centralizer is elementary in that
core. In the degree-two row the selected maximizing actor has a nontrivial
such subgroup, preserved by the same escaping ambient two-normalizer.
The original residual long-root intersection is still to be established.

Source: Aschbacher–Smith F.4.37, 5.3.3 and the Chapter12 application,
printed pp.293,659,795. Both orientations, q=4 and the full catalogue remain.
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

/-- The original outer involution fixes a hyperplane of order q³ in O₂(L). -/
theorem rankOne_unitaryFour_outer_core_fixed_card_eq
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    Nat.card (L.pCoreIn 2 ⊓ centralizer ({u.val} : Set G) : Subgroup G) = (2^m)^3 :=
  d.unitaryFour_outer_core_fixed_card_eq
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc u hu ho

/-- The center–derived subgroup of the full fixed Sylow is elementary inside O₂(L). -/
theorem rankOne_unitaryFour_outer_derived_center_le_core
    (u : T) (hu : orderOf u=2) (ho : u.val ∉ L) :
    let P := (T : Subgroup G) ⊓ centralizer ({u.val} : Set G)
    let Z := (center P ⊓ _root_.commutator P).map P.subtype
    Z ≤ L.pCoreIn 2 ∧ IsElementaryAbelian 2 Z :=
  d.unitaryFour_outer_derived_center_le_core
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc u hu ho

omit hc in
/-- The same maximizing involution and escaping normalizer preserve a nontrivial elementary subgroup of the original core. -/
theorem rankOne_unitaryFour_degreeTwo_selected_center
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)) :
    ∃ f : T, orderOf f=2 ∧ f.val ∉ L ∧ f.val ∉ residual H ∧
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
          V ≤ normalizer (Z : Set G) :=
  d.unitaryFour_degreeTwo_selected_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
