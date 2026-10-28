module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.LongCentralization
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalUnitaryFullNormalizer.Four

/-!
# Original chosen-module consumers of the full long-root centralizer reduction

Every involution of the original Sylow fixes the original right-residual
center pointwise. For the SAME selected degree-two outer involution, the
full centralizer fixes that whole long-root group; its derived group is
disjoint from it, and its quotient by its inner part has order two. The
inner fixed group has at least q⁴ elements and at least q images in the
literal L/O₂(L) quotient. Both endpoint Sylow conditions and the SAME
escaping two-group are retained.

These are source-input reductions for F.4.37, not unconditional unitary
recognition: a nontrivial long-root commutator in this same full centralizer
is still required for the contradiction. The original whole-module and
KnownSimple hypotheses, both orientations and q=4 are retained.
Source: Aschbacher–Smith F.4.29(7),37 and 12.2, pp.289,293,795.
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

theorem rankOne_unitaryFour_involution_centralizes_right_center
    (u : T) (hu : orderOf u=2) :
    u.val ∈ centralizer (((center (residual H)).map (residual H).subtype) : Set G) :=
  d.unitaryFour_involution_centralizes_right_center
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc u hu

theorem rankOne_unitaryFour_long_fixer_index_le_two
    (P : Subgroup G) (hPT : P ≤ (T : Subgroup G))
    (hPR : P ≤ centralizer (((center (residual H)).map (residual H).subtype) : Set G)) :
    L.relIndex P ≤ 2 :=
  d.unitaryFour_long_fixer_index_le_two
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm hc P hPT hPR

omit hc in
theorem rankOne_unitaryFour_degreeTwo_selected_long_centralization
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
        (∀ B : Subgroup G, B ≤ (center (residual H)).map (residual H).subtype →
          V ≤ normalizer (B : Set G) → B=⊥) ∧
        let P := (T : Subgroup G) ⊓ centralizer ({f.val} : Set G)
        let R := (center (residual H)).map (residual H).subtype
        let Z := (center P ⊓ _root_.commutator P).map P.subtype
        Z ≠ ⊥ ∧ IsElementaryAbelian 2 Z ∧ Z ≤ L.pCoreIn 2 ∧
          V ≤ normalizer (Z : Set G) ∧
          (_root_.commutator P).map P.subtype ⊓ R=⊥ ∧ P ≤ centralizer (R : Set G) ∧
          L.relIndex P=2 ∧
          (2^m)^4 ≤ Nat.card ((((T : Subgroup G) ⊓ L) ⊓
            centralizer ({f.val} : Set G)) : Subgroup G) ∧
          2^m ≤ (L.pCoreIn 2).relIndex
            (((T : Subgroup G) ⊓ L) ⊓ centralizer ({f.val} : Set G)) :=
  d.unitaryFour_degreeTwo_selected_long_centralization
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH hp m hm he

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
