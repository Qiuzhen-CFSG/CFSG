module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.Family
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ECaseReduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ModelMembers
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# The ambient derived symplectic lower obstruction

The family consists of the elementary abelian subgroups of L of order q³.
Its weak closure in T is T ∩ L and its normalizer is proper. The literal
quotient maps in E.1.2 reduce every potential low-rank E-member to the
two-core quotient of K ∩ L, so a rank gap in the concrete symplectic model
excludes every such member. This accounts for ambient outer automorphisms
without assuming that they preserve a parabolic type.

The intrinsic model rank gap is proved in `ElementaryCoreRankGap` and applied
to the actual family in `ModelMembers`. Thus `not_isEGenerated` establishes
the lower obstruction in E.1.14(1), and `not_isEGenerated_of_generalizedFitting`
applies it to the source's literal L = F*(G). This argument needs only a normal
simple derived-model subgroup; the source's SQTK and G = LT hypotheses are
not needed for this lower bound. The comparison with the full symplectic group
uses its proved derived inclusion isomorphism for f > 1. The earlier conditional
assembly interfaces remain available.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--6 and E.1.14(1), printed pp.209--211, 214, citing [Asc82a, Lemma 4.7].
-/

public section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {F : Type v} [Field F] [Finite F]

/-- The full ambient obstruction, conditional only on the stated intrinsic model bound. -/
theorem not_isEGenerated_of_coreRankGap (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Sp F))
    (hgap : ∀ (H : Type u) [Group H] [Finite H] (j : H →* Sp F),
      Function.Injective j → ∀ (A : Subgroup H), IsElementaryAbelian 2 A →
      Nat.card A = 2 ^ (3 * f) →
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f → A ≤ pCore 2 H) :
    ¬ IsEGenerated (f - 1) G := by
  apply not_isEGenerated_of_members_le T (family L f) (family_elementary L f)
    (normalizer ((T : Subgroup G) ⊓ L : Set G)) (normalizer_ne_top L T hf hF e)
  · rw [weakClosure_eq L T hf hF e]
    exact le_rfl
  · intro A hA _ K hK
    exact (not_member_of_coreRankGap L (e.trans (EvenTwoRank.derivedEquiv hF (by omega)))
      (by omega) hgap hA.1 hA.2.2 hK).elim

/-- Application to the source's literal generalized Fitting subgroup.
The additional model bound must still be supplied before asserting E.1.14(1). -/
theorem not_isEGenerated_of_generalizedFitting_coreRankGap
    [IsSimpleGroup (generalizedFitting G)] (T : Sylow 2 G)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Sp F))
    (hgap : ∀ (H : Type u) [Group H] [Finite H] (j : H →* Sp F),
      Function.Injective j → ∀ (A : Subgroup H), IsElementaryAbelian 2 A →
      Nat.card A = 2 ^ (3 * f) →
      Group.rank (A.map (QuotientGroup.mk' (pCore 2 H))) < f → A ≤ pCore 2 H) :
    ¬ IsEGenerated (f - 1) G :=
  not_isEGenerated_of_coreRankGap (generalizedFitting G) T hf hF e hgap

/-- The maximum-elementary family and its proper weak-closure normalizer
obstruct E-generation at f − 1 in every ambient extension of the normal
simple derived symplectic model. All local model premises are discharged. -/
theorem not_isEGenerated (L : Subgroup G) [L.Normal] [IsSimpleGroup L]
    (T : Sylow 2 G) {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ≃* commutator (Sp F)) :
    ¬ IsEGenerated (f - 1) G := by
  apply not_isEGenerated_of_members_le T (family L f) (family_elementary L f)
    (normalizer ((T : Subgroup G) ⊓ L : Set G)) (normalizer_ne_top L T hf hF e)
  · rw [weakClosure_eq L T hf hF e]
    exact le_rfl
  · intro A hA _ K hK
    exact (not_member L hf hF e hA hK).elim

/-- The derived Sp₄ lower obstruction in the literal E.1.14(1) setup.
The stronger normal-subgroup result already handles all ambient outer
automorphisms, without needing SQTK or the supplementary equality G = LT. -/
theorem not_isEGenerated_of_generalizedFitting
    [IsSimpleGroup (generalizedFitting G)] (T : Sylow 2 G)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : generalizedFitting G ≃* commutator (Matrix.symplecticGroup (Fin 2) F)) :
    ¬ IsEGenerated (f - 1) G :=
  not_isEGenerated (generalizedFitting G) T hf hF e

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.Sp4Lower
