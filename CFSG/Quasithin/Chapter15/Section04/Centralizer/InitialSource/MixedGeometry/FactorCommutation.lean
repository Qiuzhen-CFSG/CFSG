module
public import Theory.GroupTheory.PPerfectCharacteristicPair
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.DoubleMoved

/-!
# Commuting actual factors after A4 recognition

For the same source pair, a factor of order twelve has two-core of order four.
Its actual module of order four is normal and therefore equals that
core. The sibling centralizes this module and acts trivially modulo the core;
its two-perfectness then forces it to centralize the whole factor.

Source: Aschbacher--Smith, proof of 15.4.18, p.1163, after identifying A4.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure TwoFactors TwoFactors.SourceFactors
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

/-- Commutation follows after the actual first factor has order twelve. -/
theorem Pair.source_commute_of_factor_card (p : Pair T M X) (h : Input κ T M X 2)
    (hcard : Nat.card (p.quotient.factor false) = 12) :
    p.quotient.factor false ≤ centralizer (p.quotient.factor true : Set G) := by
  let A := p.quotient.factor false
  let V := p.quotient.moduleFactor false
  have hcore : Nat.card (A.pCoreIn 2) = 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (pCore 2 A)
    rw [p.quotient.factor_quotient_card false,hcard] at hh
    change Nat.card ((pCore 2 A).map A.subtype) = 4
    rw [card_map_of_injective A.subtype_injective]
    omega
  have hVC : V = A.pCoreIn 2 := by
    apply eq_of_le_of_card_ge
    · exact le_pCoreIn_of_normalizes (p.module_elementary h false).isPGroup
        (p.module_le_factor h false)
        (normalizer_commutator_ge_right (localV (T : Subgroup G) M) A)
    · rw [hcore,p.module_card false]
  let S := ChapterB.baumann (T : Subgroup G)
  have ha := p.factor_actions_thompson h (source_thompsonGeometry h)
    (show S ≤ T from inf_le_left) (p.baumann false)
  dsimp only at ha
  have hcross : V ≤ centralizer (p.quotient.factor true : Set G) := ha.2.2.2.2.2.2.2.2.1 true
  apply le_centralizer_iff.mp
  exact le_centralizer_of_pPerfect_of_core A (p.quotient.factor true)
    (p.quotient.factor_perfect true)
    ((p.factor_le h true).trans (p.quotient.factor_normalized h false))
    (le_centralizer_iff.mp (hVC ▸ hcross)) (p.sibling_commutator h false)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
