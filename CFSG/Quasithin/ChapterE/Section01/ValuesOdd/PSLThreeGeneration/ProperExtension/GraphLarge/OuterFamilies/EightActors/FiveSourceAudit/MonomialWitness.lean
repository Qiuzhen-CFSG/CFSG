module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Preparation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.Solvability
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.SylowPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Escape

/-!
# Assembly of the concrete five-prime monomial witness

The matrix calculation in `Preparation` discharges weak-closure movement from
simultaneous Sylow placement of the two actual actors. The existing solvable
E-generation theorem then produces an escaping rank-one E-member for a member
of the original full conjugacy family. The literal actor orders are certified
in `Preparation`.

`Solvability` proves that the literal monomial plus graph subgroup is solvable.
`SylowPlacement` constructs a common ambient Sylow two-subgroup containing both
actors and contained in that overgroup. Combining these results gives the
unconditional concrete witness and its escaping E-member. This establishes the
specified PSL₃(5) diagnostic, not the general positioned-eight case of E.1.14(7).

Source: Aschbacher--Smith E.1.5, E.1.8, E.1.13 and E.1.14(7), pp.210--214;
`FiveSourceAudit/source/README.md` for the concrete matrices.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit

/-- Simultaneous placement supplies the requested monomial movement witness. -/
theorem monomial_motion_of_simultaneous_sylow
    (hplace : ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      (T : Subgroup Model) ≤ monomialOvergroup ∧ movedActor ≤ (T : Subgroup Model)) :
    ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      (T : Subgroup Model) ≤ monomialOvergroup ∧
      ¬ monomialOvergroup ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  obtain ⟨T, hAT, hTK, hBT⟩ := hplace
  exact ⟨T, hAT, hTK, monomial_motion_of_movedActor_le T hBT⟩

/-- Actual consumer application: the resulting subgroup has the intrinsic
E1 quotient-rank and escape clauses for an original-family conjugate. The
solvability and simultaneous-placement inputs remain explicit. -/
theorem monomial_escape_of_simultaneous_sylow
    (hsolv : Group.IsSolvable monomialOvergroup)
    (hplace : ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      (T : Subgroup Model) ≤ monomialOvergroup ∧ movedActor ≤ (T : Subgroup Model)) :
    ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      ∃ g : Model, actor.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Model) ∧
        ∃ K : Subgroup Model,
          IsEMemberAt 1 (T : Subgroup Model) (actor.map (MulAut.conj g).toMonoidHom) K ∧
          ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  let := hsolv
  obtain ⟨T, hAT, hTK, hmove⟩ := monomial_motion_of_simultaneous_sylow hplace
  obtain ⟨B, ⟨g, rfl⟩, hBT, K, hK, hKM⟩ :=
    exists_escape_of_solvable_overgroup T family family_elementary monomialOvergroup hTK hmove
  exact ⟨T, hAT, g, hBT, K, hK, hKM⟩

/-- The complete concrete monomial witness: the original eight-actor has inner
intersection of order four and lies in an ambient Sylow contained in the
solvable monomial overgroup, which moves the original family's weak closure. -/
theorem monomial_witness :
    Nat.card actor = 8 ∧ Nat.card (actor ⊓ inner : Subgroup Model) = 4 ∧
      Group.IsSolvable monomialOvergroup ∧
      ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
        (T : Subgroup Model) ≤ monomialOvergroup ∧
        ¬ monomialOvergroup ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) :=
  ⟨card_actor, card_actor_inf_inner, monomialOvergroup_solvable, exists_monomial_sylow_motion⟩

/-- The concrete witness supplies an escaping rank-one E-member for an actual
conjugate of the original actor. Both model premises of the conditional
consumer are discharged. -/
theorem monomial_escape :
    ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      ∃ g : Model, actor.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Model) ∧
        ∃ K : Subgroup Model,
          IsEMemberAt 1 (T : Subgroup Model) (actor.map (MulAut.conj g).toMonoidHom) K ∧
          ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) :=
  monomial_escape_of_simultaneous_sylow monomialOvergroup_solvable simultaneous_sylow_placement

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
