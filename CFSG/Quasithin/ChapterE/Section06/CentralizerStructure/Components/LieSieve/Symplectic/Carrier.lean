module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# The actual derived symplectic carriers in E.6.8(2)

In characteristic two the central quotient map identifies Sp₄ with PSp₄.
For fields of order greater than two, the proved root-generation theorem
identifies the derived subgroup with the full matrix group. At the binary
endpoint we restrict the central-quotient equivalence to commutators instead;
we do not identify Sp₄(2) with its derived subgroup. The six-letter polar
representation also supplies the actual A₆ identification in that endpoint.

These comparisons prove the model clause only. The Borel and parabolic action
clauses of E.6.8(2) remain separate mathematical obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] {L : Subgroup G}

/-- The nonbinary projective constructor gives precisely the derived matrix
model required by E.6.8(2). -/
theorem model_of_projective {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp L 2 (2 ^ n)) : SymplecticDerivedModel L n := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let _ := EvenProjective.charTwo_of_card hcard
  have hlarge : 2 < Nat.card F := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) hn)
  exact ⟨by omega, F, hF, hfin, hcard,
    ⟨(e.trans EvenProjective.equiv.symm).trans
      (derivedEquivFull_of_card_gt_two hlarge).symm⟩⟩

/-- Restrict the actual central-quotient equivalence to the two derived groups.
This does not replace the derived binary group by the full symplectic group. -/
noncomputable def binaryProjectiveDerivedEquiv :
    commutator (ClassicalGroup.PSp 2 (ZMod 2)) ≃* commutator (Sp (ZMod 2)) := by
  let e := (EvenProjective.equiv (F := ZMod 2)).symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  rfl

/-- The small Theorem C constructor retains the exact Sp₄(2)′ carrier. -/
theorem model_of_projective_derived
    (hm : Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    SymplecticDerivedModel L 1 := by
  obtain ⟨e⟩ := hm
  exact ⟨le_rfl, ZMod 2, inferInstance, inferInstance, by simp,
    ⟨e.trans binaryProjectiveDerivedEquiv⟩⟩

/-- Both symplectic constructors of the earlier classification have the
literal model in E.6.8(2), including parameter one. -/
theorem exists_model
    (hm : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2 ^ n)) ∨
      Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    ∃ n, SymplecticDerivedModel L n := by
  rcases hm with ⟨n, hn, hm⟩ | hm
  · exact ⟨n, model_of_projective hn hm⟩
  · exact ⟨1, model_of_projective_derived hm⟩

/-- The binary derived model has an actual alternating-six identification,
independently of which local subgroup alternative eventually occurs. -/
theorem alternating_six_of_model_one (hm : SymplecticDerivedModel L 1) :
    Chapter1.Section02.LocalModels.IsAlternating L 6 := by
  obtain ⟨_, F, _, _, hcard, ⟨e⟩⟩ := hm
  exact ⟨e.trans (Binary.derivedEquivAlternatingSix (by simpa using hcard))⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
