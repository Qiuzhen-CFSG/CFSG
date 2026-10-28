module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.GroupAction.PerfectCentralQuotient
import Mathlib.Tactic

/-!
# The actual S₆ fixed group in the Sp₄(4) overcomponent row

The trivial symplectic multiplier lifts the given central quotient model to
the whole component, preserving the quotient map and the specified actor.
The field-fixed matrices descend to their two-element fixed coefficient
field. The binary symplectic equivalence then identifies the whole fixed
group with S₆, retaining the original fixed subgroup before any quotient.

Source: Aschbacher–Smith 2.5.19(3)(c) and the componenthood argument in
2.5.21, printed pp.561 and 566; the field calculation is 16.1.4(4).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms FieldFixedResidual

/-- The marked field involution on an actual Sp₄(4) central quotient has
S₆ as the fixed group of the original component itself. -/
theorem symplectic_four_quotient_fixed_equiv_symmetric_six
    {E F : Type*} [Group E] [Group.IsPerfect E]
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (a : MulAut E) (e : (E ⧸ center E) ≃* Sp F)
    (hmark : MulAut.congr e (quotientAut (center E) a) = representative 1) :
    Nonempty (a.fixedSubgroup ≃* Equiv.Perm (Fin 6)) := by
  obtain ⟨f, hf⟩ := CentralCovers.Even.exists_whole_model (n := 2) (by simpa using hF)
    (by decide) e
  have hcompat (x : E) : f (a x) = (representative 1) (f x) := by
    rw [hf, hf]
    have hh := congrArg (fun b : MulAut (Sp F) => b (e (QuotientGroup.mk' (center E) x))) hmark
    change e (quotientAut (center E) a (e.symm (e (QuotientGroup.mk' (center E) x)))) = _ at hh
    rw [e.symm_apply_apply, quotientAut_apply_mk] at hh
    exact hh
  have ha : MulAut.congr f a = representative 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    change f (a (f.symm (f x))) = _
    rw [f.symm_apply_apply]
    exact hcompat x
  let q := MulAut.fixedSubgroupCongr f a
  rw [ha] at q
  have hk : Nat.card (halfField (F := F) 1) = 2 :=
    card_halfField (by decide) (by simpa using hF)
  let d : (representative (F := F) 1).fixedSubgroup ≃* Equiv.Perm (Fin 6) :=
    (fixedEquiv ((frobeniusEquiv F 2) ^ 1)).trans
      ((Binary.fieldEquivSp (Binary.fieldEquivZModTwo _ hk)).trans
        Binary.symmetricSixEquiv.symm)
  exact ⟨q.trans d⟩

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6
