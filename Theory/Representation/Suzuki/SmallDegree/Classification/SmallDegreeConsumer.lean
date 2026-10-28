module

public import Theory.Representation.Suzuki.SmallDegree.Classification
public import Theory.Representation.Suzuki.SmallDegree

/-!
# Applying Suzuki tensor exhaustion to the small binary degree window

Apply the counting assembly to the actual absolute Schur module. Faithfulness
excludes the empty tensor, and the published degree estimate forces a singleton
once the independent field-period divisibility is supplied. All representation
equivalences use the original Suzuki matrix group and the literal tensor model.

The final consumer discharges the simple/distinct/class-count premises using
the absolute classification. Only the independent field-period premise remains;
its producer is `SuzukiSmallDegree.field_period_dvd` in `SmallDegree.Descent`.
Source: Guralnick--Malle, *Classification of 2F-modules, II*, §3.1 and Lemma 8.3;
Aschbacher--Smith K.3.5--6, printed p.457.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural FrobeniusTensor

variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) [ρ.IsIrreducible]
  [Algebra (F m) (Closure ρ)]

/-- For the actual absolute Schur module, the counting inputs and the independent
period divisibility give a single natural Frobenius position under the source
degree bound. The source assembly must discharge those explicit premises. -/
theorem exists_singleton_tensorRep_equiv_of_simple_distinct_class_bound
    (hirr : ∀ I : Support m, IsIrreducible (tensorRep m (Closure ρ) I))
    (hdist : ∀ I J : Support m,
      Nonempty ((tensorRep m (Closure ρ) I).Equiv (tensorRep m (Closure ρ) J)) → I = J)
    (hbound : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      2 ^ (2 * m + 1))
    (hperiod : ∀ I : Support m,
      Nonempty ((absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) →
        2 * m + 1 ∣ I.card * Module.finrank (ZMod 2) (SchurField ρ))
    (hfaith : Function.Injective ρ)
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) :
    ∃ i : Fin (2 * m + 1),
      Nonempty ((absoluteRep ρ).Equiv (tensorRep m (Closure ρ) {i})) := by
  obtain ⟨I, hI, ⟨e⟩⟩ :=
    exists_nonempty_tensorRep_equiv_of_simple_distinct_class_bound hirr hdist hbound
      (absoluteRep ρ) inferInstance (absoluteRep_injective ρ hfaith)
  have hcard : I.card = 1 :=
    support_card_eq_one_of_smallDegree ρ I hI e (hperiod I ⟨e⟩) hsmall
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  exact ⟨i, ⟨e⟩⟩

/-- Absolute tensor classification supplies all representation and class-count
inputs for the faithful small-degree Schur module. The source assembly supplies
only the independently proved field-period divisibility. -/
theorem exists_singleton_tensorRep_equiv_of_field_period (hm : 1 ≤ m)
    (hperiod : ∀ I : Support m,
      Nonempty ((absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) →
        2 * m + 1 ∣ I.card * Module.finrank (ZMod 2) (SchurField ρ))
    (hfaith : Function.Injective ρ)
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) :
    ∃ i : Fin (2 * m + 1),
      Nonempty ((absoluteRep ρ).Equiv (tensorRep m (Closure ρ) {i})) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_nonempty_tensorRep_equiv hm
    (absoluteRep ρ) inferInstance (absoluteRep_injective ρ hfaith)
  have hcard : I.card = 1 :=
    support_card_eq_one_of_smallDegree ρ I hI e (hperiod I ⟨e⟩) hsmall
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  exact ⟨i, ⟨e⟩⟩

end Representation.SuzukiSmallDegree
