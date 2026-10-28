module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ReadyCoverCases
public import Theory.Alternating.OddCentralCovers
/-!
# Alternating ordinary components in A.3.6

The odd-center covering calculation leaves only a simple alternating group
or a central triple cover of A₆ or A₇. Each branch supplies the complete
A.3.6 conclusion, including its common Fitting and radical clauses.

Source: Aschbacher–Smith, A.3.6, printed pp.43–45, and I.1.3, p.407.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory GLS3.Chapter5.OddCentralCovers
namespace CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
open Chapter1.Section02 Chapter1.Section02.LocalModels

/-- The complete alternating branch of A.3.6, including the exceptional
triple covers in degrees six and seven. -/
theorem a36_alternating {X : Type*} [Group X] [Finite X]
    (hcore : pCore 2 X = ⊥) (L : Subgroup X) (hL : IsComponent X L)
    (n : ℕ) (hn : 5 ≤ n ∧ n ≤ 8)
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) : A36Conclusion L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
  have heven : 2 ∣ Nat.card L := by
    have hA : 2 ∣ Nat.card (alternatingGroup (Fin n)) := by
      rcases hn with ⟨hlo, hhi⟩
      interval_cases n <;> rw [nat_card_alternatingGroup, Nat.card_fin] <;> norm_num [Nat.factorial]
    have hq : 2 ∣ Nat.card (L ⧸ center L) :=
      (Nat.card_congr e.toEquiv).symm ▸ hA
    exact hq.trans (card_quotient_dvd_card _)
  rcases odd_center_alternatives n hn.1 e (component_center_odd hcore L hL)
    with hc | ⟨hex, hc⟩
  · let j := alternatingEquivOfCenterCardOne n e hc
    exact ⟨.simple hL j.isSimpleGroup (.alternating n hn ⟨j⟩),
      ReadyCoverCases.common_of_quasisimple heven (Or.inl hc)⟩
  · have hz : Nonempty (center L ≃* Multiplicative (ZMod 3)) :=
      ⟨mulEquivOfPrimeCardEq hc (by simp)⟩
    refine ⟨.cover hL hz ?_, ReadyCoverCases.common_of_quasisimple heven (Or.inr hc)⟩
    rcases hex with rfl | rfl
    · exact .alternating_six ⟨inferInstance, hz, ⟨e⟩⟩
    · exact .alternating_seven ⟨inferInstance, hz, ⟨e⟩⟩
end CFSG.Quasithin.ChapterA.SQTKStructure.OrdinarySource
