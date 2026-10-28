module

public import Theory.SpecificGroups.PSL3Two.Parabolics.CosetGeometry
public import Theory.GroupAction.TypedCosetGeometry.Residues.Quotient

/-!
# Fano coordinates through an actual quotient map

A surjection sending two subgroups to the standard point and line
parabolics gives coordinates on their original cosets. Incidence is
preserved in both directions by lifting a common representative. The
Fano duality handles the opposite order of the two parabolics.

Source: Aschbacher–Smith I.5.4(2), printed p.420.
-/

@[expose] public noncomputable section
namespace Matrix.PSL3Two.Fano
open Subgroup
variable {H : Type*} [Group H]

structure QuotientMark (P L : Subgroup H) where
  points : (H ⧸ P) ≃ Point
  lines : (H ⧸ L) ≃ Line
  incident : ∀ q r, (∃ a : H, (a : H ⧸ P) = q ∧ (a : H ⧸ L) = r) ↔
    Incident (points q) (lines r)

namespace QuotientMark
variable {P L : Subgroup H}

def swap (m : QuotientMark P L) : QuotientMark L P where
  points := m.lines.trans duality.symm
  lines := m.points.trans duality
  incident q r := by
    have hs : (∃ a : H, (a : H ⧸ L) = q ∧ (a : H ⧸ P) = r) ↔
        (∃ a : H, (a : H ⧸ P) = r ∧ (a : H ⧸ L) = q) := by
      simp only [and_comm]
    rw [hs, m.incident]
    change Incident (m.points r) (m.lines q) ↔
      Incident (duality.symm (m.lines q)) (duality (m.points r))
    rw [← incident_duality]
    simp only [Equiv.apply_symm_apply]

theorem points_card (m : QuotientMark P L) : Nat.card (H ⧸ P) = 7 := by
  rw [Nat.card_congr m.points, Nat.card_eq_fintype_card, card_point]

theorem lines_card (m : QuotientMark P L) : Nat.card (H ⧸ L) = 7 := by
  rw [Nat.card_congr m.lines, Nat.card_eq_fintype_card, card_line]

end QuotientMark

def quotientMark_of_surjective (P L : Subgroup H) (f : H →* PSL)
    (hf : Function.Surjective f) (hkP : f.ker ≤ P) (hkL : f.ker ≤ L)
    (hP : P.map f = pointParabolic) (hL : L.map f = lineParabolic) :
    QuotientMark P L := by
  let ep := (CosetGeometry.QuotientTransport.cosetEquiv P f hf hkP).trans
    (quotientEquivOfEq hP)
  let el := (CosetGeometry.QuotientTransport.cosetEquiv L f hf hkL).trans
    (quotientEquivOfEq hL)
  have hep (a : H) : ep (a : H ⧸ P) = (f a : PSL ⧸ pointParabolic) := rfl
  have hel (a : H) : el (a : H ⧸ L) = (f a : PSL ⧸ lineParabolic) := rfl
  refine ⟨ep.trans pointCosetEquiv, el.trans lineCosetEquiv, ?_⟩
  intro q r
  change _ ↔ Incident (pointCosetEquiv (ep q)) (lineCosetEquiv (el r))
  rw [← coset_incident_iff]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    exact ⟨f a, (hep a).symm, (hel a).symm⟩
  · rintro ⟨g, hp, hl⟩
    obtain ⟨a, rfl⟩ := hf g
    exact ⟨a, ep.injective ((hep a).trans hp), el.injective ((hel a).trans hl)⟩

theorem exists_quotientMark (P L : Subgroup H) (f : H →* PSL)
    (hf : Function.Surjective f) (hkP : f.ker ≤ P) (hkL : f.ker ≤ L)
    (h : (P.map f = pointParabolic ∧ L.map f = lineParabolic) ∨
      (P.map f = lineParabolic ∧ L.map f = pointParabolic)) :
    Nonempty (QuotientMark P L) := by
  rcases h with h | h
  · exact ⟨quotientMark_of_surjective P L f hf hkP hkL h.1 h.2⟩
  · exact ⟨(quotientMark_of_surjective L P f hf hkL hkP h.2 h.1).swap⟩

/-- Each individual Fano coset action is faithful modulo the original quotient kernel. -/
theorem normalCore_eq_ker_of_standard_parabolic (P : Subgroup H) (f : H →* PSL)
    (hf : Function.Surjective f) (hk : f.ker ≤ P)
    (hP : P.map f = pointParabolic ∨ P.map f = lineParabolic) :
    P.normalCore = f.ker := by
  have ht : (P.map f).normalCore.comap f = P.normalCore := by
    simpa only [inf_idem] using
      CosetGeometry.QuotientTransport.normalCore_inf_comap P P f hf (le_inf hk hk)
  have hb : (P.map f).normalCore = ⊥ := by
    rcases hP with h | h <;> rw [h, Subgroup.normalCore_eq_ker]
    · exact MonoidHom.ker_eq_bot _ MulAction.toPerm_injective
    · exact MonoidHom.ker_eq_bot _ MulAction.toPerm_injective
  rw [← ht, hb, MonoidHom.comap_bot]

end Matrix.PSL3Two.Fano
