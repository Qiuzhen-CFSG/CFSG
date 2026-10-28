module

public import CFSG.Quasithin.ChapterB.Section05.QuotientComponents.PreparationSource.FixedCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.NilpotentRadical
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.CenterBounds
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# Structural inputs to the B.5.5 chief-section choice

The original SQTK presentation exhibits every component as an actual
quasisimple section of its cover. The full A.2 implication gives SQTK for
that component. Applying A.3.6 to its top subgroup gives center order one
or three: the other common alternative would make the nontrivial perfect
component nilpotent. This route uses no multiplier assumption.

The Fitting identity is an elementary consequence of centrality of the
non-three prime cores. That centrality remains a separate source step;
it is not inferred here from the component calculations.

The retained universal inputs are the existing full `SemisimpleInput`
(producer `qt-a-02`) and `A36Input` (producer `qt-a03-sqtk-structure`).
Final discharge belongs to `qt-b05-quotient-components`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.5, printed pp.104–105; A.2 and A.3.6, pp.33 and 43–45.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.PreparationSource
open SourceInduction ComponentReduction ComponentReduction.PreliminaryActions
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

/-- The exact Fitting identity follows once the non-three prime cores are central. -/
theorem fitting_of_primeCore_central [Finite D]
    (hc : ∀ p : ℕ, p.Prime → p ≠ 3 → pCore p D ≤ center D) :
    generalizedFitting D = (componentLayer D ⊔ pCore 3 D) ⊔ center D := by
  have hnil : Group.IsNilpotent (center D) := by
    refine ⟨1, ?_⟩
    rw [Subgroup.upperCentralSeries_one_eq_top_iff]
    infer_instance
  have hZ : center D ≤ fittingSubgroup D := le_sSup ⟨inferInstance,hnil⟩
  apply le_antisymm
  · apply sup_le
    · rw [fitting_eq_sup_pCore]
      apply iSup_le
      intro p
      by_cases he : p.val.val = 3
      · rw [he]
        exact (le_sup_right : pCore 3 D ≤ componentLayer D ⊔ pCore 3 D).trans le_sup_left
      · exact (hc _ (Nat.mem_primeFactors.mp p.val.property).1 he).trans le_sup_right
    · exact le_sup_left.trans le_sup_left
  · exact sup_le (sup_le le_sup_right ((pCore_le_fitting D 3).trans le_sup_left))
      (hZ.trans le_sup_left)

/-- Apply the full A.2 theorem to L as a section of the supplied SQTK cover. -/
theorem component_sqtk [Finite D] {K : GroupClass.{u}}
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (hyp : FFHypothesis K ρ) {L : Subgroup D} (hL : IsComponent D L) : IsSQTK K L := by
  let := hL.2
  obtain ⟨c⟩ := hyp.quotient
  let f : c.Cover →* D := c.equiv.toMonoidHom.comp (QuotientGroup.mk' c.kernel)
  have hf : Function.Surjective f := c.equiv.surjective.comp (QuotientGroup.mk'_surjective c.kernel)
  apply HighThreeRank.CoverCentralizer.SourceConstruction.quasisimple_section_sqtk hA c.sqtk
  exact (ChapterA.Section02.IsSectionOf.subgroup L).ambient_surjective f hf

private theorem center_card_of_common {X : Type u} [Group X] [Finite X] [IsQuasisimple X]
    (h : Chapter1.Section02.A36Common X) :
    Nat.card (center X) = 1 ∨ Nat.card (center X) = 3 := by
  rcases h.2.2.1 with hf | hc
  · have ht : fittingSubgroup X = ⊤ := hf.1.trans generalizedFitting_eq_top_of_quasisimple
    have hnil : Group.IsNilpotent (⊤ : Subgroup X) := ht ▸ inferInstanceAs (Group.IsNilpotent (fittingSubgroup X))
    let := hnil
    let : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv (topEquiv : (⊤ : Subgroup X) ≃* X)
    let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
    let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
    exact (Group.IsPerfect.not_isNilpotent X inferInstance).elim
  · simpa only [hc.1] using hc.2.2

/-- A.3.6 gives the actual center alternatives. Its F=F* case is impossible
for the nontrivial perfect component; no multiplier theorem is used. -/
theorem component_center_order [Finite D] {K : GroupClass.{u}}
    (hA : HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (hyp : FFHypothesis K ρ) {L : Subgroup D} (hL : IsComponent D L) [L.Normal] :
    Nat.card (center L) = 1 ∨ Nat.card (center L) = 3 := by
  let := hL.2
  let : IsQuasisimple (⊤ : Subgroup L) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have ht : IsComponent L ⊤ := ⟨(inferInstance : (⊤ : Subgroup L).Normal).isSubnormal,inferInstance⟩
  have hc := center_card_of_common (h36 L (component_sqtk ρ hA hyp hL)
    (component_twoCore hyp.twoCore) ⊤ ht.isCComponent).2
  have he := Nat.card_congr (centerCongr (topEquiv : (⊤ : Subgroup L) ≃* L)).toEquiv
  rwa [he] at hc
end CFSG.Quasithin.ChapterB.PreparationSource
