module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies


/-!
# Irreducible exclusion for the actual source action

The literal earlier hypotheses select an actual component of the minimal
normal subgroup. If this component is the whole subgroup, its trivial center
makes it simple and the proved Theorem C gives the complete model catalogue.
The single-family exclusions apply to the original action and marked involution.
A proper component belongs to the two-factor tensor branch, which is separately
excluded with the same source rank and displacement data.

Source: Aschbacher--Smith, 15.3.58, printed p.1149; the required specialization
of G.9.3, printed pp.354--357.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction ChapterG.Section09

variable {G : Type*} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {v : ActorQuotient Z} {s : ℕ}

/-- The selected minimal normal subgroup in the original source action cannot act irreducibly. -/
theorem EarlierActionInputs.not_irreducible
    {d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s}
    (a : EarlierActionInputs d) {K : Subgroup (ActorQuotient Z)}
    (hK : MinimalNormalConclusion KnownSimple.IsKnownSimple d.kernel K v s)
    (hi : Representation.IsIrreducible
      ((actorRepresentation Z ZS d.kernel).comp K.subtype)) : False := by
  have h := a.sieveData
  have hKD := hK.componentData hi
  have hsqtk := actor_sqtk Z d.sqtk
  obtain ⟨L, hc⟩ := IrreducibleSieve.source_componentHypothesis
    KnownSimple.IsKnownSimple Z ZS d.kernel h hKD d.sqtk
  have hLK : L ≤ K := by
    rcases hc.components with he | ⟨L₂, _, he, _⟩
    · exact he.symm.le
    · rw [he]
      exact le_sup_left
  by_cases he : L = K
  · subst L
    obtain ⟨hs, hn, hm⟩ := d.model_of_component hKD hc.component
    exact IrreducibleSieve.SourceFamilies.not_simple_component h hKD hc hsqtk hs hn hm
  · have r := normal_reduction_of_earlier_source d
    let : Representation.IsIrreducible (actorRepresentation Z ZS d.kernel) := r.irreducible
    have hcore : pCore 2 (ActorQuotient Z) = ⊥ := h.setup.twoCore_eq_bot
    exact IrreducibleSieve.SourceFamilies.TwoFactors.false_of_proper_component
      h hKD hc (lt_of_le_of_ne hLK he) hsqtk hcore

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
