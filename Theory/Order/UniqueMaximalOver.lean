module

public import Mathlib.Order.Atoms.Finite

/-!
# Generation by intervals with a unique maximal element

McBride's lemma is a finite-lattice argument: for `x < u`, the elements `v ≤ u`
for which `[x, v)` has a unique maximal element have supremum `u`.
Induct on `u`. Either its maximal elements above `x` are unique, or two distinct
such elements generate `u` and the induction hypothesis applies to both.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Definition B.6.2 and Lemma B.6.3, pp. 112–113.
-/

namespace Order

/-- The proper interval above `x` and below `u` has exactly one maximal element.
In a subgroup lattice this says that `u` has a unique maximal subgroup containing `x`. -/
@[expose] public def HasUniqueMaximalOver {α : Type*} [PartialOrder α] (x u : α) : Prop :=
  x < u ∧ ∃! m, x ≤ m ∧ m ⋖ u

/-- Order isomorphisms preserve the unique-maximal-over relation. -/
public theorem HasUniqueMaximalOver.map {α β : Type*} [PartialOrder α] [PartialOrder β]
    (e : α ≃o β) {x u : α} (h : HasUniqueMaximalOver x u) :
    HasUniqueMaximalOver (e x) (e u) := by
  obtain ⟨hlt, m, hm, hu⟩ := h
  refine ⟨e.lt_iff_lt.mpr hlt, e m,
    ⟨e.monotone hm.1, (apply_covBy_apply_iff e).mpr hm.2⟩, ?_⟩
  intro n hn
  have hn' : x ≤ e.symm n ∧ e.symm n ⋖ u := by
    constructor
    · exact e.le_iff_le.mp (by simpa using hn.1)
    · exact (apply_covBy_apply_iff e).mp (by simpa using hn.2)
  simpa using congrArg e (hu (e.symm n) hn')

variable {α : Type*} [CompleteLattice α] [Finite α]

/-- Every proper overgroup of `x` lies below its unique maximal overgroup in `u`. -/
public theorem HasUniqueMaximalOver.le_maximal {x u m v : α}
    (h : HasUniqueMaximalOver x u) (hm : x ≤ m ∧ m ⋖ u)
    (hxv : x ≤ v) (hvu : v < u) : v ≤ m := by
  obtain ⟨n, hvn, hn⟩ := exists_le_covBy_of_lt hvu
  have heq : n = m := h.2.unique ⟨hxv.trans hvn, hn⟩ hm
  exact heq ▸ hvn

/-- McBride's lemma in its finite-lattice form. -/
public theorem eq_sSup_hasUniqueMaximalOver {x u : α} (hxu : x < u) :
    u = sSup {v | v ≤ u ∧ HasUniqueMaximalOver x v} := by
  classical
  apply le_antisymm
  · induction u using WellFoundedLT.induction with
    | ind u ih =>
      obtain ⟨m, hxm, hm⟩ := exists_le_covBy_of_lt hxu
      by_cases hu : ∀ n, x ≤ n ∧ n ⋖ u → n = m
      · exact le_sSup ⟨le_rfl, hxu, m, ⟨hxm, hm⟩, hu⟩
      · push Not at hu
        obtain ⟨n, ⟨hxn, hn⟩, hnm⟩ := hu
        have hxltm : x < m := lt_of_le_of_ne hxm (by
          intro heq
          have := hm.eq_or_eq (heq ▸ hxn) hn.le
          exact hnm (this.resolve_right hn.ne))
        have hxltn : x < n := lt_of_le_of_ne hxn (by
          intro heq
          have := hn.eq_or_eq (heq ▸ hxm) hm.le
          exact hnm ((this.resolve_right hm.ne).symm))
        have hgen (v : α) (hv : v < u) (hxv : x < v) :
            v ≤ sSup {w | w ≤ u ∧ HasUniqueMaximalOver x w} :=
          (ih v hv hxv).trans (sSup_le_sSup (fun w hw => ⟨hw.1.trans hv.le, hw.2⟩))
        conv_lhs => rw [← hm.wcovBy.sup_eq hn.wcovBy hnm.symm]
        exact sup_le (hgen m hm.lt hxltm) (hgen n hn.lt hxltn)
  · exact sSup_le fun v hv => hv.1

end Order
