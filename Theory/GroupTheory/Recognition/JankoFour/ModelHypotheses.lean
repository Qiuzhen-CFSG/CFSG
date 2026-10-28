module

public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses.CoreQuotient
public import Theory.GroupTheory.Recognition.JankoFour.ModelHypotheses.Fusion

/-!
# The literal matrix model is of type J₄

The distinguished generator a has order two. Its centralizer has an
extraspecial generalized Fitting subgroup of order 2¹³, identified with the
certified intrinsic two-core. Its exact quotient retains the cubic kernel
above Aut(M₂₂). A certified kernel word gives a distinct conjugate of a
inside that core, with conjugacy in the original Janko4.Model.

This proves all clauses of Aschbacher–Segev's type-J₄ hypothesis on the
concrete carrier. It uses no assumed simplicity or recognition theorem.
Source: *The study of J₄ via the theory of uniqueness systems* (1992), p.12;
the intended recognition consumer is Aschbacher–Smith 8.2.14, printed p.723.
-/

public section

namespace Theory.GroupTheory.Recognition.JankoFour

/-- The concrete matrix carrier, with its literal first generator, satisfies type J₄. -/
theorem model_isTypeJ4 : IsTypeJ4 Janko4.a where
  involution := Janko4.orderOf_a
  extraspecial := by
    rw [ModelHypotheses.core_eq_twoCore]
    exact Janko4.InvolutionCentralizers.First.centralizer_twoCore_extraspecial
  core_card := by
    rw [ModelHypotheses.core_eq_twoCore]
    exact Janko4.InvolutionCentralizers.First.centralizer_twoCore_card
  cubic_quotient := ⟨ModelHypotheses.cubicQuotient⟩
  fusion := by
    obtain ⟨q, hconj, hne⟩ :=
      Janko4.InvolutionCentralizers.First.TypeFusion.exists_returning_twoCore
    intro he
    apply hne
    apply Set.mem_singleton_iff.mp
    rw [← he]
    refine ⟨hconj, ?_⟩
    apply Subgroup.mem_map.mpr
    refine ⟨(q : centralizer Janko4.a), ?_, rfl⟩
    rw [ModelHypotheses.core_eq_twoCore]
    exact q.property

end Theory.GroupTheory.Recognition.JankoFour
