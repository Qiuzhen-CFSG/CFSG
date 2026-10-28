module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.M12Local.Inner
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.M12Local.Outer

/-!
# The M₁₂ local deductions in reverse Δ₀ membership

The comparison supplies actual central-quotient and residual-image equivalences.
The inner calculation proves the non-2-central mark before lifting, and identifies
the full relative centralizer when the center is trivial. Conjugation transports
that centerless component to L′, where the outer calculation controls the action
on the original embedded two-residual.

The exact earlier 16.1.5(4) and I.2.2(5b) clauses are explicit inputs. The intrinsic
automorphism-centralizer decomposition is still a separate model prerequisite;
`localData_of_decomposition` is conditional on it. The assembly of the source
lemma remains with ReverseDelta and must discharge every input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of 16.4.11(2), printed p.1193; 16.1.5(4), p.1171;
I.2.2(5b), pp.409–410.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
open Subgroup Theory.GroupTheory
open DoubleCoverCentralizer
open CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- All three ambient outputs, conditional on the still-missing intrinsic
centralizer generation and the precise earlier source clauses. -/
theorem localData_of_decomposition (d : Contrary T z L g R r)
    (hc : M12Comparison L (L.conjBy g) r z)
    (htable : ∀ a : MulAut Sporadic.Mathieu.M12, orderOf a = 2 →
      M12InvolutionAlternative a)
    (hlift : center L ≠ ⊥ → NonTwoCentralInvolutionLifting L)
    (hdecomp : OuterCentralizerDecomposition) : M12LocalData L (L.conjBy g) r z := by
  refine ⟨cover_lift d hc htable hlift, inner_centralizer d hc htable, ?_⟩
  intro hZ
  obtain ⟨e⟩ := hc.component
  let q : L ≃* (L ⧸ center L) :=
    MulEquiv.ofBijective (QuotientGroup.mk' (center L))
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hZ]),
        QuotientGroup.mk'_surjective _⟩
  let eM : (L.conjBy g) ≃* Sporadic.Mathieu.M12 :=
    ((MulAut.conj g).subgroupMap L).symm.trans (q.trans e)
  exact ambient_outer_restriction hdecomp htable (L.conjBy g) z d.z_normalizes eM
    d.outer_action_order d.outer_action

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.M12Local
