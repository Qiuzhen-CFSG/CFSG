module

public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.Roots
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.ProperParabolics
public import Theory.GroupAction.InnerInvolutionGeometry

/-!
# Ree root-involution geometry: representatives and elementary reductions

The two actual root curves, their nonidentity involutions, and properness
of the two root-defined parabolics are established in the imported modules.
An inner involutory automorphism fixing a Sylow subgroup pointwise is
represented by a 2-central involution of the original carrier. The general
residual transport module retains both embeddings in the local-centralizer
comparison.

Exhaustion of involutions by the two root classes, containment of their full
centralizers in the corresponding parabolics, and the long-root description
of the positive-subgroup center remain separate geometric obligations.
Consequently this module does not yet assert the full Ree cases of source
16.1.4(1) or 16.1.6. Automorphism innerness is supplied by the independent
inner–field decomposition; the Tits endpoint is separate.

Source: Aschbacher–Smith, 16.1.4(1), 16.1.6 and 16.5.13–14, printed
pp.1171–1172,1201–1203, `refs/quasithin.pdf`.
-/

public section
namespace ReeF4.EvenInvolutionGeometry

/-- Inner Sylow fixers have actual 2-central representatives. Identifying
this class with the long-root class requires the positive-center calculation. -/
theorem inner_involution_twoCentral (m : ℕ)
    [IsSimpleGroup (Model m)] [Group.IsPerfect (Model m)]
    (S : Sylow 2 (Model m)) (a : MulAut (Model m)) (ha : orderOf a = 2)
    (hi : ∃ x : Model m, a = MulAut.conj x) (hfix : ∀ y ∈ S, a y = y) :
    ∃ x : Model m, a = MulAut.conj x ∧ IsTwoCentralInvolution x := by
  obtain ⟨x, hx, he, hS, hcomm⟩ := MulAut.inner_involution_fixing_sylow
    Subgroup.center_eq_bot_of_simple_perfect S a ha hi hfix
  exact ⟨x, he, hx, S, hS, hcomm⟩

end ReeF4.EvenInvolutionGeometry
