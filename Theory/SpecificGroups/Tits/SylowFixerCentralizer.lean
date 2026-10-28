module
public import Theory.SpecificGroups.Tits.SylowPointwiseInner
public import Theory.SpecificGroups.Tits.SharpOuterBound
public import Theory.SpecificGroups.Tits.RelativeParabolicNormalizers.FirstCentralizer
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.Orders
public import Theory.GroupAction.InnerCentralizerCardinality

/-!
# Three-free centralizers of Sylow-fixing Tits automorphisms

Align the supplied full Sylow subgroup with the certified Parrott--Atlas
Sylow. The nonidentity pointwise fixer is conjugation by its central
involution r5. Its inner centralizer has order 10240, and the full outer
automorphism group has order at most two. Thus the full automorphism
centralizer has order prime to three. Both the actual automorphism and
its Sylow marking are transported through the same group equivalence.

Source: Parrott (1972), §5, p.683; Aschbacher--Smith, proof of 12.6.26,
printed p.832, the rank-two Theorem C inspection.
-/

public section
open Subgroup
namespace Tits

/-- No cubic subgroup centralizes a nonidentity pointwise Sylow fixer. -/
theorem not_three_dvd_sylow_fixer_centralizer
    (P : Sylow 2 ParrottGroup) (a : MulAut ParrottGroup) (ha : a ≠ 1)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 3 ∣ Nat.card (centralizer ({a} : Set (MulAut ParrottGroup))) := by
  obtain ⟨e,_,he⟩ := SylowPointwiseInner.fixing_sylow_marking
    parrottFiniteImageEquiv P a hP ha
  have hc := Nat.card_congr
    (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.congr e) a).toEquiv
  rw [he] at hc
  rw [hc]
  have hd := MulAut.centralizer_conj_card_dvd
    RelativeSylowMarking.atlas_center_eq_bot atlas1600R5
  rw [←RelativeParabolicNormalizers.first_eq_centralizer,
    ExceptionalParabolics.first_card] at hd
  intro h3
  rcases Nat.prime_three.dvd_mul.mp (h3.trans hd) with h|h
  · norm_num at h
  · have hl := Nat.le_of_dvd (Nat.card_pos (α := MulAut.Outer Atlas1600Group)) h
    have hu := SharpOuterBound.atlas_outer_card_le_two
    omega
end Tits
