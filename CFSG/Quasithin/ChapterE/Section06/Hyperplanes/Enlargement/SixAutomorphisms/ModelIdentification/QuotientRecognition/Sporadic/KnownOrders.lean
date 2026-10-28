module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.Sporadic.Reduction
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.SpecificGroups.Janko1.Model.Certification.Order

/-!
# The M₁₁, M₂₃ and J₁ exclusions

All involutory automorphisms of the concrete M₁₁ and M₂₃ carriers are
inner. Their fixed subgroups have orders 48 and 2688, respectively, neither
divisible by 360. The order 175560 of J₁ is itself not divisible by 360.
Thus none of these three cases even contains an A₆ fixed subgroup.

Source: Aschbacher–Smith, Theorem C, printed p.33, and the inspection in
E.6.23, p.254. The concrete order, innerness and fusion calculations are
imported directly from Theory, independently of later chapter assemblies.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
open _root_.Sporadic.Mathieu

/-- The actual M₁₁ fixed subgroup has order 48. -/
theorem m11 : FixedSixExclusion M11 := by
  apply FixedSixExclusion.of_fixed_card
  intro a ha
  rw [Nat.card_congr (m11InvolutoryAutFixedEquiv a ha).toEquiv,
    ← Nat.card_congr m11InvolutionCentralizer_mulEquiv_gl2.toEquiv,
    m11_involutionCentralizer_card]
  norm_num

/-- The actual M₂₃ fixed subgroup has order 2688. -/
theorem m23 : FixedSixExclusion M23 := by
  apply FixedSixExclusion.of_fixed_card
  intro a ha
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.fixedSubgroup_equiv_representative_of_inner
    a ha (m23_involution_automorphism_inner a ha)
  rw [Nat.card_congr e.toEquiv]
  change ¬ 360 ∣ Nat.card (centralizer ({M23Geometry.involutionRepresentative} : Set M23))
  rw [M23Geometry.involutionRepresentative_centralizer_card]
  norm_num

/-- J₁ has no subgroup isomorphic to A₆, by its actual matrix-group order. -/
theorem janko_one : FixedSixExclusion Janko1.Model := by
  apply FixedSixExclusion.of_card
  rw [Janko1.card_model]
  norm_num

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.Sporadic
