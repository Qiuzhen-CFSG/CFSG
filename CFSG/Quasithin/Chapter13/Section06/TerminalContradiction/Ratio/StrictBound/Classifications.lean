module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Alternatives
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.SmallDegree
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.FixedComparisons
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.ClassicalComparisons
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications.Order20160

/-!
# The terminal irreducible B.4 comparison

`Alternatives` applies the full universal B.4.2/B.4.5 implications and
eliminates all numerically impossible rows and both nontrivial triple
centers. Its source consumer transports the remaining group alternatives
through the actual equivalence with the image of H∞ in H/O₂(H).
`SmallDegree` makes the same reduction for intrinsic irreducible component
actions, using an explicit involution and the rank-nullity degree bound.

`ClassicalComparisons` excludes every variable-field competitor by orders
and divisibility. `FixedComparisons` handles the fixed orders, and
`Order20160` distinguishes PSL₃(4) from SL₄(2) by their Sylow two-centers.
Thus every faithful component-irreducible action with one of the three
exceptional components has quadratic ratio greater than two. Intrinsically,
an involution then rules out irreducible binary actions of degree at most
four, using its actual cyclic actor and rank-nullity.

The two universal B.4 implications and triviality of the component center
remain explicit inputs, as does the involution for the degree result.
The triple-cover branches use only their center identifications, so their
offender geometry is not used here. The source consumers use the literal
residual image in H/O₂(H); reducible-module assembly remains in `StrictBound`.

Source: Aschbacher–Smith, B.4.2/B.4.5 and terminal §13.6, printed
pp.86–87 and 935 (1 March 2004 manuscript).
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition.SmallRatioSource

namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
universe u v
open Section08

/-- On the actual terminal residual image, every fixed alternative is
eliminated except the order-20160 comparison. The remaining disjunction is
a proved consequence of the two full earlier classifications. -/
theorem source_classical_or_order20160
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) D V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S)
    (e : generalizedFitting D ≃* Source.starImage H (terminalResidual H))
    (hq : quadraticRatio σ ≤ 2) :
    ClassicalCompetitor (Source.starImage H (terminalResidual H)) ∨
      Nonempty (Components.L3Four ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  obtain ⟨hm, hc | hf⟩ :=
    source_competitors_of_small_ratio σ hB42 hB45 hyp hz H S hs e hq
  · exact .inl hc
  · exact .inr (order20160_collision_of_exceptional_fixed hm hf)

/-- The intrinsic degree argument is reduced to the same two group
comparisons. Quasisimplicity and SQTK are inherited inputs on L; the
involution need not yet have been constructed by the source model owner. -/
theorem small_degree_classical_or_order20160
    {L : Type u} [Group L] [Finite L] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) L V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hsq : IsSQTK 𝒦 L) (hf : Function.Injective σ)
    (hL : IsQuasisimple L) (hi : σ.IsIrreducible) (hz : center L = ⊥)
    (hm : ExceptionalModel L) (t : L) (ht : orderOf t = 2)
    (hdim : Module.finrank (ZMod 2) V ≤ 4) :
    ClassicalCompetitor L ∨
      Nonempty (Components.L3Four ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rcases competitors_of_small_degree σ hB42 hB45 hsq hf hL hi hz t ht hdim with hc | hfix
  · exact .inl hc
  · exact .inr (order20160_collision_of_exceptional_fixed hm hfix)

/-- The full B.4 implications force strict quadratic ratio for each actual
terminal component. All competing group models have been excluded by
proved comparisons; no filtered classification is an input. -/
theorem quadraticRatio_gt_two_of_exceptional
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) D V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    (hm : ExceptionalModel (generalizedFitting D)) :
    2 < quadraticRatio σ := by
  by_contra! hq
  rcases competitors_of_small_ratio σ hB42 hB45 hyp hz hq with hc | hf
  · exact not_classicalCompetitor_of_exceptional hm hc
  · exact not_fixedCompetitor_of_exceptional hm hf

/-- The constituent degree bound. The inherited SQTK and quasisimplicity
inputs apply B.4 intrinsically to L, and a genuine involution supplies the
rank-one quadratic actor excluding dimension at most four. -/
theorem finrank_gt_four_of_exceptional
    {L : Type u} [Group L] [Finite L] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) L V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hsq : IsSQTK 𝒦 L) (hf : Function.Injective σ)
    (hL : IsQuasisimple L) (hi : σ.IsIrreducible) (hz : center L = ⊥)
    (hm : ExceptionalModel L) (t : L) (ht : orderOf t = 2) :
    4 < Module.finrank (ZMod 2) V := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  by_contra! hdim
  rcases competitors_of_small_degree σ hB42 hB45 hsq hf hL hi hz t ht hdim with hc | hfix
  · exact not_classicalCompetitor_of_exceptional hm hc
  · exact not_fixedCompetitor_of_exceptional hm hfix

/-- Application to the actual component-irreducible terminal action. The
exceptional marking is obtained from 13.6.27 through `residual_model_of_source`
and the given equivalence with the literal residual image. -/
theorem source_quadraticRatio_gt_two
    {D : Type u} [Group D] [Finite D] {V : Type v}
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (σ : Representation (ZMod 2) D V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hyp : B4Hypotheses 𝒦 σ) (hz : center (generalizedFitting D) = ⊥)
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S)
    (e : generalizedFitting D ≃* Source.starImage H (terminalResidual H)) :
    2 < quadraticRatio σ := by
  apply quadraticRatio_gt_two_of_exceptional σ hB42 hB45 hyp hz
  rcases (residual_model_of_source H S hs).2 with hm | hm | hm
  all_goals obtain ⟨f⟩ := hm
  · exact .inl ⟨e.trans f⟩
  · exact .inr (.inl ⟨e.trans f⟩)
  · exact .inr (.inr ⟨e.trans f⟩)

/-- The degree input for constituent reduction on the literal source
component. Its marking and quasisimplicity follow from 13.6.27; the center,
involution, and inherited SQTK inputs remain with their structural owners. -/
theorem source_finrank_gt_four
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (S : Subgroup H)
    (hs : Components.Conclusion S)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (Source.starImage H (terminalResidual H)) V)
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦) (hB45 : FullB45.{u,v} 𝒦)
    (hsq : IsSQTK 𝒦 (Source.starImage H (terminalResidual H)))
    (hf : Function.Injective σ) (hi : σ.IsIrreducible)
    (hz : center (Source.starImage H (terminalResidual H)) = ⊥)
    (t : Source.starImage H (terminalResidual H)) (ht : orderOf t = 2) :
    4 < Module.finrank (ZMod 2) V :=
  finrank_gt_four_of_exceptional σ hB42 hB45 hsq hf
    (residual_quasisimple_of_source H S hs) hi hz (residual_model_of_source H S hs).2 t ht

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio.StrictBound.Classifications
