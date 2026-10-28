module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.SimpleSection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Triality.ParabolicObstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.EvenModels.Triality.FieldComponents
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.CoefficientAction

/-!
# The genuine triality branch of the field-component identification

For the fixed PSL₃(2) component in `SimpleInput`, inner involutions are
excluded by the proved normalizer cover and genuine parabolic Levi quotients.
For non-inner involutions, an actual coefficient expression and fixed-field
descent identify the fixed group with a smaller triality carrier. Simplicity
of that smaller group then contradicts the proved component-order obstruction.
The model equivalence transports the automorphism and its ordinary component
together, preserving the literal fixed subgroup.

The final theorem below is conditional: automorphism coverage, the smaller
fixed-group isomorphism and smaller-carrier simplicity remain prerequisites.
Ambient simplicity and perfectness are supplied from `SimpleInput`; they
are not assumed for the smaller group. All positive exponents, including one,
use the genuine pinned D₄ graph-field carrier and cubic coefficient action.

Sources: Aschbacher--Smith, proof of 15.3.38, printed p.1137, Theorem C and
Remark A.2.4, p.33, and 16.1.4(1,4), p.1171, `refs/quasithin.pdf`;
GLS3 §§2.5--2.6, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section

open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.OuterOdd
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

/-- Conditional source assembly. The inner branch and the component calculation
in a smaller simple fixed model are proved. The three remaining premises are
actual coefficient coverage, actual fixed-group descent, and simplicity of the
smaller carrier; none is claimed to follow from a model tag. -/
theorem SimpleInput.not_even_triality_of_descent {S : Type*} [Group S]
    (s : SimpleInput S) {n : ℕ} (hn : 0 < n)
    (hcoverage : ∀ [IsSimpleGroup (BinaryCarrier n hn)]
      [Group.IsPerfect (BinaryCarrier n hn)] (a : MulAut (BinaryCarrier n hn)),
      ∃ g : BinaryCarrier n hn, ∃ e : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj g * coefficientAction (binaryParameters n hn) e)
    (hdescent : ∀ [IsSimpleGroup (BinaryCarrier n hn)]
      [Group.IsPerfect (BinaryCarrier n hn)] (a : MulAut (BinaryCarrier n hn)),
      a ^ 2 = 1 → a ∉ MulAut.innerSubgroup (BinaryCarrier n hn) →
      ∀ (g : BinaryCarrier n hn) (e : CoefficientAut (binaryParameters n hn)),
      a = MulAut.conj g * coefficientAction (binaryParameters n hn) e →
      ∃ (m : ℕ) (hm : 0 < m), n = 2 * m ∧
        Nonempty (a.fixedSubgroup ≃* BinaryCarrier m hm))
    (hsmall : ∀ (m : ℕ) (hm : 0 < m), n = 2 * m → IsSimpleGroup (BinaryCarrier m hm)) :
    ¬ IsTrialityGroupAt (2 ^ n) S := by
  intro h
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff S n hn).mp h
  let : IsSimpleGroup S := s.simple
  let : Group.IsPerfect S := ⟨(inferInstance : (commutator S).Normal).eq_bot_or_eq_top.resolve_left
    (fun h => s.nonabelian ((commutator_eq_bot_iff S).mp h))⟩
  let : IsSimpleGroup (BinaryCarrier n hn) := e.symm.isSimpleGroup
  let : Group.IsPerfect (BinaryCarrier n hn) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let a := MulAut.congr e s.involution
  have ha : orderOf a = 2 := ((MulAut.congr e).orderOf_eq s.involution).trans s.involution_order
  let d : s.involution.fixedSubgroup ≃* a.fixedSubgroup :=
    MulAut.fixedSubgroupCongr e s.involution
  let C := s.component.map d.toMonoidHom
  have hC : IsComponent a.fixedSubgroup C := s.isComponent.map_equiv d
  have hCE : Nonempty (C ≃* Matrix.PSL3Two.PSL) :=
    ⟨(d.subgroupMap s.component).symm.trans s.equiv⟩
  by_cases hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn)
  · exact EvenModels.TrialityCase.not_fixed_component_of_inner n hn a ha hi C hCE
  · obtain ⟨g, c, hform⟩ := hcoverage a
    have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    obtain ⟨m, hm, hnm, ⟨q⟩⟩ := hdescent a ha2 hi g c hform
    let : IsSimpleGroup (BinaryCarrier m hm) := hsmall m hm hnm
    exact EvenModels.TrialityCase.not_fixed_component_of_descent a C hC m hm q hCE

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
