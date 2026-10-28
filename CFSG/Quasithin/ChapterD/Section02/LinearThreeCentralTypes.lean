module
public import Theory.Representation.IrreducibleSectionSemisimple
public import Theory.Representation.CliffordSubquotient
public import Theory.Representation.QuadraticFourGroup.CubicSections.SectionReduction.Occurrence
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeConstituents
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree

/-!
# Natural central quotients of the original component supports

Assume that every noncentral component type in every irreducible ambient
subquotient is natural. For a prescribed Irr⁺ support, place its literal
irreducible central quotient in an ambient irreducible subquotient. Clifford
restriction and semisimplicity realize that same quotient as a noncentral
component submodule. The supplied section recognition then marks the original
central quotient, with both group and linear equivalences. Field transport
puts the marking over the binary prime field.

The Chapter14 LinearThreeCovers consumer proves the section premise from
its source hypotheses. No semisimplicity or splitting of the original
support is assumed. Source: Aschbacher--Smith F.9.18(3,5), pp.325--326,
and the central-cover step of 14.6.22, printed p.1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
universe u
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

set_option backward.isDefEq.respectTransparency false in
/-- Recognition on ambient irreducible subquotients identifies the literal
central quotient of every original Irr⁺ support, retaining its fixed kernel. -/
theorem central_constituent_linear_three_of_sections
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [Group.IsPerfect K]
    (hK : K.IsSubnormal)
    (hsections : ∀ (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation),
      IsIrreducible N.quotientRepresentation → NaturalLinearThreeTypes N.quotientRepresentation K)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ K I) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose)
      (linearNatural BinaryField.two 3)) := by
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let τ := centralQuotientRepresentation ρ K I hI.choose
  have hs : QuadraticFourGroup.IsIrreducibleSection (ρ.comp K.subtype) τ :=
    ⟨hI.choose_spec.2, invariantSubspace ρ K I hI.choose,
      centralSubspace ρ K I hI.choose, ⟨Representation.Equiv.refl _⟩⟩
  obtain ⟨U, N, hi, hs⟩ :=
    QuadraticFourGroup.SectionReduction.exists_irreducible_section_occurrence ρ K.subtype τ hs
  let σ := N.quotientRepresentation
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := inferInstance
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K hK)
  obtain ⟨J, ⟨b⟩⟩ := hs.exists_equiv_subrepresentation
  have hirr : IsIrreducible J.toRepresentation :=
    (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv b)).mpr hI.choose_spec.2
  have hn : ¬ J.toSubmodule ≤ fixedSpace σ K := by
    intro hj
    have hf (k : K) (v : centralQuotient ρ K I) : τ k v = v := by
      obtain ⟨w, rfl⟩ := b.toLinearEquiv.surjective v
      have hw : J.toRepresentation k w = w := Subtype.ext (hj w.property k)
      exact (LinearMap.congr_fun (b.isIntertwining' k) w).symm.trans
        (congrArg b.toLinearEquiv hw)
    apply hI.not_le_fixedSpace ρ
    rw [← hI.choose_spec.1]
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    have hh := hf ⟨k,hk⟩ (Submodule.Quotient.mk (⟨v,hv⟩ : I))
    have hz : ((fixedSpace ρ K).comap I.subtype).mkQ
        ((⟨ρ k v, (hI.choose hk v).2 hv⟩ : I) - ⟨v,hv⟩) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hh
    exact (Submodule.Quotient.mk_eq_zero ((fixedSpace ρ K).comap I.subtype)).mp hz
  have hJ : IsIrrPlus σ K J.toSubmodule := isIrrPlus_of_simple_noncentral σ K J hirr hn
  obtain ⟨F, hF, ⟨a⟩⟩ := hsections U N hi J.toSubmodule hJ
  let c := ExtensionConsequences.degreeOneNaturalEquiv F hF 3
  refine ⟨⟨a.groupEquiv.trans c.groupEquiv,
    (b.symm.toLinearEquiv.trans a.linearEquiv).trans c.linearEquiv, ?_⟩⟩
  intro k v
  exact (congrArg c.linearEquiv
    ((congrArg a.linearEquiv (LinearMap.congr_fun (b.symm.isIntertwining' k) v)).trans
      (a.intertwines k (b.symm v)))).trans (c.intertwines (a.groupEquiv k) _)

end CFSG.Quasithin.ChapterD
