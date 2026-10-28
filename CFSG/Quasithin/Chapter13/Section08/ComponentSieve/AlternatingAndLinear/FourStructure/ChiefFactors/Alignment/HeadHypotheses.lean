module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment.Models
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# The B.4 hypotheses on each maximal L₄ quotient

The literal quotient by a maximal subrepresentation is irreducible. A generating
irreducible two-space injects into it, and simplicity of the actual GL₄(2) actor
then forces faithfulness: a trivial action would leave every seed line invariant.
The original elementary quadratic actor descends with no increase in fixed
codimension. Thus a universal B.4.2/B.4.5 input applies to every maximal quotient,
without assuming its model or orientation beforehand.

`LinearB4` is the explicit earlier classification input specialized to the actual
L₄(2) group. It retains faithfulness, irreducibility and the small quadratic ratio,
and identifies the natural, dual and exterior-square representations equivariantly.
It is a hypothesis specification, not a proof of that earlier classification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(9–10),
B.4.5, printed pp.86–87; 13.8.25, printed pp.960–961 (PDF pp.977–978).
-/

@[expose] public section

open Representation Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]

/-- A maximal quotient is faithful: a trivial kernel alternative would make every
line of its injective irreducible seed invariant, contradicting seed dimension two. -/
theorem maximal_quotient_faithful (ρ : Representation (ZMod 2) H U) (s : GeneratingSeed ρ)
    [IsSimpleGroup H] (W : Subrepresentation ρ) (hW : IsCoatom W) :
    Function.Injective W.quotientRepresentation := by
  apply W.quotientRepresentation.ker_eq_bot_iff.mp
  rcases (MonoidHom.normal_ker W.quotientRepresentation).eq_bot_or_eq_top with h | h
  · exact h
  have hfix : ∀ g : s.parabolic, ∀ v ∈ s.space, ρ g v = v := by
    intro g v hv
    apply congrArg Subtype.val (s.quotient_injective ρ W hW.1
      (a₁ := ⟨ρ g v, s.space.apply_mem_toSubmodule g hv⟩) (a₂ := ⟨v, hv⟩) ?_)
    have he := MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top (g : H))
    exact congrArg (fun f : Module.End (ZMod 2) (U ⧸ W.toSubmodule) => f (W.toSubmodule.mkQ v)) he
  have hs0 : s.space.toSubmodule ≠ ⊥ := by
    intro hzero
    have hd := s.dim_two
    rw [hzero, finrank_bot] at hd
    contradiction
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff s.space.toSubmodule).mp hs0
  let X : Subrepresentation (ρ.comp s.parabolic.subtype) :=
    ⟨Submodule.span (ZMod 2) {v}, fun g u hu => by
      change ρ g u ∈ Submodule.span (ZMod 2) {v}
      rw [hfix g u ((Submodule.span_singleton_le_iff_mem v s.space.toSubmodule).mpr hv hu)]
      exact hu⟩
  have hX : X ≠ ⊥ := by
    intro hzero
    have hm : v ∈ X := Submodule.subset_span (by simp)
    exact hv0 (show v ∈ (⊥ : Subrepresentation (ρ.comp s.parabolic.subtype)) from hzero ▸ hm)
  have he : X = s.space := (s.irreducible.le_iff_eq hX).mp
    ((Submodule.span_singleton_le_iff_mem v s.space.toSubmodule).mpr hv)
  have hd := congrArg (fun S : Subrepresentation (ρ.comp s.parabolic.subtype) =>
    Module.finrank (ZMod 2) S.toSubmodule) he
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) = _ at hd
  rw [finrank_span_singleton hv0, s.dim_two] at hd
  contradiction

/-- The actual projective-to-linear equivalence transports simplicity of PSL₄(2). -/
theorem simple_actor (eH : H ≃* BinaryLinear.GL NaturalSpace) : IsSimpleGroup H := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 4 (by decide)
  exact (eH.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4)).symm).isSimpleGroup

universe v
/-- Universal earlier B.4 specialization, retaining the genuine models and all action hypotheses. -/
def LinearB4 (eH : H ≃* BinaryLinear.GL NaturalSpace) : Prop :=
  ∀ (E : Type v) [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (σ : Representation (ZMod 2) H E),
    Function.Injective σ → IsIrreducible σ →
    quadraticRatio σ ≤ 2 → HeadAlternatives σ eH

variable {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] [Finite H]

/-- All B.4 action hypotheses hold on every maximal quotient. The original
quadratic actor survives, and its fixed codimension cannot increase. -/
theorem maximal_quotient_alternatives (ρ : Representation (ZMod 2) H E) (s : GeneratingSeed ρ)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hB4 : LinearB4.{v} eH)
    (A : Subgroup H) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hb : fixedCodim ρ A ≤ 2 * rank A) (W : Subrepresentation ρ) (hW : IsCoatom W) :
    HeadAlternatives W.quotientRepresentation eH := by
  let : IsSimpleGroup H := simple_actor eH
  apply hB4 (E ⧸ W.toSubmodule) W.quotientRepresentation
    (maximal_quotient_faithful ρ s W hW) (SimpleHeadQuotient.irreducible_quotient_of_isCoatom W hW)
  apply (quadraticRatio_le_two_iff W.quotientRepresentation).mpr
  exact ⟨A, hA, quadratic_of_equivariant_surjection ρ W.quotientRepresentation
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq,
    (fixedCodim_le_of_equivariant_surjection ρ W.quotientRepresentation
      W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans hb⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Alignment
