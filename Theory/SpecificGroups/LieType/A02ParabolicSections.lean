module

public import Theory.Quasithin
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Marked sections of proper two-local normalizers

The geometric input to a parabolic-section argument consists of a nontrivial
two-subgroup, its proper normalizer, and a surjection from an actual subgroup
of that normalizer. The kernel is normal in this numerator, not necessarily
in the ambient group. We retain the surjection and its literal quotient.

The constructors below accept a subgroup map or an embedding into the ambient
group and restrict it to the normalizer. They assert no exceptional-group
geometry. For the application to Aschbacher–Smith A.2.18 (printed p.40 of
`refs/quasithin.pdf`), the family constructions must additionally identify
this normalizer with the root-defined parabolic of GLS3 §2.6.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType

universe u v w
variable (H : Type u) (S : Type v) [Group H] [Group S]

/-- An actual quotient section of the normalizer of a nontrivial two-subgroup.
This is construction data, not a claim that a particular family has such a section. -/
structure NormalizerSection where
  twoSubgroup : Subgroup H
  nontrivial : twoSubgroup ≠ ⊥
  twoGroup : IsPGroup 2 twoSubgroup
  proper : Subgroup.normalizer (twoSubgroup : Set H) ≠ ⊤
  numerator : Subgroup (Subgroup.normalizer (twoSubgroup : Set H))
  quotient : numerator →* S
  onto : Function.Surjective quotient

namespace NormalizerSection
variable {H S} (d : NormalizerSection H S)

theorem isTwoLocal : IsTwoLocal (Subgroup.normalizer (d.twoSubgroup : Set H)) :=
  ⟨d.twoSubgroup, d.nontrivial, d.twoGroup, rfl⟩

/-- The section is the quotient by the kernel of the stored map. -/
noncomputable def quotientEquiv : (d.numerator ⧸ d.quotient.ker) ≃* S :=
  QuotientGroup.quotientKerEquivOfSurjective d.quotient d.onto

/-- The quotient marking agrees on every representative with the original map. -/
@[simp] theorem quotientEquiv_mk (x : d.numerator) :
    d.quotientEquiv (QuotientGroup.mk' d.quotient.ker x) = d.quotient x := rfl

variable {T : Type w} [Group T]

/-- Change the target only through an actual group isomorphism. -/
def mapTarget (e : S ≃* T) : NormalizerSection H T where
  twoSubgroup := d.twoSubgroup
  nontrivial := d.nontrivial
  twoGroup := d.twoGroup
  proper := d.proper
  numerator := d.numerator
  quotient := e.toMonoidHom.comp d.quotient
  onto := e.surjective.comp d.onto

/-- Restrict an ambient numerator to the literal two-local normalizer. -/
noncomputable def ofSurjection (Q U : Subgroup H)
    (hQ : Q ≠ ⊥) (h₂ : IsPGroup 2 Q)
    (hproper : Subgroup.normalizer (Q : Set H) ≠ ⊤)
    (hU : U ≤ Subgroup.normalizer (Q : Set H))
    (f : U →* S) (hf : Function.Surjective f) : NormalizerSection H S where
  twoSubgroup := Q
  nontrivial := hQ
  twoGroup := h₂
  proper := hproper
  numerator := U.subgroupOf (Subgroup.normalizer (Q : Set H))
  quotient := f.comp (Subgroup.subgroupOfEquivOfLe hU).toMonoidHom
  onto := hf.comp (Subgroup.subgroupOfEquivOfLe hU).surjective

/-- A faithful subgroup in the normalizer is a section, with its range as numerator. -/
noncomputable def ofEmbedding (Q : Subgroup H)
    (hQ : Q ≠ ⊥) (h₂ : IsPGroup 2 Q)
    (hproper : Subgroup.normalizer (Q : Set H) ≠ ⊤)
    (f : S →* H) (hf : Function.Injective f)
    (hU : f.range ≤ Subgroup.normalizer (Q : Set H)) : NormalizerSection H S :=
  ofSurjection Q f.range hQ h₂ hproper hU
    (MonoidHom.ofInjective hf).symm.toMonoidHom (MonoidHom.ofInjective hf).symm.surjective

end NormalizerSection
end Theory.SpecificGroups.LieType
