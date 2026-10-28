module

public import Theory.AlgebraicGroup.RootSubgroups.Defs

/-!
The subgroup attached to a cocharacter by limits at zero.

An element belongs when its actual inverse-conjugation curve extends from the
multiplicative group to an affine-line morphism. Products and inverses of these
morphisms prove the subgroup laws. The separate centralizer condition expresses
regularity geometrically, without selecting roots or a positive system.

This is the limit construction underlying Borel, *Linear Algebraic Groups*,
IV, 13.3 and 13.8--13.10. This module only defines the subgroup; identifying it
with an arbitrary Borel remains a geometric theorem. The inverse conjugation
agrees with `RootWeightEquation` and reverses the source's direct-conjugation
cocharacter convention.
-/

universe u

namespace Theory.AlgebraicGroup.BorelCocharacter

variable {k : Type u} [Field k]
variable {G : Variety k} [AlgebraicGroup G] {T : ClosedSubgroup G}

/-- Extension to zero of the actual inverse-conjugation curve. No value at
zero is prescribed; this is the limit condition for the associated parabolic. -/
@[expose]
public def HasLimit (c : ClosedSubgroupTorusCocharacter T) (g : Variety.Point G) : Prop :=
  ∃ f : Variety.Morphism (KPlus k) G,
    ∀ t : Variety.Point (KMult k),
      f.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) =
        (T.includePoint (c.onPoints t))⁻¹ * g * T.includePoint (c.onPoints t)

/-- Elements whose inverse-conjugation curve extends to the affine line form
an actual subgroup: multiply or invert their extension morphisms. -/
@[expose]
public def limitSubgroup (c : ClosedSubgroupTorusCocharacter T) : Subgroup (Variety.Point G) where
  carrier := {g | HasLimit c g}
  one_mem' := by
    refine ⟨Variety.Morphism.const _ _ 1, ?_⟩
    intro t
    change 1 = _
    simp
  mul_mem' := by
    rintro a b ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨(AlgebraicGroup.mulMorphism G).comp (f.pair g), ?_⟩
    intro t
    change f.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) *
      g.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)) = _
    rw [hf, hg]
    group
  inv_mem' := by
    rintro a ⟨f, hf⟩
    refine ⟨(AlgebraicGroup.invMorphism G).comp f, ?_⟩
    intro t
    change (f.toFun (kPlusPoint (dPointEquiv 1 t 0 : k)))⁻¹ = _
    rw [hf]
    group

/-- The centralizer of the cocharacter image is contained in `T`.
When `T` is a torus, the reverse inclusion follows from commutativity. -/
@[expose]
public def CentralizesOnlyTorus (c : ClosedSubgroupTorusCocharacter T) : Prop :=
  ∀ g : Variety.Point G,
    (∀ t : Variety.Point (KMult k),
      (T.includePoint (c.onPoints t))⁻¹ * g * T.includePoint (c.onPoints t) = g) →
    g ∈ T

/-- Membership in the limit subgroup is the existence of an extension
morphism, with the literal inverse-conjugation convention. -/
public theorem mem_limitSubgroup_iff
    (c : ClosedSubgroupTorusCocharacter T) (g : Variety.Point G) :
    g ∈ limitSubgroup c ↔ HasLimit c g := Iff.rfl

end Theory.AlgebraicGroup.BorelCocharacter
