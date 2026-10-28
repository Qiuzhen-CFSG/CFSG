module

public import Theory.Representation.G2NaturalSemilinear
public import Theory.Representation.InvolutoryExtensionEquivalence
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Automorphisms

/-!
# Markings for the Hall--Janko natural restriction

A marking embeds the actual degree-100 permutation carrier in G₂(4) and its
actual permutation extension in the inner-field extension of G₂(4). The two
embeddings agree on the carrier, and the specified outside involution maps
to coefficient Frobenius. No existence of such a marking is asserted here.

Given this geometric input, the natural quotient gives literal binary actions
of both groups. We prove the restriction identity, field compatibility and
coordinate equivalence, rather than identifying the module by its dimension.
These are the precise representation conventions used by K.4.5, printed p.460
of Aschbacher--Smith. The ATLAS permutation and octonion attributions are retained
in the imported constructions.
-/

@[expose] public noncomputable section

namespace Sporadic.LeechRelated.J2.G2FourModule
open ExceptionalParabolics
open Atlas.G2.Natural.BinarySemilinear

abbrev F := Four
abbrev V := Atlas.G2.Natural.Space F
abbrev M := Atlas.G2.Model F
abbrev OuterM := Actor F

/-- Geometric input; its existence is a separate concrete embedding theorem. -/
structure MarkedEmbedding where
  inner : Carrier →* M
  inner_injective : Function.Injective inner
  outer : Extension →* OuterM
  outer_injective : Function.Injective outer
  on_inner : ∀ j, outer (intoExtension j) = SemidirectProduct.inl (inner j)
  on_involution : outer extensionInvolution = SemidirectProduct.inr fourFrobenius

namespace MarkedEmbedding
variable (d : MarkedEmbedding)

/-- The natural G₂(4) action restricted to the marked J₂ carrier. -/
def innerRepresentation : Representation (ZMod 2) Carrier V :=
  (Atlas.G2.Natural.BinarySemilinear.innerRepresentation F).comp d.inner

/-- The actual extension action, including its marked coefficient involution. -/
def outerRepresentation : Representation (ZMod 2) Extension V :=
  (representation F).comp d.outer

/-- The same extension action expressed in the six F₄ coordinates. -/
def outerCoordinates : Representation (ZMod 2) Extension (Coordinates F) :=
  (coordinateRepresentation F).comp d.outer

/-- Restriction recovers precisely the literal natural action through `inner`. -/
theorem outer_on_inner (j : Carrier) (v : V) :
    d.outerRepresentation (intoExtension j) v = Atlas.G2.Natural.action F (d.inner j) v := by
  change representation F (d.outer (intoExtension j)) v = _
  rw [d.on_inner, representation_inner]

/-- Equality as representations, without changing either group map. -/
theorem restriction_eq : d.outerRepresentation.comp intoExtension = d.innerRepresentation := by
  apply MonoidHom.ext
  intro j
  apply LinearMap.ext
  intro v
  change representation F (d.outer (intoExtension j)) v =
    representation F (SemidirectProduct.inl (d.inner j)) v
  rw [d.on_inner]

/-- The specified outside involution acts by the actual quotient field map. -/
theorem outer_on_involution (v : V) :
    d.outerRepresentation extensionInvolution v = fieldEquivalence F fourFrobenius v := by
  change representation F (d.outer extensionInvolution) v = _
  rw [d.on_involution, representation_field]

/-- The group marking itself intertwines the actual J₂ and G₂ field actions. -/
theorem inner_involution (j : Carrier) :
    d.inner (involutionAut j) = Atlas.G2.fieldEquiv fourFrobenius (d.inner j) := by
  have hj : intoExtension (involutionAut j) =
      extensionInvolution * intoExtension j * extensionInvolution⁻¹ := by
    apply Subtype.ext
    rfl
  have h := congrArg d.outer hj
  rw [map_mul, map_mul, map_inv, d.on_inner, d.on_inner, d.on_involution] at h
  have h' : d.inner (involutionAut j) =
      Atlas.G2.LieAutomorphismExtensions.fieldAction fourFrobenius (d.inner j) := by
    simpa using congrArg SemidirectProduct.left h
  exact h'

/-- Field compatibility on the actual restricted module. -/
theorem field_inner_action (j : Carrier) (v : V) :
    fieldEquivalence F fourFrobenius (d.innerRepresentation j v) =
      d.innerRepresentation (involutionAut j) (fieldEquivalence F fourFrobenius v) := by
  change fieldEquivalence F fourFrobenius
      (representation F (SemidirectProduct.inl (d.inner j)) v) =
    representation F (SemidirectProduct.inl (d.inner (involutionAut j))) _
  rw [representation_inner, representation_inner, d.inner_involution]
  exact fieldEquivalence_action F fourFrobenius (d.inner j) v

/-- An equivariant identification of the quotient with the displayed coordinates. -/
def coordinateEquivalence : Representation.RepEquiv d.outerRepresentation d.outerCoordinates where
  toLinearEquiv := coordinatesEquiv F
  isIntertwining' x := LinearMap.ext (coordinates_representation F (d.outer x))

/-- Inner equivalence extends to the actual permutation extension. In particular
the outside action needs no extra scalar-centralizer or normalizer hypothesis. -/
theorem exists_outer_equivalence {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) Extension W)
    [Representation.IsIrreducible (k := ZMod 2) (ρ.comp intoExtension)]
    [Representation.IsIrreducible d.innerRepresentation]
    (c : Representation.RepEquiv (ρ.comp intoExtension) d.innerRepresentation) :
    Nonempty (Representation.RepEquiv ρ d.outerRepresentation) := by
  have hgen : intoExtension.range ⊔ Subgroup.zpowers extensionInvolution = ⊤ := by
    rw [show intoExtension = Subgroup.inclusion
      (show generated ≤ extension from le_sup_left) from rfl, Subgroup.inclusion_range]
    apply Subgroup.map_injective extension.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
      (show generated ≤ extension from le_sup_left), MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  have ht : extensionInvolution ^ 2 = 1 := by
    apply Subtype.ext
    change involution ^ 2 = 1
    simpa only [pow_two] using involution_mul_self
  let : Representation.IsIrreducible (k := ZMod 2)
      (d.outerRepresentation.comp intoExtension) := by
    rw [d.restriction_eq]
    infer_instance
  have c' : Representation.RepEquiv (ρ.comp intoExtension)
      (d.outerRepresentation.comp intoExtension) := by
    rw [d.restriction_eq]
    exact c
  apply Representation.exists_equiv_of_irreducible_restriction_involution
    ρ d.outerRepresentation intoExtension involutionAut extensionInvolution ht
    (fun _ => ?_) hgen c'
  apply Subtype.ext
  rfl

end MarkedEmbedding
end Sporadic.LeechRelated.J2.G2FourModule
