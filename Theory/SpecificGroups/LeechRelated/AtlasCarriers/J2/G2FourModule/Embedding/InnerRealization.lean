module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.Extension
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.PresentationExact
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.OctonionPair
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Realizing the Hall--Janko marking from the five-relator presentation

The certified presentation comparison identifies the presented group with the
literal degree-100 permutation carrier. Its universal map to the certified
octonion pair then gives the concrete inner homomorphism `inner`.
Simplicity of the carrier and a nontrivial first image prove injectivity;
the two Frobenius identities propagate by generation and supply the complete
outer marking `markedEmbedding` through `markedOfEquivariant`.

This constructs the group embedding and field marking used in
Aschbacher--Smith, K.4.5, printed p.460/PDF p.471. Only the inherited simplicity
of the carrier remains explicit for injectivity; presentation exactness and
all octonion equations are discharged here. Binary irreducibility and the
source module recognition remain with the parent assembly. The general
conditional constructions are retained for reuse.
-/

@[expose] public noncomputable section
namespace Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization
open ExceptionalParabolics Atlas.G2.Natural.BinarySemilinear

variable (hp : Function.Injective Presentation.toCarrier)

/-- The exact comparison, conditional on injectivity of the published surjection. -/
def carrierEquiv : Presentation.UniversalGroup ≃* Carrier :=
  MulEquiv.ofBijective Presentation.toCarrier ⟨hp, Presentation.toCarrier_surjective⟩

@[simp] theorem carrierEquiv_zero :
    carrierEquiv hp (PresentedGroup.of 0) = GeneratorPair.a := Presentation.toCarrier_zero

@[simp] theorem carrierEquiv_one :
    carrierEquiv hp (PresentedGroup.of 1) = GeneratorPair.b := Presentation.toCarrier_one

/-- The inner homomorphism obtained from the concrete octonion pair. -/
def innerOfRelations (x y : M) (h : Presentation.Relations x y) : Carrier →* M :=
  (Presentation.toGroup x y h).comp (carrierEquiv hp).symm.toMonoidHom

@[simp] theorem innerOfRelations_a (x y : M) (h : Presentation.Relations x y) :
    innerOfRelations hp x y h GeneratorPair.a = x := by
  change Presentation.toGroup x y h ((carrierEquiv hp).symm GeneratorPair.a) = x
  rw [← carrierEquiv_zero hp, MulEquiv.symm_apply_apply, Presentation.toGroup_zero]

@[simp] theorem innerOfRelations_b (x y : M) (h : Presentation.Relations x y) :
    innerOfRelations hp x y h GeneratorPair.b = y := by
  change Presentation.toGroup x y h ((carrierEquiv hp).symm GeneratorPair.b) = y
  rw [← carrierEquiv_one hp, MulEquiv.symm_apply_apply, Presentation.toGroup_one]

/-- The inherited simple-group hypothesis eliminates the kernel. -/
theorem innerOfRelations_injective [IsSimpleGroup Carrier]
    (x y : M) (h : Presentation.Relations x y) (hx : x ≠ 1) :
    Function.Injective (innerOfRelations hp x y h) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (innerOfRelations hp x y h).ker inferInstance with hk | hk
  · exact hk
  · have ha : GeneratorPair.a ∈ (innerOfRelations hp x y h).ker := by rw [hk]; trivial
    exact (hx (by simpa only [MonoidHom.mem_ker, innerOfRelations_a] using ha)).elim

/-- The concrete generator identities enforce the required field marking. -/
theorem innerOfRelations_equivariant (x y : M) (h : Presentation.Relations x y)
    (hx : x = Atlas.G2.fieldEquiv fourFrobenius x)
    (hy : y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y) :
    ∀ j, innerOfRelations hp x y h (involutionAut j) =
      Atlas.G2.fieldEquiv fourFrobenius (innerOfRelations hp x y h j) := by
  let f := innerOfRelations hp x y h
  have heq : f.comp involutionAut.toMonoidHom =
      (Atlas.G2.fieldEquiv fourFrobenius).toMonoidHom.comp f := by
    apply MonoidHom.eq_of_eqOn_dense GeneratorPair.closure_pair_eq_top
    intro j hj
    rcases Set.mem_insert_iff.mp hj with rfl | hj
    · simpa [f] using hx
    · rw [Set.mem_singleton_iff] at hj
      subst j
      simpa [f] using hy
  exact fun j => DFunLike.congr_fun heq j

/-- Actual application of the extension theorem to the presentation construction. -/
def markedOfRelations [IsSimpleGroup Carrier]
    (x y : M) (h : Presentation.Relations x y) (hx : x ≠ 1)
    (hσx : x = Atlas.G2.fieldEquiv fourFrobenius x)
    (hσy : y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y) : MarkedEmbedding :=
  markedOfEquivariant (innerOfRelations hp x y h)
    (innerOfRelations_injective hp x y h hx)
    (innerOfRelations_equivariant hp x y h hσx hσy)

@[simp] theorem markedOfRelations_inner_a [IsSimpleGroup Carrier]
    (x y : M) (h : Presentation.Relations x y) (hx : x ≠ 1)
    (hσx : x = Atlas.G2.fieldEquiv fourFrobenius x)
    (hσy : y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y) :
    (markedOfRelations hp x y h hx hσx hσy).inner GeneratorPair.a = x :=
  innerOfRelations_a hp x y h

@[simp] theorem markedOfRelations_inner_b [IsSimpleGroup Carrier]
    (x y : M) (h : Presentation.Relations x y) (hx : x ≠ 1)
    (hσx : x = Atlas.G2.fieldEquiv fourFrobenius x)
    (hσy : y⁻¹ = Atlas.G2.fieldEquiv fourFrobenius y) :
    (markedOfRelations hp x y h hx hσx hσy).inner GeneratorPair.b = y :=
  innerOfRelations_b hp x y h

/-- The concrete homomorphism from the literal degree-100 carrier to G₂(4). -/
def inner : Carrier →* Atlas.G2.Model (GaloisField 2 2) :=
  innerOfRelations PresentationExact.toCarrier_injective
    OctonionPair.x OctonionPair.y OctonionPair.relations

@[simp] theorem inner_a : inner GeneratorPair.a = OctonionPair.x :=
  innerOfRelations_a _ _ _ _

@[simp] theorem inner_b : inner GeneratorPair.b = OctonionPair.y :=
  innerOfRelations_b _ _ _ _

/-- The nonidentity octonion image and inherited simplicity give faithfulness. -/
theorem inner_injective [IsSimpleGroup Carrier] : Function.Injective inner :=
  innerOfRelations_injective _ _ _ _ OctonionPair.x_ne_one

/-- The literal permutation involution agrees with coefficient Frobenius. -/
theorem inner_equivariant (j : Carrier) :
    inner (involutionAut j) = Atlas.G2.fieldEquiv fourFrobenius (inner j) :=
  innerOfRelations_equivariant _ _ _ _
    OctonionPair.x_frobenius OctonionPair.y_inv_frobenius j

/-- The concrete marked embedding, with all presentation and octonion inputs proved. -/
def markedEmbedding [IsSimpleGroup Carrier] : MarkedEmbedding :=
  markedOfEquivariant inner inner_injective inner_equivariant

@[simp] theorem markedEmbedding_inner [IsSimpleGroup Carrier] :
    markedEmbedding.inner = inner := rfl

/-- The constructed outer map is injective on the literal permutation extension. -/
theorem markedEmbedding_outer_injective [IsSimpleGroup Carrier] :
    Function.Injective markedEmbedding.outer :=
  markedEmbedding.outer_injective

@[simp] theorem markedEmbedding_on_inner [IsSimpleGroup Carrier] (j : Carrier) :
    markedEmbedding.outer (intoExtension j) = SemidirectProduct.inl (inner j) :=
  markedEmbedding.on_inner j

@[simp] theorem markedEmbedding_on_involution [IsSimpleGroup Carrier] :
    markedEmbedding.outer extensionInvolution = SemidirectProduct.inr fourFrobenius :=
  markedEmbedding.on_involution

/-- Existence of the actual group marking needed by the module-recognition consumer. -/
theorem nonempty_markedEmbedding [IsSimpleGroup Carrier] : Nonempty MarkedEmbedding :=
  ⟨markedEmbedding⟩

end Sporadic.LeechRelated.J2.G2FourModule.Embedding.InnerRealization
