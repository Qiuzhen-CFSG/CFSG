module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicCentralizer
public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.FieldReduction

/-!
# The six-dimensional source cubic-centralizer module

The actual C_{H/⟨z⟩}(X) acts on Q/Z(Q) through the original map to H/Q.
Its native triple-cover marking makes this action faithful and irreducible.
The central cubic supplies GF(4) scalars on that very vector space; its
dimension becomes six and every group operator remains unchanged. James's
binary intertwiner respects the central scalar, so it is also GF(4)-linear.
The image of the original X is proved to be the entire central cubic.

`source_cubic_structure` assembles the normalizer product, fixed core,
quasisimple centralizer and native six-dimensional module without additional
premises. These are the local conclusions of Aschbacher–Segev, *The uniqueness
of groups of type J₄*, Invent. Math. 105 (1991), (4.1), printed p.597,
DOI 10.1007/BF01232280. This is not the ambient uniqueness theorem.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup LocalGeometry Sporadic.Mathieu Representation
open M22TripleCover.Uniqueness.PointRestriction
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

include h in
/-- The original cubic Sylow, in H/⟨z⟩, is exactly the center of its centralizer. -/
theorem cubicCentralizer_center_image :
    (center (cubicCentralizer e X)).map (cubicCentralizer e X).subtype =
      (cubicSylowImage e X).map (QuotientGroup.mk' (center (centralizer z))) := by
  let A := cubicSylowImage e X
  let q := QuotientGroup.mk' (center (centralizer z))
  let K := A.map q
  have hAcard : Nat.card A = 3 :=
    (card_map_of_injective (CubicLift.subgroup e).subtype_injective).trans (cubicSylow_card e h X)
  let : IsCyclic A := isCyclic_of_prime_card hAcard
  have hKle : K ≤ cubicCentralizer e X := by
    rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg q (congrArg Subtype.val (mul_comm' (⟨b,hb⟩ : A) ⟨a,ha⟩))
  have hle : K ≤ (center (cubicCentralizer e X)).map (cubicCentralizer e X).subtype := by
    intro k hk
    refine ⟨⟨k,hKle hk⟩,mem_center_iff.mpr (fun g => ?_),rfl⟩
    exact Subtype.ext (g.property k hk).symm
  have hc : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk',centralizer_center_card h]
    decide
  have hf := injective_comp_subtype_of_coprime_ker q hc A
    (X.isPGroup'.map (CubicLift.subgroup e).subtype)
  have hKcard : Nat.card K = 3 := by
    have he := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    rw [MonoidHom.range_comp,range_subtype] at he
    exact he.symm.trans hAcard
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective (cubicCentralizer e X).subtype_injective,
    Nat.card_congr (centerCongr (cubicCentralizerTripleEquiv h e X)).toEquiv,
    M22TripleCover.center_card,hKcard]

variable [IsExtraspecial 2 (core z)]

/-- The original binary action, restricted through the literal centralizer projection. -/
noncomputable def cubicCentralizerRepresentation :
    Representation (ZMod 2) (cubicCentralizer e X) (CoreSpace (z := z)) :=
  (coreBinaryRepresentation h).comp
    ((innerPreimage e).subtype.comp (cubicCentralizerProjection h e X))

@[simp] theorem cubicCentralizerRepresentation_apply (g : cubicCentralizer e X)
    (v : CoreSpace (z := z)) :
    cubicCentralizerRepresentation h e X g v =
      coreBinaryRepresentation h (centerToCoreProjection h g.val) v := rfl

theorem cubicCentralizerRepresentation_injective :
    Function.Injective (cubicCentralizerRepresentation h e X) :=
  (coreBinaryRepresentation_injective h).comp
    ((innerPreimage e).subtype_injective.comp (cubicCentralizerProjection_injective h e X))

/-- Identification with the native James module on the actual centralizer. -/
theorem cubicCentralizerRepresentation_james :
    (cubicCentralizerRepresentation h e X).IsIrreducible ∧
      Nonempty (Representation.Equiv (cubicCentralizerRepresentation h e X)
        (M22TripleCover.representationOfEquiv (cubicCentralizerTripleEquiv h e X))) :=
  tripleCover_equiv_of_degree_le_twelve (cubicCentralizerTripleEquiv h e X)
    (cubicCentralizerRepresentation h e X) (cubicCentralizerRepresentation_injective h e X)
    (coreSpace_finrank h).le

/-- Reindexing the same operators by the constructed native group marking. -/
noncomputable def cubicCentralizerNativeRepresentation :
    Representation (ZMod 2) M22TripleCover (CoreSpace (z := z)) :=
  (cubicCentralizerRepresentation h e X).comp (cubicCentralizerTripleEquiv h e X).symm.toMonoidHom

theorem cubicCentralizerNativeRepresentation_injective :
    Function.Injective (cubicCentralizerNativeRepresentation h e X) :=
  (cubicCentralizerRepresentation_injective h e X).comp
    (cubicCentralizerTripleEquiv h e X).symm.injective

instance cubicCentralizerNativeRepresentation_irreducible :
    (cubicCentralizerNativeRepresentation h e X).IsIrreducible :=
  (irreducible_comp_surjective_iff (cubicCentralizerTripleEquiv h e X).symm.toMonoidHom
    (cubicCentralizerTripleEquiv h e X).symm.surjective _).mpr
      (cubicCentralizerRepresentation_james h e X).1

/-- GF(4) scalars defined by the central cubic on the original Q/Z(Q). -/
@[instance_reducible] noncomputable def coreFieldModule : Module F (CoreSpace (z := z)) :=
  fieldModule (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X)

/-- The original centralizer action over its forced central field. -/
noncomputable def cubicCentralizerFieldRepresentation :
    letI := coreFieldModule h e X
    Representation F (cubicCentralizer e X) (CoreSpace (z := z)) :=
  (fieldRepresentation (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X)).comp
      (cubicCentralizerTripleEquiv h e X).toMonoidHom

@[simp] theorem cubicCentralizerFieldRepresentation_apply (g : cubicCentralizer e X)
    (v : CoreSpace (z := z)) :
    cubicCentralizerFieldRepresentation h e X g v = cubicCentralizerRepresentation h e X g v := by
  change cubicCentralizerRepresentation h e X
    ((cubicCentralizerTripleEquiv h e X).symm (cubicCentralizerTripleEquiv h e X g)) v = _
  rw [MulEquiv.symm_apply_apply]

theorem coreField_finrank :
    letI := coreFieldModule h e X
    Module.finrank F (CoreSpace (z := z)) = 6 :=
  field_finrank (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X) (coreSpace_finrank h)

theorem cubicCentralizerFieldRepresentation_injective :
    Function.Injective (cubicCentralizerFieldRepresentation h e X) :=
  (fieldRepresentation_faithful (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X)).comp
      (cubicCentralizerTripleEquiv h e X).injective

theorem cubicCentralizerFieldRepresentation_irreducible :
    letI := coreFieldModule h e X
    (cubicCentralizerFieldRepresentation h e X).IsIrreducible := by
  let := coreFieldModule h e X
  exact (irreducible_comp_surjective_iff (cubicCentralizerTripleEquiv h e X).toMonoidHom
    (cubicCentralizerTripleEquiv h e X).surjective _).mpr
      (M22TripleCover.DegreeTwentyFour.fieldRepresentation_isIrreducible
        (cubicCentralizerNativeRepresentation h e X)
        (cubicCentralizerNativeRepresentation_injective h e X))

/-- The primitive field scalar is the action of the marked central cubic element. -/
theorem coreField_scalar (v : CoreSpace (z := z)) :
    letI := coreFieldModule h e X
    cubicCentralizerRepresentation h e X
      ((cubicCentralizerTripleEquiv h e X).symm M22TripleCover.scalar) v =
        (QuadraticAlgebra.omega : F) • v :=
  field_scalar (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X) v

private noncomputable def binaryEquivOverField
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) M22TripleCover W) [ρ.IsIrreducible]
    (hf : Function.Injective ρ)
    (E : Representation.Equiv ρ M22TripleCover.binaryRepresentation) :
    letI := fieldModule ρ hf
    letI := fieldModule M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful
    Representation.Equiv (fieldRepresentation ρ hf)
      (fieldRepresentation M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful) := by
  letI := fieldModule ρ hf
  letI := fieldModule M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful
  refine .mk { E.toLinearEquiv.toAddEquiv with map_smul' := ?_ } ?_
  · intro a v
    change E (a.re • v + a.im • ρ M22TripleCover.scalar v) =
      a.re • E v + a.im • M22TripleCover.binaryRepresentation M22TripleCover.scalar (E v)
    rw [map_add, map_smul, map_smul]
    exact congrArg (fun w => a.re • E v + a.im • w)
      (LinearMap.congr_fun (E.isIntertwining' M22TripleCover.scalar) v)
  · intro g
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (E.isIntertwining' g) v

/-- The actual six-dimensional module is equivalent over GF(4) to the native one. -/
theorem cubicCentralizerField_equiv_native :
    letI := coreFieldModule h e X
    letI := fieldModule M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful
    Nonempty (Representation.Equiv (cubicCentralizerFieldRepresentation h e X)
      ((fieldRepresentation M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful).comp
        (cubicCentralizerTripleEquiv h e X).toMonoidHom)) := by
  let := coreFieldModule h e X
  let := fieldModule M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful
  obtain ⟨E⟩ := M22TripleCover.Uniqueness.equiv_of_finrank_twelve
    (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X) (coreSpace_finrank h)
  let f := binaryEquivOverField (cubicCentralizerNativeRepresentation h e X)
    (cubicCentralizerNativeRepresentation_injective h e X) E
  refine ⟨.mk f.toLinearEquiv (fun g => ?_)⟩
  exact f.isIntertwining' (cubicCentralizerTripleEquiv h e X g)

omit [IsExtraspecial 2 (core z)] in
/-- Construct the source (4.1) local package from IsTypeJ4, retaining X, Q,
the centralizer in H/⟨z⟩, and every vector operator under the native comparison. -/
theorem source_cubic_structure :
    letI := h.extraspecial
    ∃ (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
      (X : Sylow 3 (CubicLift.subgroup e)),
      Nat.card X = 3 ∧
      (∀ g : centralizer z, ∃ q : core z,
        ∃ n : normalizer (cubicSylowImage e X : Set (centralizer z)), (q : centralizer z) * n = g) ∧
      (Subgroup.centralizer (cubicSylowImage e X : Set (centralizer z))).subgroupOf (core z) =
        center (core z) ∧
      IsQuasisimple (cubicCentralizer e X) ∧
      Nonempty (cubicCentralizer e X ≃* M22TripleCover) ∧
      (center (cubicCentralizer e X)).map (cubicCentralizer e X).subtype =
        (cubicSylowImage e X).map (QuotientGroup.mk' (center (centralizer z))) ∧
      letI := coreFieldModule h e X
      Module.finrank F (CoreSpace (z := z)) = 6 ∧
      (cubicCentralizerFieldRepresentation h e X).IsIrreducible ∧
      Function.Injective (cubicCentralizerFieldRepresentation h e X) ∧
      (∀ g v, cubicCentralizerFieldRepresentation h e X g v =
        coreBinaryRepresentation h (centerToCoreProjection h g.val) v) ∧
      letI := fieldModule M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful
      Nonempty (Representation.Equiv (cubicCentralizerFieldRepresentation h e X)
        ((fieldRepresentation M22TripleCover.binaryRepresentation M22TripleCover.binaryRepresentation_faithful).comp
          (cubicCentralizerTripleEquiv h e X).toMonoidHom)) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (CubicLift.subgroup e)))
  exact ⟨e,X,cubicSylow_card e h X,exists_core_mul_cubicNormalizer e h X,
    core_cubic_centralizer h e X,cubicCentralizer_quasisimple h e X,
    ⟨cubicCentralizerTripleEquiv h e X⟩,cubicCentralizer_center_image h e X,
    coreField_finrank h e X,cubicCentralizerFieldRepresentation_irreducible h e X,
    cubicCentralizerFieldRepresentation_injective h e X,
    cubicCentralizerFieldRepresentation_apply h e X,cubicCentralizerField_equiv_native h e X⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
