module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Models
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.SymplecticBound
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.Geometry

/-!
# Symmetric natural-module exclusions from intrinsic type a₂

A faithful isometric binary action and the intrinsic type-a₂ hypotheses give
the small conjugate-product bound. In a natural normal A₇ extension this forces
a transposition, contradicting displacement rank two. For the split
six-dimensional orthogonal action, including every subgroup of index at most
two, it forces four disjoint transpositions, whose moved-plane stabilizer is
transitive. The permutation conjugators and normalizer witnesses are proved
in the imported model calculations.

The model adapter retains both the group equivalence and the intertwining
linear equivalence. For the literal split quadratic space, faithfulness and
the nondegenerate alternating polar form are derived from its actual action.
No product-order bound, class table, or normalizer transitivity is assumed.
The normal A₇ theorem applies in particular when that subgroup is F*(G).

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708). The type convention is Definition E.2.6,
printed p.218 (PDF p.229).
-/

namespace Representation.RankTwo.Symmetric
open BinaryPermutation Atlas.Order20160A8

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The actual natural normal A₇ action admits no faithful isometric extension
containing a type-a₂ involution. This excludes G.11.2(4). -/
public theorem seven_extension_not_type_a2
    (K : Subgroup G) [K.Normal]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 7))
    (eV : V ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ k : K, ∀ x, eV (ρ k x) =
      alternatingCoreRepresentation (Fin 7) (eK k) (eV x))
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (v : G) (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hType : ∀ x, B x (ρ v x) = 0) : False := by
  let := eV.symm.finiteDimensional
  have hv : v ≠ 1 := by
    rintro rfl
    rw [movedSpace, map_one, sub_self, LinearMap.range_zero, finrank_bot] at hr
    omega
  exact seven_extension_rank_ne_two K ρ hρ eK eV he v hv hv2
    (smallConjugateProducts_of_type_a2 B ρ hAlt hND hρ hpres v hv2 hr hType) hr

/-- G.11.2(5), transported through the actual group and module identifications.
The source type-a₂ hypotheses discharge the conjugate-product premise. -/
public theorem split_orthogonal_model_stabilizerTransitive_of_type_a2
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (H : Subgroup (O_DPlus 3 (ZMod 2))) (hH : H.index ≤ 2)
    (e : G ≃* H) (f : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 3 (ZMod 2))
    (hf : ∀ g x, f (ρ g x) = (splitOrthogonalAction.comp H.subtype) (e g) (f x))
    (B : LinearMap.BilinForm (ZMod 2) V) (hAlt : B.IsAlt) (hND : B.Nondegenerate)
    (hpres : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (v : G) (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2) (movedSpace ρ v) = 2)
    (hType : ∀ x, B x (ρ v x) = 0) :
    StabilizerTransitive ρ (movedSpace ρ v) := by
  let := f.symm.finiteDimensional
  have hv : v ≠ 1 := by
    rintro rfl
    rw [movedSpace, map_one, sub_self, LinearMap.range_zero, finrank_bot] at hr
    omega
  have hb := smallConjugateProducts_of_type_a2 B ρ hAlt hND hρ hpres v hv2 hr hType
  apply stabilizerTransitive_transport ρ _ e f hf v
  apply split_orthogonal_stabilizerTransitive H hH (e v)
  · exact fun h => hv (e.injective (h.trans e.map_one.symm))
  · rw [← map_pow, hv2, map_one]
  · exact hb.map e
  · exact (finrank_movedSpace_transport ρ _ e f hf v).symm.trans hr

/-- The literal split orthogonal natural module, with its own polar form.
This includes the index-two subgroup; the cubic witnesses are even. -/
public theorem split_orthogonal_stabilizerTransitive_of_type_a2
    (H : Subgroup (O_DPlus 3 (ZMod 2))) (hH : H.index ≤ 2)
    (v : H) (hv2 : v ^ 2 = 1)
    (hr : Module.finrank (ZMod 2)
      (movedSpace (splitOrthogonalAction.comp H.subtype) v) = 2)
    (hType : ∀ x, (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin x
      ((splitOrthogonalAction.comp H.subtype) v x) = 0) :
    StabilizerTransitive (splitOrthogonalAction.comp H.subtype)
      (movedSpace (splitOrthogonalAction.comp H.subtype) v) := by
  have hfaith : Function.Injective (splitOrthogonalAction.comp H.subtype) := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact LinearMap.congr_fun he x
  have hAlt : (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin.IsAlt := by
    intro x
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self,
      two_nsmul, CharTwo.add_self_eq_zero]
  have hpres (g : H) (x y : ClassicalOrthogonal.VectorD 3 (ZMod 2)) :
      (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin
        ((splitOrthogonalAction.comp H.subtype) g x)
        ((splitOrthogonalAction.comp H.subtype) g y) =
      (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin x y := by
    have hg := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mp g.val.property
    change (ClassicalOrthogonal.formD 3 (ZMod 2)).polarBilin (g.val.val x) (g.val.val y) = _
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hg]
  exact split_orthogonal_model_stabilizerTransitive_of_type_a2 _ hfaith H hH
    (MulEquiv.refl H) (LinearEquiv.refl _ _) (fun _ _ => rfl)
    _ hAlt ClassicalOrthogonal.polarD_nondegenerate hpres v hv2 hr hType

end Representation.RankTwo.Symmetric
