module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.Outer
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.QuadraticQuotient
/-!
# The Mathieu code and cocode actions are not FF modules

The checked Sylow calculations bound every elementary quadratic actor by order
four, on both M24 and the full M22 pair stabilizer. Coordinate duality gives the
same bounds on the actual code actions. Every involution displaces at least
four dimensions for M24, and at least three for the M22 pair stabilizer.
Thompson replacement therefore excludes all offenders. Restriction through the
literal inclusions gives the native M23 and inner M22 conclusions.
Source: Aschbacher--Smith H.15--16 and K.4.2--4, printed pp.399--403,458--459.
-/
public section
open Sporadic.Mathieu Representation Representation.BinaryOffender
open MathieuCode.CocodeOctad.Involutions
namespace MathieuCode.QuadraticActors
noncomputable section

private lemma quadratic_dual_iff {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) :
    IsQuadratic ρ A ↔ IsQuadratic ρ.dual A := by
  have hρ : IsQuadratic ρ A ↔
      Coinvariants.ker (ρ.comp A.subtype) ≤ Representation.invariants (ρ.comp A.subtype) := by
    rw [commutator_le_invariants_iff]
    exact ⟨fun h g t v => h g g.property t t.property v,
      fun h g hg t ht v => h ⟨g,hg⟩ ⟨t,ht⟩ v⟩
  have hd : IsQuadratic ρ.dual A ↔
      Coinvariants.ker (Representation.dual (ρ.comp A.subtype)) ≤
        Representation.invariants (Representation.dual (ρ.comp A.subtype)) := by
    rw [commutator_le_invariants_iff]
    exact ⟨fun h g t v => h g g.property t t.property v,
      fun h g hg t ht v => h ⟨g,hg⟩ ⟨t,ht⟩ v⟩
  exact hρ.trans ((commutator_le_invariants_iff_dual _).trans hd.symm)

lemma m24_code_card_le_four (A : Subgroup M24) [IsElementaryAbelian 2 A]
    (hq : IsQuadratic codeRepresentation A) : Nat.card A ≤ 4 := by
  apply m24_cocode_card_le_four A
  apply (quadratic_dual_iff cocodeRepresentation A).mpr
  exact quadratic_of_equivariant_surjection codeRepresentation cocodeRepresentation.dual
    codeDuality.toLinearMap codeDuality.toLinearEquiv.surjective
    (fun g v => LinearMap.congr_fun (codeDuality.isIntertwining' g) v) A hq

lemma m22Outer_code_card_le_four (A : Subgroup m22PairStabilizer)
    [IsElementaryAbelian 2 A] (hq : IsQuadratic m22OuterCodeRepresentation A) :
    Nat.card A ≤ 4 := by
  apply m22Outer_cocode_card_le_four A
  apply (quadratic_dual_iff m22OuterCocodeRepresentation A).mpr
  exact quadratic_of_equivariant_surjection m22OuterCodeRepresentation
    m22OuterCocodeRepresentation.dual m22CodeCocodeDuality.toLinearMap
    m22CodeCocodeDuality.surjective m22CodeCocodeDuality_equivariant A hq

lemma m24_cocode_involution_gt_two (g : M24) (hg : orderOf g = 2) :
    2 < fixedCodim cocodeRepresentation (Subgroup.zpowers g) := by
  rcases M24InvolutionCentralizers.involution_classes g hg with hz | ht
  · rw [fixedCodim_of_isConj_z g hz]
    decide
  · rw [fixedCodim_of_isConj_t g ht]
    decide

lemma code_not_isFFModule : ¬ IsFFModule codeRepresentation := by
  apply not_isFFModule_of_quadratic_card_le_four
  · intro A hA hq
    let : IsElementaryAbelian 2 A := hA
    exact m24_code_card_le_four A hq
  · intro g hg
    rw [code_cocode_fixedCodim_zpowers]
    exact m24_cocode_involution_gt_two g hg

lemma cocode_not_isFFModule : ¬ IsFFModule cocodeRepresentation := by
  apply not_isFFModule_of_quadratic_card_le_four
  · intro A hA hq
    let : IsElementaryAbelian 2 A := hA
    exact m24_cocode_card_le_four A hq
  · exact m24_cocode_involution_gt_two

lemma m23Code_not_isFFModule : ¬ IsFFModule m23CodeRepresentation := by
  intro h
  exact code_not_isFFModule (h.map_equivariant m23CodeRepresentation codeRepresentation
    pointEmbedding pointEmbedding_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))

lemma m23Cocode_not_isFFModule : ¬ IsFFModule m23CocodeRepresentation := by
  intro h
  exact cocode_not_isFFModule (h.map_equivariant m23CocodeRepresentation cocodeRepresentation
    pointEmbedding pointEmbedding_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))

lemma m22OuterCode_not_isFFModule : ¬ IsFFModule m22OuterCodeRepresentation := by
  apply not_isFFModule_of_quadratic_card_le_four
  · intro A hA hq
    let : IsElementaryAbelian 2 A := hA
    exact m22Outer_code_card_le_four A hq
  · intro g hg
    exact lt_of_lt_of_le (by decide : 2 < 3) (m22Outer_involution_displacement_ge_three g hg).1

lemma m22OuterCocode_not_isFFModule : ¬ IsFFModule m22OuterCocodeRepresentation := by
  apply not_isFFModule_of_quadratic_card_le_four
  · intro A hA hq
    let : IsElementaryAbelian 2 A := hA
    exact m22Outer_cocode_card_le_four A hq
  · intro g hg
    exact lt_of_lt_of_le (by decide : 2 < 3) (m22Outer_involution_displacement_ge_three g hg).2
lemma m22Code_not_isFFModule : ¬ IsFFModule m22CodeRepresentation := by
  intro h
  apply m22OuterCode_not_isFFModule
  exact h.map_equivariant m22CodeRepresentation m22OuterCodeRepresentation
    m22ToPairStabilizer (fun _ _ he => m22Embedding_injective (congrArg Subtype.val he))
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

lemma m22Cocode_not_isFFModule : ¬ IsFFModule m22CocodeRepresentation := by
  intro h
  apply m22OuterCocode_not_isFFModule
  exact h.map_equivariant m22CocodeRepresentation m22OuterCocodeRepresentation
    m22ToPairStabilizer (fun _ _ he => m22Embedding_injective (congrArg Subtype.val he))
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

end
end MathieuCode.QuadraticActors
