module
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.FaithfulSections
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductExchange
public import CFSG.Quasithin.Chapter10.SourceA5ProductAlternatives
public import Theory.Representation.OrthogonalFourPlusMatrix.TensorRecognition
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Models for the actual original local type

The local central image is preserved by the original Sylow element t.
Its induced linear map exchanges the marked A₅ factors, with the actual
first-factor twist induced by t². The unrestricted binary A₅ classifier
then leaves a cubic-free product or the deleted tensor square. The former
has determinant coordinates with surjective markings of both factors.

These coordinates concern the original local image before V=V_M is known.
They supply non-FF model recognition for the invariant sections in
Aschbacher–Smith D.3.9(1), printed pp.199–200, using D.3.7, pp.197–199.
-/

public noncomputable section
open Representation Representation.QuadraticFourGroup
  Representation.QuadraticFourGroup.TensorClassification
open BinaryPermutation.FiveTensorSquare
namespace CFSG.Quasithin.Chapter10
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Cubic-free irreducible A₅ factors give the literal determinant action
with both factor markings, independently of any full/local equality. -/
theorem source_a5_cubic_free_determinant_coordinates
    (σ : Representation (ZMod 2) (Alt × Alt) V) [σ.IsIrreducible]
    (hfree : CubicFreeOnFactors σ) :
    ∃ j₁ j₂ : Alt ≃* Matrix.SpecialLinearGroup (Fin 2) ClassicalOrthogonal.FourPlusMatrix.Binary.F,
      Nonempty (σ.Equiv (ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp
        (j₁.prodCongr j₂).toMonoidHom)) := by
  let j : Alt ≃* Factor 2 :=
    (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (GaloisField.card 2 2 (by decide))).some.symm
  let : Group.IsPerfect Alt := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Factor 2) :=
    Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
  let σ' : Representation (ZMod 2) (Factor 2 × Factor 2) V := σ.comp (j.symm.prodCongr j.symm).toMonoidHom
  let : σ'.IsIrreducible :=
    (irreducible_comp_surjective_iff (j.symm.prodCongr j.symm).toMonoidHom (j.symm.prodCongr j.symm).surjective σ).mpr inferInstance
  have hfree' : CubicFreeOnFactors σ' := by
    constructor
    · intro g hg v hv
      apply hfree.1 (j.symm g)
        ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change σ (j.symm g,j.symm 1) v = v at hv
      simpa only [map_one] using hv
    · intro g hg v hv
      apply hfree.2 (j.symm g)
        ((orderOf_injective j.symm.toMonoidHom j.symm.injective g).trans hg) v
      change σ (j.symm 1,j.symm g) v = v at hv
      simpa only [map_one] using hv
  obtain ⟨j₁,j₂,⟨b⟩⟩ :=
    ClassicalOrthogonal.FourPlusMatrix.TensorRecognition.exists_binary_determinant_equiv σ' hfree'
  refine ⟨j.trans j₁,j.trans j₂,⟨Representation.Equiv.mk b.toLinearEquiv ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  have h := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap
    ((j.prodCongr j) g) v
  change b.toLinearEquiv (σ (j.symm (j g.1), j.symm (j g.2)) v) = _ at h
  change b.toLinearEquiv (σ (j.symm (j g.1),j.symm (j g.2)) v) =
    ClassicalOrthogonal.FourPlusMatrix.Binary.action (j₁ (j g.1),j₂ (j g.2))
      (b.toLinearEquiv v) at h
  change b.toLinearEquiv (σ g v) =
    ClassicalOrthogonal.FourPlusMatrix.Binary.action (j₁ (j g.1),j₂ (j g.2))
      (b.toLinearEquiv v)
  simpa only [j.symm_apply_apply] using h

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Chapter3.Section02 Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
attribute [local instance] tensorSectionsElementary tensorSectionsLocalElementary

/-- The actual local type has natural determinant or deleted-square coordinates,
using the original Sylow element to exchange its two marked factors. -/
theorem source_a5_original_local_type_models
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* Alt)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G)) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    let := (source_full_module_reduced D).normal
    let qM := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
    let J := ((localOrbit T L).subgroupOf D.maximalLocal).map qM
    ∀ τ : Representation (ZMod 2) (D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal))
        (Additive D.fullCentralQuotient),
      (∀ (m : D.maximalLocal) (v : D.fullModule),
        τ (qM m) (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(m : G) * (v : G) * (m : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule m.property) v).mp
                v.property⟩)) →
    ∀ S : Subrepresentation (τ.comp J.subtype),
      S.toSubmodule = (originalLocalCentralLinearProjection D).range →
      S.toRepresentation.IsIrreducible → Function.Injective S.toRepresentation →
      ∃ b : Alt × Alt ≃* J,
        (∃ f : Alt × Alt →* ClassicalOrthogonal.FourPlusMatrix.Binary.G,
          Function.Surjective f ∧ Nonempty (Representation.Equiv (S.toRepresentation.comp b.toMonoidHom)
            (ClassicalOrthogonal.FourPlusMatrix.Binary.action.comp f))) ∨
        Nonempty (Representation.Equiv (S.toRepresentation.comp b.toMonoidHom) deletedAction) := by
  dsimp only
  let M := D.maximalLocal
  let U := D.fullModule.subgroupOf M
  let := (source_full_module_reduced D).normal
  let qM := QuotientGroup.mk' (centralizer (U : Set M))
  let J := ((localOrbit T L).subgroupOf M).map qM
  intro τ hτ S hr hS hSf
  let q := originalA5ProductProjection D e hn ht htn
  have hq := originalA5ProductProjection_surjective D e hn ht htn
  obtain ⟨i,hi,_,hcompat⟩ := source_a5_original_product_embedding D e hn ht htn
  have hiJ (g : Alt × Alt) : i g ∈ J := by
    obtain ⟨x,rfl⟩ := hq g
    rw [hcompat]
    exact ⟨inclusion (localOrbit T L).le_normalizer x,x.property,rfl⟩
  let j : Alt × Alt →* J := i.codRestrict J hiJ
  have hji : Function.Injective j := by
    intro g h he
    exact hi (congrArg Subtype.val he)
  have hjs : Function.Surjective j := by
    rintro ⟨z,m,hm,rfl⟩
    refine ⟨q ⟨m,hm⟩,Subtype.ext ?_⟩
    exact hcompat ⟨m,hm⟩
  let b : Alt × Alt ≃* J := MulEquiv.ofBijective j ⟨hji,hjs⟩
  let σ : Representation (ZMod 2) (Alt × Alt) S.toSubmodule :=
    S.toRepresentation.comp b.toMonoidHom
  let : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff b.toMonoidHom b.surjective S.toRepresentation).mpr hS
  have hσf : Function.Injective σ := hSf.comp b.injective
  obtain ⟨a,ha,_,_,_⟩ := BinaryPermutation.AlternatingFiveLinearTwo.exists_cubic_fixed_ne_zero
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  have hleft : ∃ g, σ (g,1) ≠ 1 := by
    refine ⟨a,fun h => ha1 (congrArg Prod.fst (hσf (h.trans σ.map_one.symm)))⟩
  have hright : ∃ g, σ (1,g) ≠ 1 := by
    refine ⟨a,fun h => ha1 (congrArg Prod.snd (hσf (h.trans σ.map_one.symm)))⟩
  let tm : M := ⟨t,le_normalizer_componentOrbit L T ht⟩
  let α := originalA5ConjugationTwist D e hn ht
  have hconj (g : Alt × Alt) : qM tm * i g * (qM tm)⁻¹ = i (α g.2,g.1) := by
    obtain ⟨x,rfl⟩ := hq g
    rw [← originalA5ProductProjection_conjugate D e hn ht htn x, hcompat, hcompat]
    change qM ⟨t,_⟩ * qM ⟨x,_⟩ * (qM ⟨t,_⟩)⁻¹ = qM _
    rw [← map_inv,← map_mul,← map_mul]
    rfl
  have hmap : S.toSubmodule.map (τ (qM tm)) = S.toSubmodule := by
    rw [hr]
    exact (subspace_map_eq_iff (τ.comp qM) _ tm).mpr
      (originalLocalCentralLinearProjection_sylow_invariant D (τ.comp qM) hτ ht)
  let E : S.toSubmodule ≃ₗ[ZMod 2] S.toSubmodule :=
    (S.toSubmodule.equivMapOfInjective (τ (qM tm)) (apply_bijective τ _).injective).trans
      (LinearEquiv.ofEq _ _ hmap)
  have hE (g : Alt × Alt) (v : S.toSubmodule) :
      E (σ g v) = σ (α g.2,(MulEquiv.refl Alt) g.1) (E v) := by
    apply Subtype.ext
    change τ (qM tm) (τ (i g) v.val) = τ (i (α g.2,g.1)) (τ (qM tm) v.val)
    simp only [← Module.End.mul_apply,← map_mul]
    exact congrArg (fun g => τ g v.val) (mul_inv_eq_iff_eq_mul.mp (hconj g))
  rcases source_a5_product_module_alternatives σ hleft hright E α (MulEquiv.refl Alt) hE
      with hfree | hdeleted
  · obtain ⟨j₁,j₂,he⟩ := source_a5_cubic_free_determinant_coordinates σ hfree
    exact ⟨b,Or.inl ⟨(j₁.prodCongr j₂).toMonoidHom,(j₁.prodCongr j₂).surjective,he⟩⟩
  · exact ⟨b,Or.inr hdeleted⟩

end CFSG.Quasithin.Chapter10
