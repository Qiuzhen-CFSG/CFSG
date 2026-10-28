module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Constituents
public import CFSG.Quasithin.Chapter10.SourceA5FullTensorPassage.LocalModel
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Automorphisms

/-!
# Tensor recognition with the actual exchanged factor action

The marked product identifies the two components with A₅. Conjugation by the
original moving Sylow element exchanges those factors, with two actual factor
automorphisms; no involution assumption on that element is needed. The binary
product classification therefore leaves the natural tensor and the deleted
square. The latter violates the ambient cubic bound in its full normalizer.

The remaining tensor has determinant coordinates, and the determinant model
identifies both the entire group and the entire vector space with the literal
orthogonal carrier used by the original projection argument.

Source: Aschbacher–Smith, D.3.7, printed pp.197–199, specialized to the
field-four branch of 13.8.16(1), pp.952–953.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
open F918Sections.NoStrong
local notation "Alt" => alternatingGroup (Fin 5)
variable {D F U : Type*} [Group D] [Finite D] [Field F] [Finite F] [CharP F 2]
    (a : ExchangedActor KnownSimple.IsKnownSimple D F 2)
    [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U)

/-- The actual moving Sylow element exchanges the marked A₅ factors. -/
theorem exchanged_product_coordinates :
    ∃ e : a.orbit ≃* (Alt × Alt), ∃ E : U ≃ₗ[ZMod 2] U,
    ∃ α β : MulAut Alt, ∀ g v,
      E (σ (e.symm g) v) = σ (e.symm (α g.2,β g.1)) (E v) := by
  let : a.orbit.Normal := a.orbit_normal
  obtain ⟨j⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := F) (by simpa using a.field_card)
  let e := a.productEquiv.trans (j.prodCongr j)
  let n := a.orbit.normalizerMonoidHom
    ⟨(a.mover : D),le_normalizer_of_normal (mem_top _)⟩
  let φ := e.symm.trans (n.trans e)
  have hfirst (x : a.orbit) (hx : (x : D) ∈ a.component) : (e x).2 = 1 := by
    have hm : a.productEquiv x ∈ (⊤ : Subgroup PSL(2,F)).prod ⊥ :=
      a.first_mark ▸ mem_map_of_mem a.productEquiv.toMonoidHom hx
    change j (a.productEquiv x).2 = 1
    rw [mem_bot.mp hm.2,map_one]
  have hsecond (x : a.orbit) (hx : (x : D) ∈ a.second) : (e x).1 = 1 := by
    have hm : a.productEquiv x ∈ (⊥ : Subgroup PSL(2,F)).prod ⊤ :=
      a.second_mark ▸ mem_map_of_mem a.productEquiv.toMonoidHom hx
    change j (a.productEquiv x).1 = 1
    rw [mem_bot.mp hm.1,map_one]
  have hswap : ∃ α β : MulAut Alt, ∀ g, φ g = (α g.2,β g.1) := by
    rcases BinaryPermutation.FiveTensorSquare.product_automorphism_alternatives φ with hkeep | hswap
    · obtain ⟨α,β,hα⟩ := hkeep
      let : IsQuasisimple a.component := a.component_isComponent.2
      let : IsSimpleGroup (a.component ⧸ center a.component) := IsQuasisimple.simple
      let : Nontrivial a.component := (QuotientGroup.mk'_surjective (center a.component)).nontrivial
      obtain ⟨x,hx⟩ := exists_ne (1 : a.component)
      let y : a.orbit := ⟨x,a.component_le x.property⟩
      have hy : (n y : D) ∈ a.second := by
        rw [← a.moved]
        exact mem_map_of_mem (MulAut.conj (a.mover : D)).toMonoidHom x.property
      have he : (e y).1 = 1 := by
        apply α.injective
        have hh := congrArg Prod.fst (hα (e y))
        change (e (n (e.symm (e y)))).1 = α (e y).1 at hh
        rw [e.symm_apply_apply,hsecond (n y) hy] at hh
        exact hh.symm.trans α.map_one.symm
      have he' : e y = 1 := Prod.ext he (hfirst y x.property)
      have hy' : y = 1 := e.injective (he'.trans e.map_one.symm)
      have hx' : (x : D) = 1 := congrArg (fun z : a.orbit => (z : D)) hy'
      exact (hx (Subtype.ext hx')).elim
    · exact hswap
  obtain ⟨α,β,hφ⟩ := hswap
  let E := LinearEquiv.ofBijective (σ (a.mover : D)) (σ.apply_bijective _)
  refine ⟨e,E,α,β,?_⟩
  intro g v
  have hx : e.symm (α g.2,β g.1) = n (e.symm g) := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (hφ g).symm
  rw [hx]
  change σ (a.mover : D) (σ (e.symm g) v) = σ (n (e.symm g)) (σ (a.mover : D) v)
  rw [normalizerMonoidHom_apply_apply_coe]
  simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]


/-- A faithful irreducible restriction with the original exchange has the
whole eight-dimensional orthogonal model under a cubic bound of two. -/
theorem orthogonal_of_irreducible_restriction [FiniteDimensional (ZMod 2) U]
    [IsIrreducible (σ.comp a.orbit.subtype)]
    (hσ : Function.Injective σ) (hc : cubicRatio σ ≤ 2) :
    HasOrthogonalFourOrbit σ a.orbit := by
  let : a.orbit.Normal := a.orbit_normal
  obtain ⟨e,E,α,β,hE⟩ := exchanged_product_coordinates a σ
  let i := a.orbit.subtype.comp e.symm.toMonoidHom
  let τ : Representation (ZMod 2) (Alt × Alt) U := σ.comp i
  let : τ.IsIrreducible := (irreducible_comp_surjective_iff e.symm.toMonoidHom
    e.symm.surjective (σ.comp a.orbit.subtype)).mpr inferInstance
  have hf : Function.Injective τ := hσ.comp (a.orbit.subtype_injective.comp e.symm.injective)
  obtain ⟨g,hg⟩ := exists_ne (1 : Alt)
  have hl : ∃ g, τ (g,1) ≠ 1 := ⟨g,fun h => hg (congrArg Prod.fst (hf (h.trans (map_one τ).symm)))⟩
  have hr : ∃ g, τ (1,g) ≠ 1 := ⟨g,fun h => hg (congrArg Prod.snd (hf (h.trans (map_one τ).symm)))⟩
  rcases Chapter10.source_a5_product_module_alternatives τ hl hr E α β hE with hfree | hdeleted
  · obtain ⟨j₁,j₂,⟨b⟩⟩ := Chapter10.source_a5_cubic_free_determinant_coordinates τ hfree
    let f := (e.trans (j₁.prodCongr j₂)).trans
      ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv
    let z := b.toLinearEquiv.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates.symm
    refine ⟨f,z,?_⟩
    intro x v
    apply ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates.injective
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
      (ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates.symm (b (σ x v))) = _
    rw [LinearEquiv.apply_symm_apply]
    have hb := Representation.IntertwiningMap.isIntertwining _ _ b.toIntertwiningMap (e x) v
    change b (σ (e.symm (e x)) v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action ((j₁.prodCongr j₂) (e x)) (b v) at hb
    rw [e.symm_apply_apply] at hb
    rw [hb]
    change _ = ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
      (ClassicalOrthogonal.projectiveElementaryNatural
        (ClassicalOrthogonal.formD 2 ClassicalOrthogonal.FourPlusMatrix.Binary.F)
        (ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv ((j₁.prodCongr j₂) (e x))) (z v))
    rw [ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates_projective_equivariant]
    change _ = ClassicalOrthogonal.FourPlusMatrix.Binary.action _
      (ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
        (ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates.symm (b v)))
    rw [LinearEquiv.apply_symm_apply]
  · obtain ⟨b⟩ := hdeleted
    have hi : i.range = a.orbit := by
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,←MonoidHom.range_eq_map,range_subtype]
    let : i.range.Normal := hi.symm ▸ a.orbit_normal
    obtain ⟨B,hB,_,hb⟩ := (cubicRatio_le_nat_iff σ 2).mp hc
    exact ((not_lt_of_ge hb) (BinaryPermutation.FiveTensorSquare.faithful_actor_ratio_gt_two σ hσ i b hB)).elim

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
