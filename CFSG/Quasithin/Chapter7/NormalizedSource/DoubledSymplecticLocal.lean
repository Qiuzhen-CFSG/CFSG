module
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.Extensions.StandardGeometry
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.ScalarKernel
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Local parameters on the full paired symplectic automizer

The coefficient kernel calculation places square-one preserving operators
in the full symplectic image. H.7's inner geometry then supplies the minimum
involution bound and the strict fixed-space-family bound for the entire
standard normalizer, including its scalar, field and swapping operators.
Normalizer coverage transports these estimates to every diagram-moving pair.

For a nonbinary marked normal component, conjugation coordinates embed the
actual ambient actor in this normalizer. The chosen-module application is
`NonFFSourceDoubledSymplecticLocal`: the seed nonisomorphism forces the original
conjugator to move the diagram, and both seed axes are retained. The global
centralizer bound r ≥ m and weak-closure bound w ≤ n are separate obligations.

Source: Aschbacher--Smith H.7, printed pp.388--389, and 7.1--7.3,
printed pp.696--699 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open SymplecticConjugatePair SymplecticConjugatePair.Ambient
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterH.Section05To09.SymplecticPair
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

theorem doubledSymplectic_standard_parameters {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    3*n ≤ ChapterE.moduleM (standardAction (F := F)) ∧
      ChapterE.moduleA (standardAction (F := F)) < (2*n : ℕ) := by
  constructor
  · exact standard_moduleM_lower_of_kernel standard_square_one_coefficient_kernel_le_full hF
      (Involutions.involution_fixedCodim_lower hF)
  · have he := standard_family_two_n_empty_of_coefficients
      standardCoefficient standardCoefficient_smul standard_square_one_coefficient_kernel_le_full
      hn (pair_fixedSpaceFamily_empty hF hn)
    have ha := (ChapterE.moduleA_le_iff_next_family_empty
      (standardAction (F := F)) (2*n-1)).mpr (by
        rw [show 2*n-1+1 = 2*n by omega]
        exact he)
    exact ha.trans_lt (ENat.natCast_lt_natCast.mpr (by omega))

private theorem moduleM_ge_of_embedding {H J U W : Type*} [Group H] [Group J]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) J W)
    (f : H →* J) (hf : Function.Injective f) (E : U ≃ₗ[ZMod 2] W)
    (he : ∀ g v, E (ρ g v) = σ (f g) (E v)) :
    ChapterE.moduleM σ ≤ ChapterE.moduleM ρ := by
  apply le_csInf ⟨_, Set.mem_insert _ _⟩
  rintro d (rfl | ⟨g,hg,rfl⟩)
  · rw [E.finrank_eq]
    exact ChapterE.moduleM_le_dimension σ
  · have hi : orderOf (f g) = 2 := (orderOf_injective f hf g).trans hg
    have hc := fixedCodim_map_equivariant ρ σ f E he (Subgroup.zpowers g)
    rw [MonoidHom.map_zpowers] at hc
    exact hc ▸ ChapterE.moduleM_le_involution σ hi

theorem doubledSymplectic_normalizer_parameters (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    3*n ≤ ChapterE.moduleM (normalizerAction τ) ∧
      ChapterE.moduleA (normalizerAction τ) < (2*n : ℕ) := by
  obtain ⟨E,φ,hE,_,_⟩ := Normalizer.exists_standardAmbient_equiv τ hτ
  have hi : ∀ x v, E.symm (normalizerAction τ x v) =
      standardAction (φ.symm x) (E.symm v) := by
    intro x v
    apply E.injective
    rw [E.apply_symm_apply,hE,φ.apply_symm_apply,E.apply_symm_apply]
  have hs := doubledSymplectic_standard_parameters hF hn
  exact ⟨hs.1.trans (moduleM_ge_of_embedding _ _ φ.symm.toMonoidHom φ.symm.injective E.symm hi),
    (ChapterE.moduleA_le_of_equivariant_injective _ _ φ.symm.toMonoidHom φ.symm.injective
      E.symm hi).trans_lt hs.2⟩

theorem doubledSymplectic_pair_coordinates {J U : Type*} [Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) J U) (q : J →* Sp F)
    (e : U ≃ₗ[ZMod 2] Vector F)
    (he : ∀ j v, e (ρ j v) = symplecticNatural 2 (q j) (e v))
    (α : MulAut J) (a : MulAut (Sp F)) (ha : ∀ j, a (q j) = q (α j))
    (hne : ¬ Nonempty (ρ.Equiv (ρ.comp α.toMonoidHom))) :
    ¬ PreservesDiagram a ∧
      ∃ E : (U × U) ≃ₗ[ZMod 2] Space F,
        (∀ j v, E ((ρ.prod (ρ.comp α.toMonoidHom)) j v) = graphPair (q j) (E v)) ∧
        (∀ v, (E v).1 = 0 ↔ v.1 = 0) ∧
        (∀ v, (E v).2 = 0 ↔ v.2 = 0) := by
  have hmove : ¬ PreservesDiagram a := by
    intro hp
    obtain ⟨g,σ,hg⟩ := SemilinearClassification.inner_field_of_preservesDiagram a hp
    apply hne
    let b := (e.trans (innerFieldVector g σ)).trans e.symm
    refine ⟨Representation.Equiv.mk b ?_⟩
    intro j
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (b (ρ j v)) = e (ρ (α j) (b v))
    rw [he]
    change e (e.symm (innerFieldVector g σ (e (ρ j v)))) =
      symplecticNatural 2 (q (α j)) (e (e.symm (innerFieldVector g σ (e v))))
    rw [e.apply_symm_apply,e.apply_symm_apply,he,← ha,hg]
    exact innerFieldVector_intertwines g σ (q j) (e v)
  obtain ⟨C,hC,hU,hW⟩ := exists_graphPair_equiv a hmove
  let E := (e.prodCongr e).trans C.symm
  refine ⟨hmove,E,?_,?_,?_⟩
  · intro j v
    apply C.injective
    change C (C.symm (e (ρ j v.1),e (ρ (α j) v.2))) =
      C (graphPair (q j) (E v))
    rw [C.apply_symm_apply,hC]
    change (e (ρ j v.1),e (ρ (α j) v.2)) =
      (symplecticNatural 2 (q j) (C (E v)).1,
       symplecticNatural 2 (a (q j)) (C (E v)).2)
    change (e (ρ j v.1),e (ρ (α j) v.2)) =
      (symplecticNatural 2 (q j) (C (C.symm (e v.1,e v.2))).1,
       symplecticNatural 2 (a (q j)) (C (C.symm (e v.1,e v.2))).2)
    rw [C.apply_symm_apply,ha,he,he]
  · intro v
    have h := hW (E v)
    rw [mem_secondSummand,mem_secondSummand] at h
    change (C (C.symm (e v.1,e v.2))).1 = 0 ↔ (E v).1 = 0 at h
    rw [C.apply_symm_apply] at h
    exact h.symm.trans e.map_eq_zero_iff
  · intro v
    have h := hU (E v)
    rw [mem_firstSummand,mem_firstSummand] at h
    change (C (C.symm (e v.1,e v.2))).2 = 0 ↔ (E v).2 = 0 at h
    rw [C.apply_symm_apply] at h
    exact h.symm.trans e.map_eq_zero_iff

/-- A faithful ambient actor normalizing the marked full symplectic image
embeds in the normalizer of the derived pair. The field is nonbinary here. -/
theorem doubledSymplectic_parameters_of_marked_normal_range
    {H J U : Type*} [Group H] [Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (i : J →* H) [i.range.Normal]
    (q : J →* Sp F) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] Space F)
    (hE : ∀ j v, E (ρ (i j) v) = graphPair (q j) (E v))
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    3*n ≤ ChapterE.moduleM ρ ∧ ChapterE.moduleA ρ < (2*n : ℕ) := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 = 2^1 from rfl) ▸ (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hn
  let _ := perfect_of_card_gt_two hcard
  let γ : Representation (ZMod 2) H (Space F) := E.conjRingEquiv.toMonoidHom.comp ρ
  have he (g : H) (v : U) : E (ρ g v) = γ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hres (j : J) : linearAction γ (i j) = linearAction graphPair (q j) := by
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    exact (he (i j) v).symm.trans (hE j v)
  have himage : i.range.map (linearAction γ) = derivedImage (graphAut (F := F)) := by
    ext z
    constructor
    · rintro ⟨_,⟨j,rfl⟩,rfl⟩
      refine ⟨⟨q j,?_⟩, (hres j).symm⟩
      rw [Group.IsPerfect.commutator_eq_top]
      exact mem_top _
    · rintro ⟨x,rfl⟩
      obtain ⟨j,hj⟩ := hq x.val
      exact ⟨i j,⟨j,rfl⟩,(hres j).trans (congrArg (linearAction graphPair) hj)⟩
  have hm (g : H) : linearAction γ g ∈ pairedNormalizer (graphAut (F := F)) := by
    change linearAction γ g ∈ normalizer (derivedImage (graphAut (F := F)) : Set _)
    rw [← himage]
    exact i.range.le_normalizer_map (linearAction γ)
      (mem_map_of_mem _ (show g ∈ normalizer (i.range : Set H) from
        le_normalizer_of_normal (mem_top g)))
  let f : H →* pairedNormalizer (graphAut (F := F)) := (linearAction γ).codRestrict _ hm
  have hf : Function.Injective f := by
    intro x y hxy
    exact linearAction_injective γ hγ (congrArg Subtype.val hxy)
  have hfE : ∀ g v, E (ρ g v) = normalizerAction graphAut (f g) (E v) := he
  have hs := doubledSymplectic_normalizer_parameters (graphAut (F := F))
    graphAut_not_preservesDiagram hF (by omega)
  exact ⟨hs.1.trans (moduleM_ge_of_embedding _ _ f hf E hfE),
    (ChapterE.moduleA_le_of_equivariant_injective _ _ f hf E hfE).trans_lt hs.2⟩

end CFSG.Quasithin.Chapter7.NormalizedSource
