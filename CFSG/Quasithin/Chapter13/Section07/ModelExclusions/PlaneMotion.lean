module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.CoveredSeed
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections
public import Theory.GroupTheory.PPerfectHom
/-!
# The source plane survives in the component section

The original Sylow flag has a two-group stabilizer in the natural
six-letter action. Its two-perfect point residual therefore cannot
normalize the plane V₂: that would trivialize its action, contrary to
V₃=[V₃,L₁]. If V₂ vanished in the component section, the literal
conjugation action would put [V₂,L₁] in V₁ and force precisely this
normalization. Thus an actual plane vector has nonzero section image.

Source: Aschbacher–Smith, the contained-L₁ case of13.7.6, printed p.939.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
private theorem flag_image_twoGroup : IsPGroup 2
    (subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁) ⊓
      subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₂) : Subgroup (Equiv.Perm (Fin 6))) := by
  let f := permutation d
  let Q := (T.subtype (show (T : Subgroup G) ≤ L ⊔ T from le_sup_right)).mapSurjective
    f.rangeRestrict_surjective
  have hQ : (Q : Subgroup f.range).map f.range.subtype =
      ((T : Subgroup G).subgroupOf (L ⊔ T)).map f := by
    rw [Sylow.coe_mapSurjective, map_map, Sylow.coe_subtype]
    rfl
  obtain ⟨g, hP, hE⟩ := sylow_flag_of_between f.range (alternating_le_range d) Q
    (image d V₁) (image d V₂)
    (image_dim d V₁ (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) 1 d.line_card)
    (image_dim d V₂ (d.plane_le_seed.trans d.seed_le) 2 d.plane_card)
    (by intro x hx; exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₁ d.line_stable (hQ ▸ hx)))
    (by intro x hx; exact (mem_stabilizer_iff_map _ _).mp (image_stable d V₂ d.plane_stable (hQ ▸ hx)))
  change IsPGroup 2 (flagStabilizer (image d V₁) ⊓ flagStabilizer (image d V₂) : Subgroup (Equiv.Perm (Fin 6)))
  rw [hP, hE, flagStabilizer_move, flagStabilizer_move, flagStabilizer_line,
    flagStabilizer_plane, ← map_inf _ _ _ (MulAut.conj (g : Equiv.Perm (Fin 6))).injective,
    ← canonicalSylow_coe]
  exact canonicalSylow.isPGroup'.map _

/-- The original point residual moves the original Sylow plane. -/
theorem point_residual_not_normalizes_plane :
    ¬ sourceOne L T V₁ ≤ normalizer (V₂ : Set G) := by
  intro hn
  let A := subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₁) ⊓
    subspaceStabilizer (naturalRepresentation (Fin 6)) (image d V₂)
  let f := (permutation d).comp (inclusion ((one_le L T V₁).trans inf_le_left))
  have hf : ∀ x, f x ∈ A := by
    intro x
    exact ⟨(permutation_stabilizes_iff d V₁
      (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le)) _).mpr
        (((one_le L T V₁).trans inf_le_right) x.property),
      (permutation_stabilizes_iff d V₂ (d.plane_le_seed.trans d.seed_le) _).mpr (hn x.property)⟩
  have hf1 := (residual_isPPerfect ((L ⊔ (T : Subgroup G)) ⊓ normalizer (V₁ : Set G))).hom_eq_one_of_isPGroup
    (flag_image_twoGroup d) (f.codRestrict A hf)
  have hc : sourceOne L T V₁ ≤ centralizer (V : Set G) := by
    intro x hx
    apply (permutation_eq_one_iff d ⟨x, ((one_le L T V₁).trans inf_le_left) hx⟩).mp
    exact congrArg Subtype.val (DFunLike.congr_fun hf1 ⟨x,hx⟩)
  have hs : ⁅V₃, sourceOne L T V₁⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (centralizer_le d.seed_le))
  rw [seed_commutator_point_residual d] at hs
  have hcard := d.seed_card
  rw [hs, card_bot] at hcard
  norm_num at hcard

open Section08.TransvectionRecognition Component
variable {H K : Subgroup G}
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]

/-- Every original plane vector belongs to the literal component commutator image. -/
theorem plane_vector_mem_commutator
    (hKH : K ≤ H) (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (v : V₂) :
    seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩ ∈ commutatorImage H V₃ V₁ K := by
  rw [commutatorImage_eq_subspaceCommutator K hKH ρ hρ]
  have hm := seed_mem_commutator ρ hρ (sourceOne L T V₁) (hL₁K.trans hKH)
    (seed_commutator_point_residual d).symm ⟨v, d.plane_le_seed v.property⟩
  apply Submodule.span_mono ?_ hm
  rintro w ⟨a, ha, u, hu, hw⟩
  exact ⟨a, Subgroup.map_mono (subgroupOf_mono H hL₁K) ha, u, hu, hw⟩

/-- An actual vector of V₂ survives the quotient by K-fixed vectors. -/
theorem exists_plane_section_nonzero
    (hKH : K ≤ H) (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) :
    ∃ v : V₂, (Submodule.Quotient.mk
      (⟨seedVector H V₃ V₁ ⟨v, d.plane_le_seed v.property⟩,
        plane_vector_mem_commutator d hKH hL₁K ρ hρ v⟩ : commutatorImage H V₃ V₁ K) :
          ComponentSection H V₃ V₁ ρ K) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply point_residual_not_normalizes_plane d
  apply le_normalizer_iff_commutator_le_left.mpr
  apply le_trans ?_ d.line_le_plane
  apply commutator_le.mpr
  intro v hv l hl
  have hf := (Submodule.Quotient.mk_eq_zero _).mp (hn ⟨v, hv⟩)
  change seedVector H V₃ V₁ ⟨v, d.plane_le_seed hv⟩ ∈
    fixedSpace ρ (Section08.Source.starImage H K) at hf
  have he := hf ⟨QuotientGroup.mk' (pCore 2 H) ⟨l, hKH (hL₁K hl)⟩,
    ⟨⟨l, hKH (hL₁K hl)⟩, hL₁K hl, rfl⟩⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) ⟨l, hKH (hL₁K hl)⟩)
    (vector H V₃ V₁ ⟨v, le_conjugateSpanBy V₃ H (d.plane_le_seed hv)⟩) = _ at he
  have hvec := vector_commutator ρ hρ
    ⟨v, le_conjugateSpanBy V₃ H (d.plane_le_seed hv)⟩ ⟨l, hKH (hL₁K hl)⟩
  rw [he, sub_self] at hvec
  have hm := (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Section08.Source.UH H V₃)) _).mp hvec
  exact hm

end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
