module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.PlaneImage
public import Theory.GroupAction.FourPointResidual
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
/-!
# The original K0 and the quotient-point stabilizer

The original line has order two, so every H-element centralizes it. A
four-group normalizer fixing that line has the same two-residual as its
centralizer. The original quotient point has precisely V2 as its preimage;
its model stabilizer therefore pulls back to N_K(V2). Residual functoriality
identifies the model residual with the actual image of K0=O²(C_K(V2)).

Source: Aschbacher–Smith, 13.7.6(iii), printed p.939, and the C3 construction
on p.940. No point-centralizer or residual identification is assumed.
-/
@[expose] public section
open Subgroup Representation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion NaturalAction
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open BinaryNaturalDual.VectorStabilizers
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- On the original source plane, normalizing and centralizing have the same two-residual. -/
theorem plane_normalizer_residual_eq_centralizer
    (hHN : H ≤ normalizer (V₁ : Set G)) (hKH : K ≤ H) :
    residual (K ⊓ normalizer (V₂ : Set G)) = residual (K ⊓ centralizer (V₂ : Set G)) := by
  let := elementary d
  let : IsElementaryAbelian 2 V₂ := IsElementaryAbelian.of_injective
    (inclusion (d.plane_le_seed.trans d.seed_le)) (inclusion_injective _)
  exact four_point_normalizer_residual_eq K V₂ V₁ d.plane_card d.line_card d.line_le_plane
    (hKH.trans (hHN.trans (normalizer_le_centralizer_of_card_two V₁ d.line_card)))

variable [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
private theorem vector_mem_plane_iff (w : Section08.Source.UH H V₃) :
    vector H V₃ V₁ w ∈ sectionImage H V₃ V₁ V₂ ↔ (w : G) ∈ V₂ := by
  constructor
  · rintro ⟨v,hv,he⟩
    let q := QuotientGroup.mk' (V₁.subgroupOf (Section08.Source.UH H V₃))
    have hq : q v = q w := he
    have hk : v⁻¹ * w ∈ V₁.subgroupOf (Section08.Source.UH H V₃) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (v⁻¹ * w) = 1
      rw [map_mul,map_inv,hq,inv_mul_cancel]
    have hm := V₂.mul_mem hv (d.line_le_plane hk)
    change (v : G) * ((v : G)⁻¹ * (w : G)) ∈ V₂ at hm
    simpa only [mul_inv_cancel_left] using hm
  · exact fun hw => ⟨w,hw,rfl⟩

/-- The model point stabilizer pulls back to the normalizer of the original plane. -/
theorem point_stabilizer_preimage_eq_plane_normalizer
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v))
    (u : Additive (Section08.Source.Utilde H V₃ V₁))
    (hu : u ∈ sectionImage H V₃ V₁ V₂) (hu0 : u ≠ 0) :
    ((representationStabilizer σ (eV u)).comap
      (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))).map K.subtype =
      K ⊓ normalizer (V₂ : Set G) := by
  have hspan : sectionImage H V₃ V₁ V₂ = Submodule.span (ZMod 2) {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (plane_section_finrank d) hu hu0
  let P := (representationStabilizer σ (eV u)).comap
    (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
  have hnormal : P.map K.subtype ≤ normalizer (V₂ : Set G) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨k,hk,rfl⟩ x hx
    have hku : ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u = u :=
      eV.injective ((he k u).trans hk)
    let w : Section08.Source.UH H V₃ := ⟨x,le_conjugateSpanBy V₃ H (d.plane_le_seed hx)⟩
    have hw := (vector_mem_plane_iff d w).mpr hx
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hw)
    have hfv : ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) (vector H V₃ V₁ w) = vector H V₃ V₁ w := by
      rw [←ha,map_smul,hku]
    have hmem : ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) (vector H V₃ V₁ w) ∈ sectionImage H V₃ V₁ V₂ := by rw [hfv]; exact hw
    rw [hρ] at hmem
    exact (vector_mem_plane_iff d _).mp hmem
  have hfix (k : K) (hk : (k : G) ∈ normalizer (V₂ : Set G)) :
      ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u = u := by
    have hm := sectionImage_invariant ρ hρ V₂ (inclusion hKH k) hk u hu
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hm)
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
    · have hz : ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) u = 0 := by simpa using ha.symm
      exact (hu0 ((ρ.apply_bijective _).1 (hz.trans (map_zero _).symm))).elim
    · simpa using ha.symm
  apply le_antisymm (le_inf (map_subtype_le P) hnormal)
  rintro x ⟨hxK,hxN⟩
  refine ⟨⟨x,hxK⟩,?_,rfl⟩
  change σ (eK (QuotientGroup.mk' (pCore 2 K) ⟨x,hxK⟩)) (eV u) = eV u
  rw [←he, hfix ⟨x,hxK⟩ hxN]
/-- The actual K0 has precisely the model point-stabilizer residual as quotient image. -/
theorem plane_centralizer_residual_model_image
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    (hHN : H ≤ normalizer (V₁ : Set G)) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (σ : Representation (ZMod 2) A E) (eK : (K ⧸ pCore 2 K) ≃* A)
    (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] E)
    (he : ∀ k : K, ∀ v,
      eV (ρ (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) v) =
        σ (eK (QuotientGroup.mk' (pCore 2 K) k)) (eV v))
    (u : Additive (Section08.Source.Utilde H V₃ V₁))
    (hu : u ∈ sectionImage H V₃ V₁ V₂) (hu0 : u ≠ 0) :
    ((residual (K ⊓ centralizer (V₂ : Set G))).subgroupOf K).map
      (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) =
        residual (representationStabilizer σ (eV u)) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let S := representationStabilizer σ (eV u)
  let P := S.comap q
  have hP : P.map K.subtype = K ⊓ normalizer (V₂ : Set G) :=
    point_stabilizer_preimage_eq_plane_normalizer d hKH ρ hρ σ eK eV he u hu hu0
  have hRmap : (residual P).map K.subtype = residual (K ⊓ normalizer (V₂ : Set G)) := by
    change ((pResidual 2 P).map P.subtype).map K.subtype = _
    rw [map_embedded_pResidual,hP]
    rfl
  have hR : (residual (K ⊓ centralizer (V₂ : Set G))).subgroupOf K = residual P := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le ((residual_le _).trans inf_le_left),hRmap,
      plane_normalizer_residual_eq_centralizer d hHN hKH]
  rw [hR]
  change ((pResidual 2 P).map P.subtype).map q = residual S
  rw [map_embedded_pResidual]
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have heq : P.map q = S := map_comap_eq_self_of_surjective hq S
  rw [heq]
  rfl
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
