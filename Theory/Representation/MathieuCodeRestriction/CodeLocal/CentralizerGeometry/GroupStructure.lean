module

public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.GroupStructure.AffineAction
public import Theory.GroupTheory.SylowKernelCore

/-!
# Transporting the affine involution supplement to native M24

The full affine-group identification supplies an actual subgroup of native
M24: the image of the maps preserving each pair parallel to the involution.
It is elementary abelian, normal relative to the full involution centralizer,
and meets the pointwise octad kernel in the marked cyclic subgroup.

The centralizer equality uses the nonidentity kernel element's literal fixed
octad. Faithful-embedding functoriality then transports its intrinsic two-core
and the literal set product. Thus the two outstanding affine-model facts,
order sixteen and the two-core product, suffice to construct the published
OctadInvolutionSupplement record. They remain explicit premises below.

Source: Aschbacher (1994), 39.1; Aschbacher--Smith H.16.2(6) and its proof,
printed pp.402--403. Identification with the code centralizer D is separate.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers.OctadAction
open MathieuCode.CocodeOctad.Dynamics
open scoped Pointwise

namespace MathieuCode.OctadAffine
noncomputable section

/-- The affine group embedded back into native M24 by the proved octad action. -/
def embed (O : Octad) : AffineGroup →* M24 :=
  (octadStabilizer O).subtype.comp (equiv O).symm.toMonoidHom

theorem embed_injective (O : Octad) : Function.Injective (embed O) :=
  (octadStabilizer O).subtype_injective.comp (equiv O).symm.injective

@[simp] theorem embed_action (O : Octad) (g : octadStabilizer O) :
    embed O (action O g) = g.val := by
  exact congrArg Subtype.val ((equiv O).symm_apply_apply g)

/-- The marked vector belonging to a native octad translation. -/
def vector (O : Octad) (a : octadPointwiseKernel O) : Space :=
  (pointwiseCoordinates O a).toAdd

theorem vector_ne_zero (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    vector O a ≠ 0 := by
  intro he
  have ha1 : a = 1 := (pointwiseCoordinates O).injective (by simpa [vector] using he)
  exact ha (congrArg Subtype.val ha1)

@[simp] theorem embed_translation (O : Octad) (a : octadPointwiseKernel O) :
    embed O (translation (vector O a)) = a.val := by
  rw [show translation (vector O a) = action O ⟨a.val, kernel_le_stabilizer O a.property⟩ from
    (action_kernel O a).symm, embed_action]

/-- The actual affine translations map onto the native pointwise octad kernel. -/
theorem translations_map (O : Octad) : translations.map (embed O) = octadPointwiseKernel O := by
  apply le_antisymm
  · rintro _ ⟨f, ⟨v, rfl⟩, rfl⟩
    let a := (pointwiseCoordinates O).symm v
    have hv : vector O a = v.toAdd :=
      congrArg Multiplicative.toAdd ((pointwiseCoordinates O).apply_symm_apply v)
    change embed O (translation v.toAdd) ∈ _
    rw [← hv, embed_translation]
    exact a.property
  · intro a ha
    refine ⟨translation (vector O ⟨a, ha⟩), ?_, embed_translation O ⟨a, ha⟩⟩
    exact ⟨Multiplicative.ofAdd (vector O ⟨a, ha⟩), rfl⟩

/-- The literal affine centralizer maps onto the whole native involution centralizer. -/
theorem centralizer_map (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    (Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup)).map (embed O) =
      Subgroup.centralizer ({a.val} : Set M24) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h := congrArg (embed O) (Subgroup.mem_centralizer_singleton_iff.mp hf)
    simpa only [map_mul, embed_translation] using h
  · intro g hg
    let b : octadStabilizer O := ⟨g, octad_kernel_centralizer_le_stabilizer O a.val a.property ha hg⟩
    refine ⟨action O b, ?_, embed_action O b⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply embed_injective O
    simpa only [map_mul, embed_action, embed_translation] using
      Subgroup.mem_centralizer_singleton_iff.mp hg

/-- The second subgroup is the native image of the concrete pair-preserving affine group. -/
def carrier (O : Octad) (a : octadPointwiseKernel O) : Subgroup M24 :=
  (fiberKernel (vector O a)).map (embed O)

theorem carrier_le_centralizer (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    carrier O a ≤ Subgroup.centralizer ({a.val} : Set M24) := by
  rw [← centralizer_map O a ha]
  exact Subgroup.map_mono (fiberKernel_le_centralizer _)

theorem carrier_normal (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    ((carrier O a).subgroupOf (Subgroup.centralizer ({a.val} : Set M24))).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer (carrier_le_centralizer O a ha)).mpr
  rw [← centralizer_map O a ha]
  exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (fiberKernel_le_centralizer (vector O a))).mp (fiberKernel_normal _))).trans
    ((fiberKernel (vector O a)).le_normalizer_map (embed O))

theorem carrier_elementary (O : Octad) (a : octadPointwiseKernel O) :
    IsElementaryAbelian 2 (carrier O a) := by
  let _ := fiberKernel_elementary (vector O a)
  exact IsElementaryAbelian.map (embed O)

theorem carrier_intersection (O : Octad) (a : octadPointwiseKernel O) :
    octadPointwiseKernel O ⊓ carrier O a = Subgroup.zpowers a.val := by
  calc
    octadPointwiseKernel O ⊓ carrier O a =
        translations.map (embed O) ⊓ (fiberKernel (vector O a)).map (embed O) :=
      congrArg (fun H : Subgroup M24 => H ⊓ carrier O a) (translations_map O).symm
    _ = (translations ⊓ fiberKernel (vector O a)).map (embed O) :=
      (Subgroup.map_inf _ _ _ (embed_injective O)).symm
    _ = Subgroup.zpowers a.val := by
      rw [translations_inf_fiberKernel, MonoidHom.map_zpowers, embed_translation]

/-- Model cardinality transfers through the actual native embedding. -/
theorem carrier_card (O : Octad) (a : octadPointwiseKernel O)
    (hcard : Nat.card (fiberKernel (vector O a)) = 16) : Nat.card (carrier O a) = 16 :=
  (Subgroup.card_map_of_injective (embed_injective O)).trans hcard

/-- The intrinsic affine two-core transports through the full centralizer isomorphism. -/
theorem centralizer_core_map (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1) :
    (((pCore 2 (Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup))).map
      (Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup)).subtype).map
        (embed O)) =
      (pCore 2 (Subgroup.centralizer ({a.val} : Set M24))).map
        (Subgroup.centralizer ({a.val} : Set M24)).subtype := by
  change ((Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup)).pCoreIn 2).map
    (embed O) = (Subgroup.centralizer ({a.val} : Set M24)).pCoreIn 2
  rw [Subgroup.map_pCoreIn_of_injective 2 _ _ (embed_injective O), centralizer_map O a ha]

/-- The literal set product, rather than just its generated subgroup, transports to native M24. -/
theorem carrier_product (O : Octad) (a : octadPointwiseKernel O) (ha : a.val ≠ 1)
    (hproduct : (translations : Set AffineGroup) * (fiberKernel (vector O a) : Set AffineGroup) =
      ((pCore 2 (Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup))).map
        (Subgroup.centralizer ({translation (vector O a)} : Set AffineGroup)).subtype : Set AffineGroup)) :
    (octadPointwiseKernel O : Set M24) * (carrier O a : Set M24) =
      ((pCore 2 (Subgroup.centralizer ({a.val} : Set M24))).map
        (Subgroup.centralizer ({a.val} : Set M24)).subtype : Set M24) := by
  have h := congrArg (fun s : Set AffineGroup => embed O '' s) hproduct
  rw [Set.image_mul, ← Subgroup.coe_map, ← Subgroup.coe_map, ← Subgroup.coe_map,
    translations_map, centralizer_core_map O a ha] at h
  exact h

end
end MathieuCode.OctadAffine

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped Pointwise

namespace MathieuCode
open OctadAffine

/-- Construct the native supplement from the two outstanding affine-model calculations.
All subgroup, normality, elementary and intersection assertions are already unconditional. -/
theorem octadInvolutionSupplement_of_affine
    (hcard : ∀ v : OctadAffine.Space, v ≠ 0 → Nat.card (fiberKernel v) = 16)
    (hproduct : ∀ v : OctadAffine.Space, v ≠ 0 →
      (translations : Set AffineGroup) * (fiberKernel v : Set AffineGroup) =
        ((pCore 2 (Subgroup.centralizer ({translation v} : Set AffineGroup))).map
          (Subgroup.centralizer ({translation v} : Set AffineGroup)).subtype : Set AffineGroup))
    (O : Octad) (z : M24) (hz : z ∈ octadPointwiseKernel O) (hne : z ≠ 1) :
    Nonempty (OctadInvolutionSupplement O z) := by
  let a : octadPointwiseKernel O := ⟨z, hz⟩
  have hv : vector O a ≠ 0 := vector_ne_zero O a hne
  exact ⟨{
    carrier := OctadAffine.carrier O a
    le_centralizer := carrier_le_centralizer O a hne
    normal := carrier_normal O a hne
    elementary := carrier_elementary O a
    card := carrier_card O a (hcard _ hv)
    intersection := carrier_intersection O a
    product := carrier_product O a hne (hproduct _ hv)
  }⟩

end MathieuCode
