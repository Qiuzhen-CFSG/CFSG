module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.Constructions
public import Theory.Representation.CyclicSeedTensor
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.Generation
public import Theory.Representation.BinaryConjugationSection.Relabel
public import Theory.Representation.BinaryConjugationSection.ImageDimensions

/-!
# Constructing the first tensor from the original seed

The original natural sections U_H/V₂ and V/V₂ share the seed V₃/V₂.
Their compatible embeddings, the cyclic K₂-orbit of the seed, and the
commuting quotient actions construct the external tensor on U₀/V₂.
Surjectivity follows from U₀ = ⟨U_H^{G₂}⟩; no tensor decomposition,
independence of the two copies, or quotient dimension is assumed.

The relabelled section retains the coordinate homomorphism and literal
kernel V₂. The same g gives U₀ = U_H U_H^g and U_H ∩ U_H^g = V₂;
source conjugation is inverse conjugation, so its linear actor is π(g⁻¹).
When U_H/V₂ has dimension three, the tensor has dimension six. Marking
the actual V/V₂ by the seed plane gives |U₀:V| = 16, the raw section
used for the field-dimension-two calculation in 13.8.30.

The initial quotient action through the two factors and the two compatible
seed embeddings remain explicit. Constructing them from the earlier local
setup, the intersection V_H ∩ V_H^g, the orthogonal V_H/U_H module, and
the second tensor remain obligations of qt-d-138-linear-four-source.
These results do not assert completion of 13.8.29 or 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.29(3) and 13.8.30, printed p.964.
-/

@[expose] public noncomputable section
open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
open scoped TensorProduct
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour

variable {G K I U W : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  (UH V2 : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (himage : f.range.toSubmodule = d.imageSpace UH)
  (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (a : I) (ha : μ a first = second)

include himage hcyclic ht ha in
/-- Conjugate generation supplies surjectivity of the constructed tensor map. -/
theorem source_tensor_map_surjective : Function.Surjective (tensorMap ρ σ f a) := by
  let F : Representation.IntertwiningMap ((externalTensor σ μ).comp π) (ρ.comp π) :=
    ⟨tensorMap ρ σ f a, fun g => tensorMap_intertwines ρ σ μ f a u₀ hcyclic t ht ha (π g)⟩
  have htop : F.range.toSubmodule = ⊤ := by
    apply d.generated_image_le UH rfl F.range
    rw [← himage]
    rintro w ⟨u,rfl⟩
    refine ⟨u ⊗ₜ[ZMod 2] first, ?_⟩
    exact (tensorMap_tmul ρ σ f a u first).trans (by simp [first])
  exact LinearMap.range_eq_top.mp htop

variable (hf : Function.Injective f) (b : I)
  (hb0 : μ b first = first) (hb1 : μ b second = first + second)

/-- The external tensor isomorphism with the original factor actions. -/
def source_tensor_coordinates : (externalTensor σ μ).Equiv ρ :=
  .mk (LinearEquiv.ofBijective (tensorMap ρ σ f a)
    ⟨tensorMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1,
      source_tensor_map_surjective UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha⟩)
    (tensorMap_intertwines ρ σ μ f a u₀ hcyclic t ht ha)

theorem source_tensor_coordinates_tmul (u : U) (v : Fin 2 → ZMod 2) :
    source_tensor_coordinates UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
      (u ⊗ₜ[ZMod 2] v) = v 0 • f u + v 1 • ρ (1,a) (f u) :=
  tensorMap_tmul ρ σ f a u v

/-- Tensor coordinates on the same literal numerator and kernel. -/
def source_tensor_section :
    BinaryConjugationSection (G2 V2) (U0 UH V2) V2 ((externalTensor σ μ).comp π) :=
  d.relabel π
    (source_tensor_coordinates UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1).symm

theorem source_tensor_section_coordinates (x : U0 UH V2) :
    (source_tensor_section UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1).coordinates x =
      Multiplicative.ofAdd
        ((source_tensor_coordinates UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1).symm
          (d.coordinates x).toAdd) := rfl

include himage hcyclic ht ha hf hb0 hb1 in
/-- The specified conjugator produces the two generating copies with exact intersection. -/
theorem source_tensor_two_conjugates (g : G2 V2) (hg : π g⁻¹ = (1,a))
    (hV2U : V2 ≤ UH) :
    U0 UH V2 = UH ⊔ UH.conjBy ((g : G)⁻¹) ∧
      UH ⊓ UH.conjBy ((g : G)⁻¹) = V2 := by
  let E := source_tensor_coordinates UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
  let C := UH.conjBy ((g : G)⁻¹)
  have hUS : UH ≤ U0 UH V2 := UH_le_U0 UH V2
  have hCS : C ≤ U0 UH V2 := by
    rintro x ⟨u,hu,rfl⟩
    exact (mem_normalizer_iff.mp (d.normalized g⁻¹.property) u).mp (hUS hu)
  have hCimage : d.imageSpace C = (d.imageSpace UH).map (ρ (1,a)) := by
    have he := d.imageSpace_conjBy UH hUS g⁻¹
    change d.imageSpace C = (d.imageSpace UH).map (ρ (π g⁻¹)) at he
    rwa [hg] at he
  have honto : Function.Surjective (coordinateMap ρ σ f a) := by
    intro w
    obtain ⟨z,hz⟩ := E.surjective w
    exact ⟨TensorProduct.piScalarRight (ZMod 2) (ZMod 2) U (Fin 2) z, hz⟩
  have hjoin : d.imageSpace (UH ⊔ C) = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨x,rfl⟩ := honto w
    apply (d.imageSpace (UH ⊔ C)).add_mem
    · apply d.imageSpace_mono le_sup_left
      rw [← himage]
      exact ⟨x 0,rfl⟩
    · apply d.imageSpace_mono le_sup_right
      rw [hCimage]
      refine ⟨f (x 1), ?_, rfl⟩
      rw [← himage]
      exact ⟨x 1,rfl⟩
  have hsum : U0 UH V2 = UH ⊔ C := by
    apply le_antisymm ?_ (sup_le hUS hCS)
    have he := d.le_sup_kernel_of_image_top (UH ⊔ C) hjoin
    exact he.trans (sup_le le_rfl (hV2U.trans le_sup_left))
  refine ⟨hsum, le_antisymm ?_ ?_⟩
  · intro x hx
    let xS : U0 UH V2 := ⟨x,hUS hx.1⟩
    let w := (d.coordinates xS).toAdd
    have hwU : w ∈ d.imageSpace UH := (d.mem_imageSpace_iff UH w).mpr ⟨xS,hx.1,rfl⟩
    have hwC : w ∈ d.imageSpace C := (d.mem_imageSpace_iff C w).mpr ⟨xS,hx.2,rfl⟩
    rw [← himage] at hwU
    obtain ⟨u,hu⟩ := hwU
    rw [hCimage, ← himage] at hwC
    obtain ⟨v,⟨v',hv⟩,he⟩ := hwC
    have heq : coordinateMap ρ σ f a ![u,0] = coordinateMap ρ σ f a ![0,v'] := by
      simp only [coordinateMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_zero, add_zero, zero_add]
      exact hu.trans (he.symm.trans (congrArg (ρ (1,a)) hv.symm))
    have hpair := coordinateMap_injective ρ σ μ f a u₀ hcyclic t ht ha hf b hb0 hb1 heq
    have hu0 : u = 0 := congrFun hpair 0
    have hw0 : w = 0 := by rw [← hu, hu0, map_zero]
    exact (d.coordinates_eq_one_iff xS).mp hw0
  · intro x hx
    refine ⟨hV2U hx, ?_⟩
    have hmem : (g : G) * x * (g : G)⁻¹ ∈ V2 :=
      (mem_normalizer_iff.mp g.property x).mp hx
    refine ⟨(g : G) * x * (g : G)⁻¹, hV2U hmem, ?_⟩
    change (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * ((g : G)⁻¹)⁻¹ = x
    simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

include himage hcyclic ht ha hf hb0 hb1 in
/-- Every element is a product in the source order, with inverse conjugation. -/
theorem source_tensor_product (g : G2 V2) (hg : π g⁻¹ = (1,a))
    (hV2U : V2 ≤ UH) (x : G) (hx : x ∈ U0 UH V2) :
    ∃ u ∈ UH, ∃ v ∈ UH, x = u * ((g : G)⁻¹ * v * (g : G)) := by
  have hs := (source_tensor_two_conjugates UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 g hg hV2U).1
  let C := UH.conjBy ((g : G)⁻¹)
  have hUS : UH ≤ U0 UH V2 := UH_le_U0 UH V2
  have hCS : C ≤ U0 UH V2 := le_sup_right.trans hs.ge
  let B := UH.subgroupOf (U0 UH V2)
  let D := C.subgroupOf (U0 UH V2)
  have hk : d.coordinates.ker ≤ B := by
    rw [d.kernel_eq]
    exact comap_mono hV2U
  let : B.Normal := by
    rw [← comap_map_eq_self hk]
    infer_instance
  have hsup : B ⊔ D = ⊤ := by
    rw [← subgroupOf_sup hUS hCS]
    exact (congrArg (fun A => A.subgroupOf (U0 UH V2)) hs).symm.trans
      (subgroupOf_self _)
  obtain ⟨u,hu,c,hc,he⟩ := mem_sup_of_normal_left.mp
    (show (⟨x,hx⟩ : U0 UH V2) ∈ B ⊔ D by rw [hsup]; trivial)
  obtain ⟨v,hv,hvc⟩ := hc
  refine ⟨u,hu,v,hv, ?_⟩
  have he' : (u : G) * c = x := congrArg Subtype.val he
  have hvc' : (g : G)⁻¹ * v * (g : G) = c := by
    change (g : G)⁻¹ * v * ((g : G)⁻¹)⁻¹ = c at hvc
    simpa only [inv_inv] using hvc
  rw [hvc', he']

include himage hcyclic ht ha hf hb0 hb1 in
/-- The original three-dimensional factor gives the six-dimensional quotient. -/
theorem source_tensor_dimension [FiniteDimensional (ZMod 2) U]
    (hd : Module.finrank (ZMod 2) U = 3) : Module.finrank (ZMod 2) W = 6 := by
  have he := (source_tensor_coordinates UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1).toLinearEquiv.finrank_eq
  rw [Module.finrank_tensorProduct, hd, Module.finrank_pi] at he
  simpa using he.symm

include himage hcyclic ht ha hf hb0 hb1 in
/-- The actual seed-plane image removes two binary dimensions from the tensor quotient. -/
theorem source_tensor_seed_index [Finite G] [FiniteDimensional (ZMod 2) U]
    (hd : Module.finrank (ZMod 2) U = 3) (hu₀ : u₀ ≠ 0)
    (V : Subgroup G) (hV2V : V2 ≤ V) (hVS : V ≤ U0 UH V2)
    (htimage : t.range.toSubmodule = d.imageSpace V) :
    V.relIndex (U0 UH V2) = 16 := by
  let : Finite W := Finite.of_surjective (fun x : U0 UH V2 => (d.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp d.onto)
  have hc : Nat.card W = 64 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      source_tensor_dimension UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1 hd]
    decide
  have htcard : Nat.card t.range.toSubmodule = 4 := by
    let e := LinearEquiv.ofInjective t.toLinearMap
      (seed_injective ρ σ μ f a u₀ hcyclic t ht ha hf hu₀ b hb0 hb1)
    calc Nat.card t.range.toSubmodule = Nat.card (Fin 2 → ZMod 2) :=
           (Nat.card_congr e.toEquiv).symm
         _ = 4 := by simp
  have hUcard : V2.relIndex (U0 UH V2) = 64 := by
    let := d.kernel_normal
    exact (Nat.card_congr d.quotientEquiv.toEquiv).trans hc
  have hVcard := d.imageSpace_card_eq_relIndex V hVS
  rw [← htimage, htcard] at hVcard
  have he := relIndex_mul_relIndex V2 V (U0 UH V2) hV2V hVS
  rw [← hVcard, hUcard] at he
  omega

end CFSG.Quasithin.Chapter13.Section08.LinearFour
