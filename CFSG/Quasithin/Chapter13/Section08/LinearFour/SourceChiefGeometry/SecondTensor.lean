module

public import Theory.Representation.BinaryConjugationSection.ShearMovement
public import Theory.Representation.CyclicSeedTensor.SliceMovement
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.OrthogonalSpan

/-!
# Movement from the natural second-tensor row

On V₀/U₀, a shear fixes the V_H-slice and sends its moved copy to the
sum of both copies. This forces movement of the orthogonal span even in
the maximal quotient U_L/N: if the moved image were still in that span,
its shear displacement would vanish modulo the image of U₀. The second
tensor identifies that displacement with the original vector. The
previously computed intersection S ∩ N = V ≤ U₀ gives the contradiction.

The final application discharges the movement premise of the nine-factor
argument from this natural second-tensor marking, using the literal
normalizer, both original actors and the same maximal-quotient action.
It neither assumes movement of that quotient nor imposes a new kernel
condition outside S.

This handles the natural two-dimensional row of 13.8.29(4). The row with
an extra trivial line, construction of the initial and orthogonal markings,
and the surrounding chief strata remain with qt-d-138-linear-four-source.
The genuine 13.8.27 setup is owned by qt-d-138-six-g2-source and final
13.8.1 assembly by qt-d-1381-source. This is not the full source theorem.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.29(4)–30, printed p.964.
-/

public section
open Subgroup Representation
open scoped TensorProduct MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I T Y Z : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup T] [Module (ZMod 2) T] [AddCommGroup Y] [Module (ZMod 2) Y]
  [AddCommGroup Z] [Module (ZMod 2) Z]

/-- The marked natural second tensor moves the literal image of S in U_L/N.
The only kernel information used is its already computed intersection with S. -/
theorem source_natural_second_tensor_movement
    (UH V2 VH S L UL N : Subgroup G)
    (η : Representation (ZMod 2) L Z) (q : BinaryConjugationSection L UL N η)
    (hSU : S ≤ UL) (hSV : S ≤ VH) (hUS : U0 UH V2 ≤ S)
    (hkernel : S ⊓ N ≤ U0 UH V2) (hproper : ¬ S ≤ U0 UH V2)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K T)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ρ : Representation (ZMod 2) (K × I) Y)
    (p : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ρ.comp π))
    (e : (externalTensor σ μ).Equiv ρ)
    (hslice : ∀ w ∈ p.imageSpace VH, ∃ u, e (u ⊗ₜ[ZMod 2] first) = w)
    (a b : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (α β : G2 V2) (hα : π α = (1,a)) (hβ : π β = (1,b))
    (hαL : (α : G) ∈ L) (hβL : (β : G) ∈ L) :
    ∃ w ∈ q.imageSpace S, η ⟨α,hαL⟩ w ∉ q.imageSpace S := by
  have hh := tensor_slice_shear σ μ ρ e first a b hb0
    (by rw [ha, hb1, add_comm]) (p.imageSpace S)
    (fun w hw => hslice w (p.imageSpace_mono hSV hw))
  apply q.image_moved_of_section_shear p S hSU (hSV.trans (VH_le_V0 VH V2))
    hUS hkernel hproper ⟨α,hαL⟩ ⟨β,hβL⟩ α.property β.property
  · simpa only [MonoidHom.comp_apply, hβ] using hh.1
  · simpa only [MonoidHom.comp_apply, hα, hβ] using hh.2

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Representation.Hexacode Atlas.Codes
open scoped TensorProduct
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation.BinaryParabolicExteriorSquare
variable {G K I U W X : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup X] [Module (ZMod 2) X]
  (UH V2 : Subgroup G) (π : G2 V2 →* K × I)
  (ρ : Representation (ZMod 2) (K × I) W)
  (σ : Representation (ZMod 2) K U) (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
  (d : BinaryConjugationSection (G2 V2) (U0 UH V2) V2 (ρ.comp π))
  (f : σ.IntertwiningMap (ρ.comp (MonoidHom.inl K I)))
  (himage : f.range.toSubmodule = d.imageSpace UH)
  (u₀ : U) (hcyclic : Submodule.span (ZMod 2) (Set.range fun k => σ k u₀) = ⊤)
  (t : μ.IntertwiningMap (ρ.comp (MonoidHom.inr K I)))
  (ht : t first = f u₀) (a : I) (ha : μ a first = second)
  (hf : Function.Injective f) (b : I)
  (hb0 : μ b first = first) (hb1 : μ b second = first + second)


include himage hcyclic ht ha hf hb0 hb1 in
/-- Both natural tensor markings and the orthogonal span give the actual nine-factor
lower bound, with no assumed quotient movement. -/
theorem source_nine_factors_of_two_natural_tensors [Finite G] [FiniteDimensional (ZMod 2) U]
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Module Representation.Hexacode.F Z] [IsScalarTower (ZMod 2) F Z]
    (hd : Module.finrank (ZMod 2) U = 3) (hu₀ : u₀ ≠ 0)
    (L J UL N V3 V : Subgroup G)
    (hUL : UL = conjugateSpanBy UH L) (hN : L ≤ normalizer N)
    (hproper : ¬ UL ≤ N) (hJL : J ≤ L)
    (ψ : Representation (ZMod 2) J X) [IsIrreducible ψ]
    (s : BinaryConjugationSection J UH V3 ψ) (hseedDim : Module.finrank (ZMod 2) X = 2)
    (hV3V : V3 ≤ V) (hV2V : V2 ≤ V) (hVS : V ≤ U0 UH V2) (hVN : V ≤ N)
    (htimage : t.range.toSubmodule = d.imageSpace V)
    (β : G2 V2) (hβ : π β = (1,b)) (hβL : (β : G) ∈ L)
    (η : Representation (ZMod 2) L Z) (q : BinaryConjugationSection L UL N η)
    (hSU : U0 UH V2 ≤ UL)
    (D : Subgroup G) (hDL : D ≤ L) (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, η (inclusion hDL x) w = (χ x : F) • w)
    (hDU : D ≤ normalizer UH) (hDS : D ≤ normalizer (U0 UH V2))
    (τ : Representation F HexEvenAutomorphisms Z) [IsIrreducible τ]
    (hz : ∀ w, τ hexEvenZ w = omega • w)
    (d₀ : BinaryConjugationSection D (UL ⊓ D) (N ⊓ D) (η.comp (inclusion hDL)))
    (H VH L1 : Subgroup G) (h1L : L1 ≤ L) (h1H : L1 ≤ H) (hD1 : D ≤ L1)
    (ρ₆ : Representation (ZMod 2) H PlaneSpan.Six)
    (p : BinaryConjugationSection H VH UH ρ₆)
    (π₆ : H →* SL(4, ZMod 2))
    (hact : ∀ h x, ρ₆ h x = exteriorMap (π₆ h).val x)
    (hUV : U0 UH V2 ≤ VH)
    (hfirst : p.imageSpace (U0 UH V2) = PlaneSpan.firstSpace)
    (hpoint : p.imageSpace V = PlaneSpan.pointSpace)
    (hblock : ∀ k : L1, (π₆ (inclusion h1H k)).val 2 0 = 0 ∧
      (π₆ (inclusion h1H k)).val 2 1 = 0 ∧
      (π₆ (inclusion h1H k)).val 3 0 = 0 ∧
      (π₆ (inclusion h1H k)).val 3 1 = 0)
    (a₆ b₆ : L1)
    (ha₆ : (π₆ (inclusion h1H a₆)).val = Matrix.transvection 1 0 1)
    (hb₆ : (π₆ (inclusion h1H b₆)).val = Matrix.transvection 0 1 1)
    {K₂ I₂ T₂ Y₂ : Type*} [Group K₂] [Group I₂]
    [AddCommGroup T₂] [Module (ZMod 2) T₂] [AddCommGroup Y₂] [Module (ZMod 2) Y₂]
    (π₂ : G2 V2 →* K₂ × I₂) (σ₂ : Representation (ZMod 2) K₂ T₂)
    (μ₂ : Representation (ZMod 2) I₂ (Fin 2 → ZMod 2))
    (ξ₂ : Representation (ZMod 2) (K₂ × I₂) Y₂)
    (p₂ : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ξ₂.comp π₂))
    (e₂ : (externalTensor σ₂ μ₂).Equiv ξ₂)
    (hslice : ∀ w ∈ p₂.imageSpace VH, ∃ u, e₂ (u ⊗ₜ[ZMod 2] first) = w)
    (a₂ b₂ : I₂) (ha₂ : μ₂ a₂ first = second)
    (hb₂0 : μ₂ b₂ first = first) (hb₂1 : μ₂ b₂ second = first + second)
    (α₂ β₂ : G2 V2) (hα₂ : π₂ α₂ = (1,a₂)) (hβ₂ : π₂ β₂ = (1,b₂))
    (hα₂L : (α₂ : G) ∈ L) (hβ₂L : (β₂ : G) ∈ L)
    (κ : L →* HexEvenAutomorphisms)
    (hcompatible : ∀ l w, η l w = τ (κ l) w)
    (chief : NoncentralChiefRefinement.ChiefSeries D)
    (hc0 : chief.head = ⊥) (hc1 : chief.last = ⊤) :
    9 ≤ chief.noncentralTwoCount := by
  let S := conjugateSpanBy (U0 UH V2) L1
  have hSV : S ≤ VH := conjugateSpanBy_le hUV (h1H.trans p.normalized)
  have hspanUL : S ≤ UL := conjugateSpanBy_le hSU (h1L.trans q.normalized)
  have hkernel := (source_maximal_tensor_kernels UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 L J UL N V3 V hUL hN hproper hJL
    ψ s hV3V hV2V hVS hVN htimage β hβ hβL).2
  have hSN := source_orthogonal_span_kernel H VH UH V2 L1 ρ₆ p π₆
    hact h1H hUV hfirst hblock a₆ ha₆ N V hkernel hVN hpoint b₆ hb₆
    (hN (h1L b₆.property))
  have hSP := source_orthogonal_span_image H VH UH V2 L1 ρ₆ p π₆
    hact h1H hUV hfirst hblock a₆ ha₆
  have hstrict : ¬ S ≤ U0 UH V2 := by
    intro hh
    have hle := p.imageSpace_mono hh
    change p.imageSpace (conjugateSpanBy (U0 UH V2) L1) ≤ p.imageSpace (U0 UH V2) at hle
    rw [hSP, hfirst] at hle
    have hd' := Submodule.finrank_mono hle
    rw [PlaneSpan.planeSpace_finrank, PlaneSpan.firstSpace_finrank] at hd'
    omega
  obtain ⟨w, hw, hm⟩ := source_natural_second_tensor_movement UH V2 VH S L UL N
    η q hspanUL hSV (le_conjugateSpanBy _ _) (by rw [hSN]; exact hVS) hstrict
    π₂ σ₂ μ₂ ξ₂ p₂ e₂ hslice a₂ b₂ ha₂ hb₂0 hb₂1 α₂ β₂ hα₂ hβ₂ hα₂L hβ₂L
  have hmoved : ∃ g w,
      w ∈ q.scalarImage D hDL χ hχ hscalar S
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)) ∧
      τ g w ∉ q.scalarImage D hDL χ hχ hscalar S
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)) := by
    refine ⟨κ ⟨α₂,hα₂L⟩,w,hw,?_⟩
    change τ (κ ⟨α₂,hα₂L⟩) w ∉ q.imageSpace S
    rwa [← hcompatible]
  exact source_nine_factors_of_tensor_orthogonal_span UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ L J UL N V3 V hUL hN hproper hJL
    ψ s hseedDim hV3V hV2V hVS hVN htimage β hβ hβL η q hSU D hDL χ hχ hscalar
    hDU hDS τ hz d₀ H VH L1 h1L h1H hD1 ρ₆ p π₆ hact hUV hfirst hpoint hblock
    a₆ b₆ ha₆ hb₆ hmoved chief hc0 hc1

end CFSG.Quasithin.Chapter13.Section08.LinearFour
