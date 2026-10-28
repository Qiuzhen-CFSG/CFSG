module
public import Theory.Representation.BinaryConjugationSection.NormShearMovement
public import Theory.Representation.CyclicSeedTensor.NormSliceMovement
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.ResidualSpan

/-!
# The extra trivial line in the second tensor

For the second tensor (natural plane plus trivial line) ⊗ dual three-space,
the ordinary shear recovers only the natural component of a marked slice.
The norm of the common cubic recovers the missing trivial component. That
same cubic acts as the nontrivial four-element-field scalar on U_L/N, so
its norm vanishes there. Comparing the two literal sections proves that
the orthogonal span is moved in U_L/N. The residual-cubic span calculation
then forces nine actual noncentral two-chief factors of L₀.

The argument assumes an element of the scalar subgroup has a pure
second-factor cubic image. `SourceCommonCubic` proves that this placement
cannot hold on the source's common product quotient: centralization of V
forces its second coordinate to be one. Thus this conditional algebraic
API does not discharge the source extra-line branch. A compatible movement
argument remains to be constructed. No extra kernel containment, assumed
quotient movement, or assumed chief count is used here. The marked tensor,
exterior action and earlier setup remain explicit. Constructing these markings,
the surrounding strata and critical geometry stays with
qt-d-138-linear-four-source; qt-d-138-six-g2-source supplies 13.8.27 and
qt-d-1381-source owns final assembly. This is not full Theorem 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.29(4)–30, printed p.964. The
corrected span quotient has denominator the image of U_H, not U_L.
-/

public section
open Subgroup Representation
open scoped TensorProduct MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
open Representation.Hexacode Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
variable {G K I T Y Z : Type*} [Group G] [Group K] [Group I]
  [AddCommGroup T] [Module (ZMod 2) T] [AddCommGroup Y] [Module (ZMod 2) Y]
  [AddCommGroup Z] [Module (ZMod 2) Z] [Module F Z]

/-- The extra trivial line is removed by the norm of the same cubic that
acts as the nontrivial field scalar on the original maximal quotient. -/
theorem source_extra_line_second_tensor_movement
    (UH V2 VH S L UL N : Subgroup G)
    (η : Representation (ZMod 2) L Z) (q : BinaryConjugationSection L UL N η)
    (hSU : S ≤ UL) (hSV : S ≤ VH) (hUS : U0 UH V2 ≤ S)
    (hkernel : S ⊓ N ≤ U0 UH V2) (hproper : ¬ S ≤ U0 UH V2)
    (π : G2 V2 →* K × I) (σ : Representation (ZMod 2) K T)
    (μ : Representation (ZMod 2) I (Fin 2 → ZMod 2))
    (ρ : Representation (ZMod 2) (K × I) Y)
    (p : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ρ.comp π))
    (e : (externalTensor σ (μ.prod (Representation.trivial (ZMod 2) I (ZMod 2)))).Equiv ρ)
    (ε : ZMod 2)
    (hslice : ∀ w ∈ p.imageSpace VH, ∃ u, e (u ⊗ₜ[ZMod 2] (first, ε)) = w)
    (a b c : I) (ha : μ a first = second)
    (hb0 : μ b first = first) (hb1 : μ b second = first + second)
    (hc0 : μ c first = second) (hc1 : μ c second = first + second)
    (α β γ : G2 V2) (hα : π α = (1,a)) (hβ : π β = (1,b)) (hγ : π γ = (1,c))
    (hαL : (α : G) ∈ L) (hβL : (β : G) ∈ L) (hγL : (γ : G) ∈ L)
    (hscalar : ∀ w, η ⟨γ,hγL⟩ w = omega • w) :
    ∃ w ∈ q.imageSpace S, η ⟨α,hαL⟩ w ∉ q.imageSpace S := by
  have hv := natural_trivial_shear_mod_norm μ a b c ha hb0 hb1 hc0 hc1 ε
  have hh := tensor_slice_shear_mod_norm σ
    (μ.prod (Representation.trivial (ZMod 2) I (ZMod 2))) ρ e
    (first, ε) a b c hv.1 hv.2 (p.imageSpace S)
    (fun w hw => hslice w (p.imageSpace_mono hSV hw))
  apply q.image_moved_of_section_shear_mod_norm p S hSU
    (hSV.trans (VH_le_V0 VH V2)) hUS hkernel hproper
    ⟨α,hαL⟩ ⟨β,hβL⟩ ⟨γ,hγL⟩ α.property β.property γ.property
  · intro w
    simp only [hscalar, smul_smul]
    have hω : omega * omega + omega + 1 = 0 := by decide
    calc
      (omega * omega) • w + omega • w + w =
          (omega * omega + omega + 1) • w := by rw [add_smul, add_smul, one_smul]
      _ = 0 := by rw [hω, zero_smul]
  · simpa only [MonoidHom.comp_apply, hβ] using hh.1
  · simpa only [MonoidHom.comp_apply, hα, hβ, hγ] using hh.2

end CFSG.Quasithin.Chapter13.Section08.LinearFour

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
/-- The second-tensor row with an extra trivial line also forces nine actual
noncentral chief factors. The common cubic belongs to the original scalar
subgroup D, and all quotient and conjugation maps are retained. -/
theorem source_nine_factors_of_extra_line_tensor [Finite G] [FiniteDimensional (ZMod 2) U]
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
    (η : Representation (ZMod 2) L Z) [IsIrreducible η]
    (q : BinaryConjugationSection L UL N η)
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
    (hblock : ∀ k : L1, (π₆ (inclusion h1H k)).val 2 0 = 0 ∧
      (π₆ (inclusion h1H k)).val 2 1 = 0 ∧
      (π₆ (inclusion h1H k)).val 3 0 = 0 ∧
      (π₆ (inclusion h1H k)).val 3 1 = 0)
    (P : Subgroup G) (hPH : P ≤ H)
    (hL1 : L1 = (pResidual 2 P).map P.subtype)
    (aP : P) (haP : (π₆ (inclusion hPH aP)).val = PlaneSpan.planeCubic)
    (hgen : L1.subgroupOf L ⊔ (G2 V2).subgroupOf L = ⊤)
    {K₂ I₂ T₂ Y₂ : Type*} [Group K₂] [Group I₂]
    [AddCommGroup T₂] [Module (ZMod 2) T₂] [AddCommGroup Y₂] [Module (ZMod 2) Y₂]
    (π₂ : G2 V2 →* K₂ × I₂) (σ₂ : Representation (ZMod 2) K₂ T₂)
    (μ₂ : Representation (ZMod 2) I₂ (Fin 2 → ZMod 2))
    (ξ₂ : Representation (ZMod 2) (K₂ × I₂) Y₂)
    (p₂ : BinaryConjugationSection (G2 V2) (V0 VH V2) (U0 UH V2) (ξ₂.comp π₂))
    (e₂ : (externalTensor σ₂
      (μ₂.prod (Representation.trivial (ZMod 2) I₂ (ZMod 2)))).Equiv ξ₂)
    (ε : ZMod 2)
    (hslice : ∀ w ∈ p₂.imageSpace VH, ∃ u, e₂ (u ⊗ₜ[ZMod 2] (first, ε)) = w)
    (a₂ b₂ c₂ : I₂) (ha₂ : μ₂ a₂ first = second)
    (hb₂0 : μ₂ b₂ first = first) (hb₂1 : μ₂ b₂ second = first + second)
    (hc₂0 : μ₂ c₂ first = second) (hc₂1 : μ₂ c₂ second = first + second)
    (γD : D) (hγG2 : (γD : G) ∈ G2 V2)
    (hγπ : π₂ ⟨γD,hγG2⟩ = (1,c₂)) (hγχ : (χ γD : F) = omega)
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
  let : Finite Z := Finite.of_surjective (fun x : UL => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  obtain ⟨a₆,ha₆⟩ := source_plane_cubic_in_residual H P L1 hPH h1H hL1 π₆ aP haP
  have hindex := source_tensor_seed_index UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ V hV2V hVS htimage
  have hindexS := source_cubic_span_index H VH UH V2 L1 ρ₆ p π₆
    hact h1H hUV hfirst hblock a₆ ha₆ V hVS hindex
  have hfields := source_maximal_tensor_field_dimensions UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ L J UL N V3 V hUL hN hproper hJL
    ψ s hseedDim hV3V hV2V hVS hVN htimage β hβ hβL η q hSU D hDL χ hχ hscalar hDU hDS
  obtain ⟨hd3,hSN⟩ := source_span_dimension_and_kernel L UL N UH V2 L1 V D η q
    h1L hgen hSU hVS hVN hindexS hDL hD1 χ hχ hscalar hDS hfields.2 τ hz
  have hSP := source_cubic_span_image H VH UH V2 L1 ρ₆ p π₆
    hact h1H hUV hfirst hblock a₆ ha₆
  have hstrict : ¬ S ≤ U0 UH V2 := by
    intro hh
    have hle := p.imageSpace_mono hh
    change p.imageSpace (conjugateSpanBy (U0 UH V2) L1) ≤ p.imageSpace (U0 UH V2) at hle
    rw [hSP, hfirst] at hle
    have hd' := Submodule.finrank_mono hle
    rw [PlaneSpan.planeSpace_finrank, PlaneSpan.firstSpace_finrank] at hd'
    omega
  obtain ⟨w, hw, hm⟩ := source_extra_line_second_tensor_movement UH V2 VH S L UL N
    η q hspanUL hSV (le_conjugateSpanBy _ _) (by rw [hSN]; exact hVS) hstrict
    π₂ σ₂ μ₂ ξ₂ p₂ e₂ ε hslice a₂ b₂ c₂ ha₂ hb₂0 hb₂1 hc₂0 hc₂1
    α₂ β₂ ⟨γD,hγG2⟩ hα₂ hβ₂ hγπ hα₂L hβ₂L (hDL γD.property)
    (fun w => (hscalar γD w).trans (by rw [hγχ]))
  have hmoved : ∃ g w,
      w ∈ q.scalarImage D hDL χ hχ hscalar S
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)) ∧
      τ g w ∉ q.scalarImage D hDL χ hχ hscalar S
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)) := by
    refine ⟨κ ⟨α₂,hα₂L⟩,w,hw,?_⟩
    change τ (κ ⟨α₂,hα₂L⟩) w ∉ q.imageSpace S
    rwa [← hcompatible]
  let S3 := q.scalarImage D hDL χ hχ hscalar S
    (hD1.trans (le_normalizer_conjugateSpanBy _ _))
  let C := q.scalarImage D hDL χ hχ hscalar UH hDU
  have hCS : C ≤ S3 := q.imageSpace_mono ((UH_le_U0 UH V2).trans (le_conjugateSpanBy _ _))
  have hdC : Module.finrank F (C.comap S3.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hCS).finrank_eq.trans hfields.1
  have hquotient : Module.finrank F (S3 ⧸ C.comap S3.subtype) = 2 := by
    have hh := (C.comap S3.subtype).finrank_quotient_add_finrank
    change Module.finrank F S3 = 3 at hd3
    omega
  exact source_nine_factors_of_maximal_tensor UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ L J UL N V3 V hUL hN hproper hJL
    ψ s hseedDim hV3V hV2V hVS hVN htimage β hβ hβL η q hSU D hDL χ hχ hscalar
    hDU hDS τ hz d₀ S3 hCS hquotient hmoved chief hc0 hc1

end CFSG.Quasithin.Chapter13.Section08.LinearFour
