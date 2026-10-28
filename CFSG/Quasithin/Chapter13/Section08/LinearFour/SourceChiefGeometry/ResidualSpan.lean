module

public import Theory.Representation.BinaryParabolicExteriorSquare.CubicSpan
public import Theory.Representation.BinaryConjugationSection.GeneratedImages
public import Theory.Representation.BinaryConjugationSection.DisplacementBound
public import Theory.GroupTheory.PResidual.FiniteImage
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.SecondTensor

/-!
# The orthogonal span using a residual cubic and generation

The point-plane parabolic's two-residual contains its odd-order plane
rotation. This actor generates the exterior five-space from the original
three-space. In the maximal quotient, equality of the two corresponding
images would make the tensor plane invariant under both generators of L.
Irreducibility and the faithful degrees three or nine exclude that equality.
The index bound forces field dimension three, and equality in that bound
recovers the exact kernel V. No Levi involutions in L₁ are needed.

These results retain the original section maps and the initial module
markings. The final application is the natural second-tensor branch of
13.8.30. The remaining source markings and extra-trivial-line row are owned
by qt-d-138-linear-four-source; qt-d-1381-source owns final assembly.
Source: Aschbacher–Smith, 13.8.29–30, printed p.964.
-/

public section
open Subgroup Representation
open Atlas.Order20160A8.Bivectors (exteriorMap)
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation.BinaryParabolicExteriorSquare.PlaneSpan

variable {G : Type*} [Group G] (H VH UH V2 L1 : Subgroup G)
  (ρ : Representation (ZMod 2) H Six)
  (p : BinaryConjugationSection H VH UH ρ)
  (π : H →* SL(4, ZMod 2))
  (hact : ∀ h x, ρ h x = exteriorMap (π h).val x)
  (hLH : L1 ≤ H) (hUV : U0 UH V2 ≤ VH)
  (hfirst : p.imageSpace (U0 UH V2) = firstSpace)
  (hblock : ∀ a : L1, (π (inclusion hLH a)).val 2 0 = 0 ∧
    (π (inclusion hLH a)).val 2 1 = 0 ∧
    (π (inclusion hLH a)).val 3 0 = 0 ∧
    (π (inclusion hLH a)).val 3 1 = 0)
  (a : L1) (ha : (π (inclusion hLH a)).val = planeCubic)

include p hLH hUV in
private theorem span_le_VH : conjugateSpanBy (U0 UH V2) L1 ≤ VH :=
  conjugateSpanBy_le hUV (hLH.trans p.normalized)

include hact hUV hfirst hblock ha in
/-- The literal L₁-conjugate span has the computed orthogonal hyperplane as image. -/
theorem source_cubic_span_image :
    p.imageSpace (conjugateSpanBy (U0 UH V2) L1) = planeSpace := by
  let S := conjugateSpanBy (U0 UH V2) L1
  have hSV : S ≤ VH := span_le_VH H VH UH V2 L1 ρ p hLH hUV
  have he : S = ⨆ g : L1, (U0 UH V2).conjBy g.val := by
    apply le_antisymm
    · apply (closure_le _).mpr
      rintro x ⟨g,hg,u,hu,rfl⟩
      exact (le_iSup (fun g : L1 => (U0 UH V2).conjBy g.val) ⟨g,hg⟩) ⟨u,hu,rfl⟩
    · apply iSup_le
      intro g x hx
      obtain ⟨u,hu,rfl⟩ := hx
      exact subset_closure ⟨g,g.property,u,hu,rfl⟩
  have hle : p.imageSpace S ≤ planeSpace := by
    rw [he, p.imageSpace_iSup]
    · apply iSup_le
      intro g
      have hc := p.imageSpace_conjBy (U0 UH V2) hUV (inclusion hLH g)
      change p.imageSpace ((U0 UH V2).conjBy (g : G)) =
        (p.imageSpace (U0 UH V2)).map (ρ (inclusion hLH g)) at hc
      rw [hc, hfirst]
      rintro _ ⟨x,hx,rfl⟩
      rw [hact]
      obtain ⟨h20,h21,h30,h31⟩ := hblock g
      exact planeSpace_preserved _ h20 h21 h30 h31 x (firstSpace_le_planeSpace hx)
    · intro g
      exact (le_iSup (fun g : L1 => (U0 UH V2).conjBy g.val) g).trans (he.symm ▸ hSV)
  apply le_antisymm hle
  apply planeSpace_le_of_cubic
  · rw [← hfirst]
    exact p.imageSpace_mono (le_conjugateSpanBy _ _)
  · intro x hx
    have hh := p.imageSpace_apply_mem S (inclusion hLH a)
      (le_normalizer_conjugateSpanBy _ _ a.property) x hx
    rwa [hact,ha] at hh

include hact hUV hfirst hblock ha in
/-- The exterior span has index 64 over V before passing to the maximal kernel. -/
theorem source_cubic_span_index [Finite G]
    (V : Subgroup G) (hVU : V ≤ U0 UH V2) (hindex : V.relIndex (U0 UH V2) = 16) :
    V.relIndex (conjugateSpanBy (U0 UH V2) L1) = 64 := by
  let S := conjugateSpanBy (U0 UH V2) L1
  have hSV : S ≤ VH := span_le_VH H VH UH V2 L1 ρ p hLH hUV
  have hUS : U0 UH V2 ≤ S := le_conjugateSpanBy _ _
  have hSP := source_cubic_span_image H VH UH V2 L1 ρ p π hact hLH hUV hfirst hblock a ha
  have hcS : UH.relIndex S = 32 := by
    rw [← p.imageSpace_card_eq_relIndex S hSV, hSP,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, planeSpace_finrank]
    decide
  have hcU : UH.relIndex (U0 UH V2) = 8 := by
    rw [← p.imageSpace_card_eq_relIndex (U0 UH V2) hUV, hfirst,
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, firstSpace_finrank]
    decide
  have he := relIndex_mul_relIndex UH (U0 UH V2) S (UH_le_U0 UH V2) hUS
  rw [hcS,hcU] at he
  have hstep : (U0 UH V2).relIndex S = 4 := by omega
  have heV := relIndex_mul_relIndex V (U0 UH V2) S hVU hUS
  rw [hindex,hstep] at heV
  exact heV.symm

end CFSG.Quasithin.Chapter13.Section08.LinearFour

open Representation.Hexacode Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open Representation.BinaryParabolicExteriorSquare.PlaneSpan
variable {G Z : Type*} [Group G] [Finite G]
  [AddCommGroup Z] [Module (ZMod 2) Z] [Module F Z]

/-- A cubic in the original parabolic image lifts to its actual two-residual. -/
theorem source_plane_cubic_in_residual
    (H P L1 : Subgroup G) (hPH : P ≤ H) (h1H : L1 ≤ H)
    (hL1 : L1 = (pResidual 2 P).map P.subtype)
    (π : H →* SL(4, ZMod 2))
    (a : P) (ha : (π (inclusion hPH a)).val = planeCubic) :
    ∃ b : L1, (π (inclusion h1H b)).val = planeCubic := by
  let f := π.comp (inclusion hPH)
  let r : f.range := ⟨f a, ⟨a,rfl⟩⟩
  have hr : r ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (f a).val ^ 3 = 1
    rw [show (f a).val = planeCubic from ha, planeCubic_cube]
  have hm : r ∈ pResidual 2 f.range := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hr))
  rw [← map_pResidual_of_surjective 2 f.rangeRestrict f.rangeRestrict_surjective] at hm
  obtain ⟨b,hb,he⟩ := hm
  have hb1 : (b : G) ∈ L1 := by rw [hL1]; exact mem_map_of_mem P.subtype hb
  refine ⟨⟨b,hb1⟩,?_⟩
  exact (congrArg (fun x : f.range => x.val.val) he).trans ha

/-- The span cannot collapse to the tensor plane: that would make the plane
invariant under both source generators of L. The index bound then gives
field dimension three and equality of the original subgroup kernel with V. -/
theorem source_span_dimension_and_kernel
    (L UL N UH V2 L1 V D : Subgroup G)
    (η : Representation (ZMod 2) L Z) [IsIrreducible η]
    (q : BinaryConjugationSection L UL N η)
    (h1L : L1 ≤ L)
    (hgen : L1.subgroupOf L ⊔ (G2 V2).subgroupOf L = ⊤)
    (hSU : U0 UH V2 ≤ UL) (hVS : V ≤ U0 UH V2) (hVN : V ≤ N)
    (hindex : V.relIndex (conjugateSpanBy (U0 UH V2) L1) = 64)
    (hDL : D ≤ L) (hD1 : D ≤ L1)
    (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, η (inclusion hDL x) w = (χ x : F) • w)
    (hDU : D ≤ normalizer (U0 UH V2))
    (hd2 : Module.finrank F (q.scalarImage D hDL χ hχ hscalar (U0 UH V2) hDU) = 2)
    (τ : Representation F HexEvenAutomorphisms Z) [IsIrreducible τ]
    (hz : ∀ w, τ hexEvenZ w = omega • w) :
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar
      (conjugateSpanBy (U0 UH V2) L1)
      (hD1.trans (le_normalizer_conjugateSpanBy _ _))) = 3 ∧
    conjugateSpanBy (U0 UH V2) L1 ⊓ N = V := by
  let : Finite Z := Finite.of_surjective (fun x : UL => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  let S := conjugateSpanBy (U0 UH V2) L1
  let S2 := q.scalarImage D hDL χ hχ hscalar (U0 UH V2) hDU
  let S3 := q.scalarImage D hDL χ hχ hscalar S
    (hD1.trans (le_normalizer_conjugateSpanBy _ _))
  have hUS : U0 UH V2 ≤ S := le_conjugateSpanBy _ _
  have hSUL : S ≤ UL := conjugateSpanBy_le hSU (h1L.trans q.normalized)
  have h23 : S2 ≤ S3 := q.imageSpace_mono hUS
  have hF : Nat.card F = 4 := (Nat.card_eq_fintype_card).trans field_card
  have hc : Nat.card S3 ≤ 64 := (q.imageSpace_card_le_relative_index S V hVN).trans_eq hindex
  have hdimupper : Module.finrank F S3 ≤ 3 := by
    rw [Module.natCard_eq_pow_finrank (K := F), hF] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 4)).mp hc
  have hneq : S2 ≠ S3 := by
    intro he
    have himage : q.imageSpace S = q.imageSpace (U0 UH V2) := by
      ext w
      exact (show w ∈ S3 ↔ w ∈ S2 from he ▸ Iff.rfl)
    have hn : q.imageSpace (U0 UH V2) ≠ ⊥ := by
      intro hbot
      have hb : S2 = ⊥ := by
        ext w
        change w ∈ q.imageSpace (U0 UH V2) ↔ w = 0
        rw [hbot]; rfl
      change Module.finrank F S2 = 2 at hd2
      have hzero : Module.finrank F S2 = 0 := by rw [hb]; simp
      omega
    have htop := q.image_eq_top_of_generators (U0 UH V2) S
      (L1.subgroupOf L) ((G2 V2).subgroupOf L) hgen
      (fun j => le_normalizer_conjugateSpanBy _ _ j.property)
      (fun k => G2_normalizes_U0 UH V2 k.property) himage hn
    have hs2top : S2 = ⊤ := by
      ext w
      change w ∈ q.imageSpace (U0 UH V2) ↔ True
      rw [htop]; rfl
    have hdimZ : Module.finrank F Z = 2 := by
      change Module.finrank F S2 = 2 at hd2
      rw [hs2top] at hd2
      simpa using hd2
    have hdegrees := Representation.Hexacode.TwelveDimensional.field_finrank_three_or_nine τ hz
    omega
  have hdimlower := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne h23 hneq)
  have hd3 : Module.finrank F S3 = 3 := by
    change Module.finrank F S2 = 2 at hd2
    omega
  refine ⟨hd3,?_⟩
  have hcard : Nat.card (q.imageSpace S) = 64 := by
    change Nat.card S3 = 64
    rw [Module.natCard_eq_pow_finrank (K := F),hF,hd3]
    decide
  have hNS : (S ⊓ N).relIndex S = 64 := by
    rw [inf_relIndex_left]
    exact (q.imageSpace_card_eq_relIndex S hSUL).symm.trans hcard
  have hVNS : V ≤ S ⊓ N := le_inf (hVS.trans hUS) hVN
  have he := relIndex_mul_relIndex V (S ⊓ N) S hVNS inf_le_left
  rw [hNS,hindex] at he
  exact le_antisymm (relIndex_eq_one.mp (by omega : V.relIndex (S ⊓ N) = 1)) hVNS

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
/-- The natural second-tensor branch using the actual parabolic two-residual.
The cubic actor is lifted, and generation supplies the kernel and corrected
quotient dimension. No Levi involutions are assumed to belong to L₁. -/
theorem source_nine_factors_of_residual_cubic [Finite G] [FiniteDimensional (ZMod 2) U]
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
