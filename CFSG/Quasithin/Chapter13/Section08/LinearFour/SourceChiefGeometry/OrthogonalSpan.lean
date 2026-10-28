module

public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneSpan
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.TensorImages

/-!
# The literal orthogonal span in the nine-factor argument

In the exterior-square marking of V_H/U_H, the image of U₀ is the
three-space 01,02,03 and V has image the point 01. This conditional adapter assumes L₁ preserves
the natural plane 0,1 and contains the two opposite shears in that plane.
Those actor assumptions have not been derived for the source two-residual;
`ResidualSpan` provides a separate cubic-and-generation route.
Its conjugate span has image the hyperplane with coordinate 23 zero.
The opposite shear forces the maximal kernel's intersection with this
span back into U₀; the first tensor has already computed that kernel as V.

Consequently the span has index 64 over V. The actual scalar image in
U_L/N is a field three-space, and its quotient by the image of U_H has
field dimension two. This is the corrected denominator in the malformed
display on printed p.964. The final theorem applies the original seed
tensor results to discharge both the kernel and index inputs, then feeds
this literal quotient into the nine-chief-factor argument.

The exterior marking, its point and three-space, and the actual parabolic
actors remain explicit geometric inputs. The second tensor must still
supply movement of the span. Their construction, the surrounding chief
strata and the critical-pair estimates remain with
qt-d-138-linear-four-source; qt-d-1381-source owns final source assembly
and the earlier 13.8.27 setup. These conditional results do not assert
completion of source 13.8.29–32 or Theorem 13.8.28.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.29(5) and 13.8.30, printed p.964.
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
  (a : L1) (ha : (π (inclusion hLH a)).val = Matrix.transvection 1 0 1)

include p hLH hUV in
private theorem span_le_VH : conjugateSpanBy (U0 UH V2) L1 ≤ VH :=
  conjugateSpanBy_le hUV (hLH.trans p.normalized)

include hact hUV hfirst hblock ha in
/-- The literal L₁-conjugate span has the computed orthogonal hyperplane as image. -/
theorem source_orthogonal_span_image :
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
  apply planeSpace_le_of_shear
  · rw [← hfirst]
    exact p.imageSpace_mono (le_conjugateSpanBy _ _)
  · intro x hx
    have hh := p.imageSpace_apply_mem S (inclusion hLH a)
      (le_normalizer_conjugateSpanBy _ _ a.property) x hx
    rwa [hact,ha] at hh

include hact hUV hfirst hblock ha in
/-- The maximal kernel has exactly the original V as intersection with this span. -/
theorem source_orthogonal_span_kernel
    (N V : Subgroup G) (hUN : U0 UH V2 ⊓ N = V)
    (hVN : V ≤ N) (hVimage : p.imageSpace V = pointSpace)
    (b : L1) (hb : (π (inclusion hLH b)).val = Matrix.transvection 0 1 1)
    (hNb : (b : G) ∈ normalizer N) :
    conjugateSpanBy (U0 UH V2) L1 ⊓ N = V := by
  let S := conjugateSpanBy (U0 UH V2) L1
  have hSV : S ≤ VH := span_le_VH H VH UH V2 L1 ρ p hLH hUV
  have hVS : V ≤ S := (hUN ▸ (inf_le_left : U0 UH V2 ⊓ N ≤ U0 UH V2)).trans
    (le_conjugateSpanBy _ _)
  have hSP := source_orthogonal_span_image H VH UH V2 L1 ρ p π hact hLH hUV hfirst hblock a ha
  have hpoint : p.imageSpace (S ⊓ N) ≤ pointSpace := by
    apply kernel_le_point
    · rw [← hSP]
      exact p.imageSpace_mono inf_le_left
    · intro w hw
      obtain ⟨x,hx,rfl⟩ := (p.mem_imageSpace_iff (S ⊓ N) w).mp hw.1
      have hxU : (x : G) ∈ U0 UH V2 :=
        (p.coordinates_mem_imageSpace_iff_of_kernel_le (U0 UH V2) (UH_le_U0 UH V2) x).mp
          (hfirst.symm ▸ hw.2)
      rw [← hVimage]
      exact (p.mem_imageSpace_iff V _).mpr ⟨x,hUN ▸ ⟨hxU,hx.2⟩,rfl⟩
    · intro w hw
      have hs : (b : G) ∈ normalizer (S ⊓ N) := by
        exact inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_conjugateSpanBy _ _ b.property,hNb⟩
      have hh := p.imageSpace_apply_mem (S ⊓ N) (inclusion hLH b) hs w hw
      rwa [hact,hb] at hh
  apply le_antisymm ?_ (le_inf hVS hVN)
  intro x hx
  let xV : VH := ⟨x,hSV hx.1⟩
  have hw : (p.coordinates xV).toAdd ∈ pointSpace :=
    hpoint ((p.mem_imageSpace_iff (S ⊓ N) _).mpr ⟨xV,hx,rfl⟩)
  have hwfirst : (p.coordinates xV).toAdd ∈ firstSpace := ⟨hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2⟩
  have hxU : x ∈ U0 UH V2 :=
    (p.coordinates_mem_imageSpace_iff_of_kernel_le (U0 UH V2) (UH_le_U0 UH V2) xV).mp
      (hfirst.symm ▸ hwfirst)
  exact hUN ▸ ⟨hxU,hx.2⟩

include hact hUV hfirst hblock ha in
/-- The actual maximal image of the span has order 64. -/
theorem source_orthogonal_span_image_order [Finite G]
    (N V : Subgroup G) (hUN : U0 UH V2 ⊓ N = V)
    (hVN : V ≤ N) (hVimage : p.imageSpace V = pointSpace)
    (b : L1) (hb : (π (inclusion hLH b)).val = Matrix.transvection 0 1 1)
    (hNb : (b : G) ∈ normalizer N)
    (hindex : V.relIndex (U0 UH V2) = 16)
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z]
    (L UL : Subgroup G) (η : Representation (ZMod 2) L Z)
    (q : BinaryConjugationSection L UL N η)
    (hSU : conjugateSpanBy (U0 UH V2) L1 ≤ UL) :
    Nat.card (q.imageSpace (conjugateSpanBy (U0 UH V2) L1)) = 64 := by
  let S := conjugateSpanBy (U0 UH V2) L1
  have hSV : S ≤ VH := span_le_VH H VH UH V2 L1 ρ p hLH hUV
  have hUS : U0 UH V2 ≤ S := le_conjugateSpanBy _ _
  have hVS : V ≤ U0 UH V2 := hUN ▸ inf_le_left
  have hSP := source_orthogonal_span_image H VH UH V2 L1 ρ p π hact hLH hUV hfirst hblock a ha
  have hSN := source_orthogonal_span_kernel H VH UH V2 L1 ρ p π hact hLH hUV hfirst hblock a ha
    N V hUN hVN hVimage b hb hNb
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
  have heV := relIndex_mul_relIndex V (U0 UH V2) S hVS hUS
  rw [hindex,hstep] at heV
  rw [q.imageSpace_card_eq_relIndex _ hSU, ← inf_relIndex_right N S, inf_comm, hSN]
  exact heV.symm

open Representation.Hexacode
include hact hUV hfirst hblock ha in
/-- The corrected source quotient has field dimension two, with its actual denominator. -/
theorem source_orthogonal_span_quotient_dimension [Finite G]
    (N V : Subgroup G) (hUN : U0 UH V2 ⊓ N = V)
    (hVN : V ≤ N) (hVimage : p.imageSpace V = pointSpace)
    (b : L1) (hb : (π (inclusion hLH b)).val = Matrix.transvection 0 1 1)
    (hNb : (b : G) ∈ normalizer N)
    (hindex : V.relIndex (U0 UH V2) = 16)
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Module F Z]
    (L UL : Subgroup G) (η : Representation (ZMod 2) L Z)
    (q : BinaryConjugationSection L UL N η)
    (hSU : conjugateSpanBy (U0 UH V2) L1 ≤ UL)
    (hfirstcard : Nat.card (q.imageSpace UH) = 4)
    (D : Subgroup G) (hDL : D ≤ L) (hD1 : D ≤ L1)
    (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, η (inclusion hDL x) w = (χ x : F) • w)
    (hDU : D ≤ normalizer UH) :
    let S3 := q.scalarImage D hDL χ hχ hscalar (conjugateSpanBy (U0 UH V2) L1)
      (hD1.trans (le_normalizer_conjugateSpanBy _ _))
    Module.finrank F
      (S3 ⧸ (q.scalarImage D hDL χ hχ hscalar UH hDU).comap S3.subtype) = 2 := by
  let : Finite Z := Finite.of_surjective (fun x : UL => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  let S := conjugateSpanBy (U0 UH V2) L1
  let S3 := q.scalarImage D hDL χ hχ hscalar S
    (hD1.trans (le_normalizer_conjugateSpanBy _ _))
  let C := q.scalarImage D hDL χ hχ hscalar UH hDU
  have hUS : UH ≤ S := (UH_le_U0 UH V2).trans (le_conjugateSpanBy _ _)
  have hCS : C ≤ S3 := q.imageSpace_mono hUS
  have hc := source_orthogonal_span_image_order H VH UH V2 L1 ρ p π hact hLH hUV hfirst
    hblock a ha N V hUN hVN hVimage b hb hNb hindex L UL η q hSU
  have hdS : Module.finrank F S3 = 3 := source_field_image_dimension
    L UL N S D η q hDL χ hχ hscalar _ hSU 3 (by simpa using hc)
  have hdC : Module.finrank F C = 1 := source_field_image_dimension
    L UL N UH D η q hDL χ hχ hscalar hDU (hUS.trans hSU) 1 (by simpa using hfirstcard)
  have hdC' : Module.finrank F (C.comap S3.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hCS).finrank_eq.trans hdC
  have he := (C.comap S3.subtype).finrank_quotient_add_finrank
  change Module.finrank F (S3 ⧸ C.comap S3.subtype) = 2
  omega

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
/-- The first tensor and the marked orthogonal geometry discharge the corrected
quotient dimension in the actual nine-chief-factor consumer. -/
theorem source_nine_factors_of_tensor_orthogonal_span [Finite G] [FiniteDimensional (ZMod 2) U]
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
    (hmoved : ∃ g w,
      w ∈ q.scalarImage D hDL χ hχ hscalar (conjugateSpanBy (U0 UH V2) L1)
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)) ∧
      τ g w ∉ q.scalarImage D hDL χ hχ hscalar (conjugateSpanBy (U0 UH V2) L1)
        (hD1.trans (le_normalizer_conjugateSpanBy _ _)))
    (chief : NoncentralChiefRefinement.ChiefSeries D)
    (hc0 : chief.head = ⊥) (hc1 : chief.last = ⊤) :
    9 ≤ chief.noncentralTwoCount := by
  let S := conjugateSpanBy (U0 UH V2) L1
  let S3 := q.scalarImage D hDL χ hχ hscalar S
    (hD1.trans (le_normalizer_conjugateSpanBy _ _))
  have hspanUL : S ≤ UL := conjugateSpanBy_le hSU (h1L.trans q.normalized)
  have hkernel := (source_maximal_tensor_kernels UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 L J UL N V3 V hUL hN hproper hJL
    ψ s hV3V hV2V hVS hVN htimage β hβ hβL).2
  have hindex := source_tensor_seed_index UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ V hV2V hVS htimage
  have hfirstcard := (source_maximal_tensor_image_orders UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ L J UL N V3 V hUL hN hproper hJL
    ψ s hseedDim hV3V hV2V hVS hVN htimage β hβ hβL η q hSU).1
  have hquotient := source_orthogonal_span_quotient_dimension H VH UH V2 L1 ρ₆ p π₆
    hact h1H hUV hfirst hblock a₆ ha₆ N V hkernel hVN hpoint b₆ hb₆
    (hN (h1L b₆.property)) hindex L UL η q hspanUL hfirstcard D hDL hD1 χ hχ hscalar hDU
  exact source_nine_factors_of_maximal_tensor UH V2 π ρ σ μ d f himage
    u₀ hcyclic t ht a ha hf b hb0 hb1 hd hu₀ L J UL N V3 V hUL hN hproper hJL
    ψ s hseedDim hV3V hV2V hVS hVN htimage β hβ hβL η q hSU D hDL χ hχ hscalar
    hDU hDS τ hz d₀ S3
    (q.imageSpace_mono ((UH_le_U0 UH V2).trans (le_conjugateSpanBy _ _)))
    hquotient hmoved chief hc0 hc1

end CFSG.Quasithin.Chapter13.Section08.LinearFour
