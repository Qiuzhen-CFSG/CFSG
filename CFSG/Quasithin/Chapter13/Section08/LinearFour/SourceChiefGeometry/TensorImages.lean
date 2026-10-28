module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceTensorKernel
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.Quotient

/-!
# The actual field line and plane in the maximal quotient

The source seed tensor and irreducible U_H/V₃ section determine the kernel
on U_H and U₀. Their images in the original U_L/N consequently have orders
four and sixteen. The full scalar action of L₀ makes these literal binary
images field subspaces, of dimensions one and two. Restricting the first
image to the subsequent three-space supplies its actual field line to the
nine-chief-factor theorem; its dimension is no longer an assumed premise.

The scalar and intersected coordinate actions remain explicit and retain the
same subgroup quotient. The next quotient dimension and the actor moving its
span still require the orthogonal module and the second tensor from 13.8.29.
The initial markings and these remaining premises belong to
qt-d-138-linear-four-source; this is not completion of 13.8.30 or 13.8.28.

Source: Aschbacher–Smith, 13.8.30, printed p.964. The corrected quotient in
the consumer is the three-space modulo the image of U_H, not modulo U_L.
-/

public section
open Representation.Hexacode Atlas.Codes
open scoped TensorProduct
open Subgroup Representation
open Representation.CyclicSeedTensor Representation.QuadraticFourGroup.TensorClassification
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
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


/-- The full scalar action makes a literal image a field subspace of its computed dimension. -/
theorem source_field_image_dimension
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Module F Z]
    [Finite G] (L UL N B D : Subgroup G)
    (η : Representation (ZMod 2) L Z) (q : BinaryConjugationSection L UL N η)
    (hDL : D ≤ L) (χ : D →* Fˣ) (hχ : Function.Surjective χ)
    (hscalar : ∀ x w, η (inclusion hDL x) w = (χ x : F) • w)
    (hn : D ≤ normalizer B) (hBU : B ≤ UL) (n : ℕ)
    (hcard : Nat.card (q.imageSpace B) = 4 ^ n) :
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar B hn) = n := by
  have hF : Nat.card F = 4 := (Nat.card_eq_fintype_card).trans field_card
  apply q.scalarImage_finrank D hDL χ hχ hscalar B hn (by rw [hF]; decide) hBU n
  rw [hF, ← q.imageSpace_card_eq_relIndex B hBU]
  exact hcard

include himage hcyclic ht ha hf hb0 hb1 in
theorem source_maximal_tensor_field_dimensions [Finite G] [FiniteDimensional (ZMod 2) U]
    {Z : Type*} [AddCommGroup Z] [Module (ZMod 2) Z] [Module Representation.Hexacode.F Z]
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
    (hDU : D ≤ normalizer UH) (hDS : D ≤ normalizer (U0 UH V2)) :
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar UH hDU) = 1 ∧
    Module.finrank F (q.scalarImage D hDL χ hχ hscalar (U0 UH V2) hDS) = 2 := by
  obtain ⟨hfirst,hsecond⟩ := source_maximal_tensor_image_orders
    UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
    hd hu₀ L J UL N V3 V hUL hN hproper hJL ψ s hseedDim hV3V hV2V hVS hVN
    htimage β hβ hβL η q hSU
  exact ⟨source_field_image_dimension L UL N UH D η q hDL χ hχ hscalar hDU
      ((UH_le_U0 UH V2).trans hSU) 1 (by simpa using hfirst),
    source_field_image_dimension L UL N (U0 UH V2) D η q hDL χ hχ hscalar hDS
      hSU 2 hsecond⟩

include himage hcyclic ht ha hf hb0 hb1 in
theorem source_nine_factors_of_maximal_tensor [Finite G] [FiniteDimensional (ZMod 2) U]
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
    (S3 : Submodule F Z)
    (hlinele : q.scalarImage D hDL χ hχ hscalar UH hDU ≤ S3)
    (hquotient : Module.finrank F
      (S3 ⧸ (q.scalarImage D hDL χ hχ hscalar UH hDU).comap S3.subtype) = 2)
    (hmoved : ∃ g w, w ∈ S3 ∧ τ g w ∉ S3)
    (chief : NoncentralChiefRefinement.ChiefSeries D)
    (hc0 : chief.head = ⊥) (hc1 : chief.last = ⊤) :
    9 ≤ chief.noncentralTwoCount := by
  let : Finite Z := Finite.of_surjective (fun x : UL => (q.coordinates x).toAdd)
    (Multiplicative.toAdd.surjective.comp q.onto)
  obtain ⟨hline,_⟩ := source_maximal_tensor_field_dimensions
    UH V2 π ρ σ μ d f himage u₀ hcyclic t ht a ha hf b hb0 hb1
    hd hu₀ L J UL N V3 V hUL hN hproper hJL ψ s hseedDim hV3V hV2V hVS hVN
    htimage β hβ hβL η q hSU D hDL χ hχ hscalar hDU hDS
  have hline' : Module.finrank F
      ((q.scalarImage D hDL χ hχ hscalar UH hDU).comap S3.subtype) = 1 :=
    (Submodule.comapSubtypeEquivOfLe hlinele).finrank_eq.trans hline
  have hn : ∃ x, χ x ≠ 1 := by
    let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_units, Nat.card_eq_fintype_card, field_card]
      decide)
    obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
    obtain ⟨x,rfl⟩ := hχ a
    exact ⟨x,ha⟩
  exact source_nine_factors_of_marked_quotient D UL N τ hz
    (η.comp (inclusion hDL)) d₀ χ hχ hn hscalar S3
    ((q.scalarImage D hDL χ hχ hscalar UH hDU).comap S3.subtype)
    hline' hquotient hmoved chief hc0 hc1
end CFSG.Quasithin.Chapter13.Section08.LinearFour
