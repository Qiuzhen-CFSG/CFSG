module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

/-!
# Compatible source point fixers and the natural extension

A binary point normalized by the actual Sylow subgroup is fixed pointwise.
The weight-four augmentation point and its canonical natural image have
exactly the duad stabilizer `BinaryFlags.H1`. Transporting these identities
through the conjugation-compatible coordinates of the literal U_H/V₁
identifies the actual quotient centralizer. Its permutation image is H1 or
L1 because the full acting image contains the marked alternating group.
Normalizing the order-two V₁ also gives H ≤ C_G(V₁).

In the natural branch the source centralizer bound supplies faithfulness,
and the proved natural A₆ normalizer constructs the full faithful H* action
extending the prescribed K* marking. `natural_source_outputs` gives all three
inputs needed by the parent's residual/quotient transport. The augmentation
version takes the full compatible extension as input; the companion
`Assembly` module now constructs it from the component action.

Conjugate generation transports to the exact orbit span. Once the actual
Sylow image is aligned with the canonical Borel, dimension and invariance
force the natural plane. Its identification with the image of the explicit
weight-four cover plane is also proved. The companion `Geometry` module chooses that alignment and derives the
cover plane from its orbit generation. No plane marking or K₂ image is
assumed in these deductions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6(3),
printed pp.938–939, the first paragraph of the proof of 13.8.6, printed
p.948, and §B.3, printed pp.83–85. The earlier source point witness, relative
normality of K*, flag dimensions, normalizers and generation identities
remain explicit inputs for the source assembly. This module does not assert
the completion of 13.8.6.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags

open Subgroup Module Representation Representation.BinaryOffender BinaryPermutation
open TransvectionRecognition Theory.SpecificGroups.SymmetricSix ComponentSieve.SixAndG2
open scoped commutatorElement IsMulCommutative

/-- The weight-four cover point projects to the duad used by BinaryFlags. -/
theorem naturalPoint_eq_pairVector : OrbitModels.naturalPoint = BinaryFlags.NaturalGeometry.pairVector 4 5 := by
  apply Subtype.ext
  apply (Submodule.Quotient.eq (constants (Fin 6))).2
  apply Submodule.subset_span
  change _ = allOne (Fin 6)
  ext i
  fin_cases i <;> decide

theorem naturalPoint_fixed_iff (g : Equiv.Perm (Fin 6)) :
    naturalRepresentation (Fin 6) g OrbitModels.naturalPoint = OrbitModels.naturalPoint ↔ g ∈ BinaryFlags.H1 := by
  rw [naturalPoint_eq_pairVector, BinaryFlags.NaturalGeometry.pairVector_map,
    BinaryFlags.NaturalGeometry.pairVector_eq_iff (g.injective.ne (by decide)) (by decide)]
  change Theory.SpecificGroups.SymmetricSix.pair (g 4) (g 5) = _ ↔
    (Theory.SpecificGroups.SymmetricSix.pair 4 5).image g = _
  simp [Theory.SpecificGroups.SymmetricSix.pair]

theorem point_fixed_iff (g : Equiv.Perm (Fin 6)) :
    coreRepresentation (Fin 6) g OrbitModels.point = OrbitModels.point ↔ g ∈ BinaryFlags.H1 := by
  constructor
  · intro hg
    apply (naturalPoint_fixed_iff g).mp
    exact (coreToNatural_equivariant g OrbitModels.point).symm.trans
      (congrArg (coreToNatural (Fin 6)) hg)
  · intro hg
    have hp : ∀ i : Fin 6, OrbitModels.point.val i = if i = 4 ∨ i = 5 then 0 else 1 := by decide
    apply Subtype.ext
    ext i
    change OrbitModels.point.val (g.symm i) = OrbitModels.point.val i
    have hg' := BinaryFlags.mem_H1_cases hg
    simp only [hp, Equiv.symm_apply_eq]
    rcases hg' with ⟨h4, h5⟩ | ⟨h4, h5⟩ <;> simp [h4, h5, or_comm]

private theorem fixes_span_iff {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (a : W →ₗ[ZMod 2] W) (w : W) :
    (∀ x ∈ Submodule.span (ZMod 2) {w}, a x = x) ↔ a w = w := by
  constructor
  · intro h
    exact h w (Submodule.subset_span (by simp))
  · intro h x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, h]

private theorem fixes_transport_iff {A U W : Type*} [Group A]
    [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A U) (σ : Representation (ZMod 2) A W)
    (E : U ≃ₗ[ZMod 2] W) (he : ∀ a u, E (ρ a u) = σ a (E u))
    (P : Submodule (ZMod 2) U) (a : A) :
    (∀ x ∈ P, ρ a x = x) ↔ ∀ y ∈ P.map E.toLinearMap, σ a y = y := by
  constructor
  · rintro h y ⟨x, hx, rfl⟩
    change σ a (E x) = E x
    rw [← he, h x hx]
  · intro h x hx
    apply E.injective
    rw [he]
    exact h (E x) (Submodule.mem_map_of_mem hx)

private theorem range_cases {A : Type*} [Group A] (φ : A →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range) :
    φ.range = ⊤ ∨ φ.range = alternatingGroup (Fin 6) := by
  by_cases h : φ.range ≤ alternatingGroup (Fin 6)
  · exact Or.inr (le_antisymm h ha)
  · left
    obtain ⟨s, hs, hsa⟩ := SetLike.not_le_iff_exists.mp h
    apply top_unique
    intro g _
    by_cases hg : g ∈ alternatingGroup (Fin 6)
    · exact ha hg
    · have hx : g * s⁻¹ ∈ alternatingGroup (Fin 6) := by
        rw [Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two,
          Subgroup.inv_mem_iff]
        simp [hg, hsa]
      simpa only [inv_mul_cancel_right] using φ.range.mul_mem (ha hx) hs

/-- Pulling back the point stabilizer and taking its image gives the full
symmetric or alternating duad parabolic, not an assumed residual image. -/
theorem parabolic_image {A : Type*} [Group A] (φ : A →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range) (C : Subgroup A)
    (hC : ∀ a, a ∈ C ↔ φ a ∈ BinaryFlags.H1) :
    C.map φ = BinaryFlags.H1 ∨ C.map φ = BinaryFlags.L1 := by
  have he : C = BinaryFlags.H1.comap φ := by ext a; exact hC a
  rw [he, Subgroup.map_comap_eq]
  rcases range_cases φ ha with h | h
  · exact Or.inl (by rw [h, top_inf_eq])
  · exact Or.inr (by rw [h, inf_comm]; rfl)

variable {G : Type*} [Group G] {H V₃ V₂ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- A marked natural point identifies the literal quotient centralizer. -/
theorem natural_preimage_mem_iff
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G)) (h : H) :
    h ∈ (commutatorPreimage H V₂ V₁).subgroupOf H ↔
      φ (QuotientGroup.mk' (pCore 2 H) h) ∈ BinaryFlags.H1 := by
  rw [quotient_centralizer_preimage ρ hρ V₂ hV₂ hHZ]
  change (h ∈ (⊤ : Subgroup H) ∧ ∀ x ∈ sectionImage H V₃ V₁ V₂,
    ρ (QuotientGroup.mk' (pCore 2 H) h) x = x) ↔ _
  rw [and_iff_right (mem_top h), fixes_transport_iff ρ
    ((naturalRepresentation (Fin 6)).comp φ) E he, hpoint]
  exact (fixes_span_iff _ _).trans (naturalPoint_fixed_iff _)

/-- The same fixer identity retains the actual weight-four vector in the cover. -/
theorem augmentation_preimage_mem_iff
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G)) (h : H) :
    h ∈ (commutatorPreimage H V₂ V₁).subgroupOf H ↔
      φ (QuotientGroup.mk' (pCore 2 H) h) ∈ BinaryFlags.H1 := by
  rw [quotient_centralizer_preimage ρ hρ V₂ hV₂ hHZ]
  change (h ∈ (⊤ : Subgroup H) ∧ ∀ x ∈ sectionImage H V₃ V₁ V₂,
    ρ (QuotientGroup.mk' (pCore 2 H) h) x = x) ↔ _
  rw [and_iff_right (mem_top h), fixes_transport_iff ρ
    ((coreRepresentation (Fin 6)).comp φ) E he, hpoint]
  exact (fixes_span_iff _ _).trans (point_fixed_iff _)

/-- The source centralizer bound supplies faithfulness; the normalizer theorem
then extends the prescribed component marking to the whole actual H*. -/
theorem natural_extension (K : Subgroup G) [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ k : Source.starImage H K, ∀ u,
      E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u)) :
    ∃ φ : Source.Hstar H →* Equiv.Perm (Fin 6), Function.Injective φ ∧
      (∀ k : Source.starImage H K, φ k = (eK k).val) ∧
      (∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u)) ∧
      alternatingGroup (Fin 6) ≤ φ.range := by
  obtain ⟨φ, hφ, hφK, hφE, _⟩ := NaturalSix.faithful_extension (Source.starImage H K) ρ
    (faithful_of_centralizer_le_core ρ hρ hcentralizer) eK E he
  refine ⟨φ, hφ, hφK, hφE, ?_⟩
  intro a ha
  obtain ⟨k, hk⟩ := eK.surjective ⟨a, ha⟩
  exact ⟨k.val, by rw [hφK, hk]⟩


/-- Normalizing an actual order-two subgroup fixes its unique nonidentity
point. In the application the normalizer is the source G₁. -/
private theorem centralizes_order_two {D : Type*} [Group D] (A Z : Subgroup D)
    (hAZ : A ≤ normalizer (Z : Set D)) (hZ : Nat.card Z = 2) :
    A ≤ centralizer (Z : Set D) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xZ : Z := ⟨x, hx⟩
  let yZ : Z := ⟨g * x * g⁻¹, (hAZ hg x).mp hx⟩
  have hyne : yZ ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : D => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have he : yZ = xZ := (hzuniq yZ hyne).trans (hzuniq xZ (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have he' : g * x * g⁻¹ = x := congrArg Subtype.val he
  have h := congrArg (fun a : D => a * g) he'
  simpa [mul_assoc] using h.symm

private theorem fixes_binary_line {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) A W) (P : Submodule (ZMod 2) W)
    (hdim : finrank (ZMod 2) P = 1) (a : A)
    (hinv : ∀ x ∈ P, ρ a x ∈ P) : ∀ x ∈ P, ρ a x = x := by
  let : Fintype P := Fintype.ofFinite P
  have hcard : Nat.card P = 2 := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2),
      ZMod.card, hdim, pow_one]
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (0 : P)).mp hcard
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have ha0 : ρ a x ≠ 0 := by
    intro he
    have he' := congrArg (ρ a⁻¹) he
    rw [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] at he'
    exact hx0 he'
  exact congrArg Subtype.val ((hzuniq ⟨ρ a x, hinv x hx⟩ (by
    intro he; exact ha0 (congrArg Subtype.val he))).trans
      (hzuniq ⟨x, hx⟩ (by intro he; exact hx0 (congrArg Subtype.val he))).symm)

/-- Normalization of V₂ transports to invariance of its actual section image. -/
theorem sectionImage_invariant
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (X : Subgroup G) (h : H)
    (hn : (h : G) ∈ normalizer (X : Set G)) :
    ∀ x ∈ sectionImage H V₃ V₁ X,
      ρ (QuotientGroup.mk' (pCore 2 H) h) x ∈ sectionImage H V₃ V₁ X := by
  rintro x ⟨u, hu, rfl⟩
  change ρ (QuotientGroup.mk' (pCore 2 H) h) (vector H V₃ V₁ u) ∈ _
  rw [hρ]
  exact ⟨_, (hn (u : G)).mp hu, rfl⟩

/-- The actual Sylow subgroup centralizes the binary point Ṽ₂ because it
normalizes V₂ and that section has dimension one. -/
theorem sylow_le_preimage [Finite G] (T : Sylow 2 G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (hTH : (T : Subgroup G) ≤ H)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hpoint : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G)) :
    (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁ := by
  intro t ht
  have hf := fixes_binary_line ρ (sectionImage H V₃ V₁ V₂) hpoint
    (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)
    (sectionImage_invariant ρ hρ V₂ ⟨t, hTH ht⟩ (hTV₂ ht))
  have hm : (⟨t, hTH ht⟩ : H) ∈ subspaceKernel
      (ρ.comp (QuotientGroup.mk' (pCore 2 H))) (sectionImage H V₃ V₁ V₂) ⊤ :=
    ⟨mem_top _, hf⟩
  rw [← quotient_centralizer_preimage ρ hρ V₂ hV₂ hHZ] at hm
  exact hm

/-- A natural-module marking gives precisely the image required by the
residual and S₃-quotient transport theorem. -/
theorem natural_preimage_image
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G)) :
    ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
      ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1 := by
  apply parabolic_image _ ?_ _ (natural_preimage_mem_iff ρ hρ φ E he hpoint hV₂ hHZ)
  intro a ha'
  obtain ⟨b, rfl⟩ := ha ha'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) b
  exact ⟨h, rfl⟩

/-- The augmentation marking gives the same parabolic image, while retaining
weight four in the cover rather than merely its natural projection. -/
theorem augmentation_preimage_image
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G)) :
    ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
      ((commutatorPreimage H V₂ V₁).subgroupOf H).map
        (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1 := by
  apply parabolic_image _ ?_ _ (augmentation_preimage_mem_iff ρ hρ φ E he hpoint hV₂ hHZ)
  intro a ha'
  obtain ⟨b, rfl⟩ := ha ha'
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) b
  exact ⟨h, rfl⟩


/-- All three source hypotheses required by the residual/quotient bridge in
the natural branch, with the faithful extension constructed from K*. -/
theorem natural_source_outputs [Finite G] (T : Sylow 2 G)
    (K : Subgroup G) [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (hcentralizer : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (heK : ∀ k : Source.starImage H K, ∀ u,
      E (ρ k u) = alternatingNaturalRepresentation (Fin 6) (eK k) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.naturalPointSpace)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G))
    (hV₁ : Nat.card V₁ = 2) :
    ∃ φ : Source.Hstar H →* Equiv.Perm (Fin 6), Function.Injective φ ∧
      (∀ k : Source.starImage H K, φ k = (eK k).val) ∧
      (∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u)) ∧
      (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁ ∧
      H ≤ centralizer (V₁ : Set G) ∧
      (((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
        ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) := by
  obtain ⟨φ, hφ, hφK, hφE, ha⟩ := natural_extension K ρ hρ hcentralizer eK E heK
  have hdim : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1 := by
    rw [← E.finrank_map_eq, hpoint]
    exact finrank_span_singleton OrbitModels.naturalPoint_ne_zero
  exact ⟨φ, hφ, hφK, hφE,
    sylow_le_preimage T ρ hρ hTH hTV₂ hdim hV₂ hHZ,
    centralizes_order_two H V₁ hHZ hV₁,
    natural_preimage_image ρ hρ φ ha E hφE hpoint hV₂ hHZ⟩

/-- The three source hypotheses in the augmentation branch once its full
compatible extension has been constructed. The cover point is not replaced
by a natural-module representative. -/
theorem augmentation_source_outputs [Finite G] (T : Sylow 2 G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (ha : alternatingGroup (Fin 6) ≤ φ.range)
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u))
    (hpoint : (sectionImage H V₃ V₁ V₂).map E.toLinearMap = OrbitModels.pointSpace)
    (hTH : (T : Subgroup G) ≤ H)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hV₂ : V₂ ≤ Source.UH H V₃) (hHZ : H ≤ normalizer (V₁ : Set G))
    (hV₁ : Nat.card V₁ = 2) :
    (T : Subgroup G) ≤ commutatorPreimage H V₂ V₁ ∧
      H ≤ centralizer (V₁ : Set G) ∧
      (((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.H1 ∨
        ((commutatorPreimage H V₂ V₁).subgroupOf H).map
          (φ.comp (QuotientGroup.mk' (pCore 2 H))) = BinaryFlags.L1) := by
  have hdim : finrank (ZMod 2) (sectionImage H V₃ V₁ V₂) = 1 := by
    rw [← E.finrank_map_eq, hpoint]
    exact OrbitModels.pointSpace_finrank
  exact ⟨sylow_le_preimage T ρ hρ hTH hTV₂ hdim hV₂ hHZ,
    centralizes_order_two H V₁ hHZ hV₁,
    augmentation_preimage_image ρ hρ φ ha E he hpoint hV₂ hHZ⟩

/-- After aligning the actual Sylow image with the canonical alternating
Borel, invariance and the actual dimension force the source plane marking.
The Borel containment is a coordinate-alignment obligation, not a plane
marking assumption. -/
theorem natural_plane_of_aligned_sylow (T : Sylow 2 G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 6))
    (E : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] natural (Fin 6))
    (he : ∀ a u, E (ρ a u) = naturalRepresentation (Fin 6) (φ a) (E u))
    (hTV₃ : (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (hdim : finrank (ZMod 2) (sectionImage H V₃ V₁ V₃) = 2)
    (halign : BinaryFlags.NaturalGeometry.T0 ≤ ((T : Subgroup G).subgroupOf H).map
      (φ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    (sectionImage H V₃ V₁ V₃).map E.toLinearMap =
      BinaryFlags.NaturalGeometry.canonicalPlane := by
  let W := (sectionImage H V₃ V₁ V₃).map E.toLinearMap
  have hW (g : Equiv.Perm (Fin 6)) (hg : g ∈ BinaryFlags.NaturalGeometry.T0) :
      ∀ w ∈ W, naturalRepresentation (Fin 6) g w ∈ W := by
    obtain ⟨t, ht, rfl⟩ := halign hg
    rintro w ⟨x, hx, rfl⟩
    change naturalRepresentation (Fin 6) (φ (QuotientGroup.mk' (pCore 2 H) t)) (E x) ∈ W
    rw [← he]
    exact Submodule.mem_map_of_mem (sectionImage_invariant ρ hρ V₃ t (hTV₃ ht) x hx)
  apply BinaryFlags.NaturalGeometry.canonicalPlane_unique W
  · rw [E.finrank_map_eq]
    exact hdim
  · intro g hg
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact hW g hg w hw
    · intro w hw
      refine ⟨naturalRepresentation (Fin 6) g⁻¹ w,
        hW g⁻¹ (BinaryFlags.NaturalGeometry.T0.inv_mem hg) w hw, ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]


/-- Group conjugate generation becomes the orbit span in the literal source
section. This transports the earlier identity V₃ = ⟨V₂^L₁⟩ without replacing
it by a plane-marking premise. -/
theorem sectionImage_conjugateSpan
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ) (X J : Subgroup G)
    (hX : X ≤ Source.UH H V₃) (hJ : J ≤ H) :
    sectionImage H V₃ V₁ (conjugateSpanBy X J) =
      Submodule.span (ZMod 2) {v | ∃ a ∈ Source.starImage H J,
        ∃ x ∈ sectionImage H V₃ V₁ X, ρ a x = v} := by
  let U := Source.UH H V₃
  let q : U →* Source.Utilde H V₃ V₁ := QuotientGroup.mk' (V₁.subgroupOf U)
  let S := Submodule.span (ZMod 2) {v | ∃ a ∈ Source.starImage H J,
    ∃ x ∈ sectionImage H V₃ V₁ X, ρ a x = v}
  let C := (S.toAddSubgroup.toSubgroup'.comap q).map U.subtype
  have hgen : conjugateSpanBy X J ≤ C := by
    apply (Subgroup.closure_le C).mpr
    rintro v ⟨j, hj, x, hx, rfl⟩
    refine ⟨⟨j * x * j⁻¹,
      le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H)
        j (hJ hj) x (hX hx)⟩, ?_, rfl⟩
    change vector H V₃ V₁ _ ∈ S
    rw [← hρ ⟨j, hJ hj⟩ ⟨x, hX hx⟩]
    exact Submodule.subset_span ⟨_, ⟨⟨j, hJ hj⟩, hj, rfl⟩,
      _, ⟨⟨x, hX hx⟩, hx, rfl⟩, rfl⟩
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    obtain ⟨w, hw, he⟩ := hgen hu
    have he' : w = u := Subtype.ext he
    subst w
    exact hw
  · apply Submodule.span_le.mpr
    rintro v ⟨a, ⟨j, hj, rfl⟩, x, ⟨u, hu, rfl⟩, rfl⟩
    change ρ (QuotientGroup.mk' (pCore 2 H) j) (vector H V₃ V₁ u) ∈ _
    rw [hρ]
    exact ⟨_, Subgroup.subset_closure ⟨j, hj, u, hu, rfl⟩, rfl⟩


/-- The canonical natural plane is the image of the source's weight-four
plane, not a one-dimensional binary subspace. -/
theorem plane_image_eq_canonical :
    OrbitModels.plane.map (coreToNatural (Fin 6)) =
      BinaryFlags.NaturalGeometry.canonicalPlane := by
  have hseed : coreToNatural (Fin 6) OrbitModels.seed =
      BinaryFlags.NaturalGeometry.pairVector 2 3 := by
    apply Subtype.ext
    apply (Submodule.Quotient.eq (constants (Fin 6))).2
    apply Submodule.subset_span
    change _ = allOne (Fin 6)
    ext i
    fin_cases i <;> decide
  rw [OrbitModels.plane, Submodule.map_span]
  simp only [Set.image_pair]
  change Submodule.span (ZMod 2)
    {OrbitModels.naturalPoint, coreToNatural (Fin 6) OrbitModels.seed} = _
  rw [naturalPoint_eq_pairVector, hseed]
  have hp := BinaryFlags.NaturalGeometry.pairVector_add
  have h23 : BinaryFlags.NaturalGeometry.pairVector 2 3 ∈
      BinaryFlags.NaturalGeometry.canonicalPlane := Submodule.subset_span (by simp)
  have h01 : BinaryFlags.NaturalGeometry.pairVector 0 1 ∈
      BinaryFlags.NaturalGeometry.canonicalPlane := Submodule.subset_span (by simp)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · rw [hp]
      exact Submodule.add_mem _ h01 h23
    · exact h23
  · apply Submodule.span_le.mpr
    rintro x (rfl | rfl)
    · have he : BinaryFlags.NaturalGeometry.pairVector 0 1 =
          BinaryFlags.NaturalGeometry.pairVector 4 5 -
            BinaryFlags.NaturalGeometry.pairVector 2 3 := by rw [hp, add_sub_cancel_right]
      rw [he]
      exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
    · exact Submodule.subset_span (by simp)

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags
