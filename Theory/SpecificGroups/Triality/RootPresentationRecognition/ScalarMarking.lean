module

public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveCollection

/-!
# Compatible markings of the original cubic field

A field equivalence intertwining the original automorphism with q-Frobenius
restricts to an equivalence of the actual fixed subfields. The inclusion
square commutes literally. Cubic trace, norm and the short-root coefficient
are preserved. No cardinality-only replacement of the source fields is used.

Source: GLS3 2.4.2, 2.4.5 and 2.4.7, including the Frobenius
reparametrization convention.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RootPresentationRecognition
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
variable {F : Type*} [Field F]

/-- The field input is an isomorphism with compatible Frobenius, not a group marking. -/
structure ScalarMarking (P : Parameters) (σ : F ≃+* F) where
  extension : F ≃+* ExtensionField P
  frobenius : ∀ x, extension (σ x) = fieldFrobenius P (extension x)

namespace ScalarMarking
variable {P : Parameters} {σ : F ≃+* F} (e : ScalarMarking P σ)

/-- The fixed scalars remain a subfield of the original source extension. -/
abbrev SourceFixed := FixedBy.subfield F σ

/-- Compatibility also determines the inverse field marking. -/
theorem inverse_frobenius (x : ExtensionField P) :
    e.extension.symm (fieldFrobenius P x) = σ (e.extension.symm x) := by
  apply e.extension.injective
  rw [RingEquiv.apply_symm_apply, e.frobenius, RingEquiv.apply_symm_apply]

include e in
/-- Cubicity follows from the compatible model Frobenius. -/
theorem cubic (x : F) : σ (σ (σ x)) = x := by
  apply e.extension.injective
  rw [e.frobenius, e.frobenius, e.frobenius, fieldFrobenius_three]

/-- The induced marking restricts the extension equivalence itself. -/
def fixed : SourceFixed (σ := σ) ≃+* fixedField P where
  toFun x := ⟨e.extension x.val, by
    change fieldFrobenius P (e.extension x.val) = e.extension x.val
    rw [← e.frobenius, show σ x.val = x.val from x.property]⟩
  invFun x := ⟨e.extension.symm x.val, by
    change σ (e.extension.symm x.val) = e.extension.symm x.val
    rw [← e.inverse_frobenius, show fieldFrobenius P x.val = x.val from x.property]⟩
  left_inv x := Subtype.ext (e.extension.symm_apply_apply x.val)
  right_inv x := Subtype.ext (e.extension.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext (e.extension.map_mul x.val y.val)
  map_add' x y := Subtype.ext (e.extension.map_add x.val y.val)

/-- The original fixed-field inclusion square, without an independently chosen embedding. -/
@[simp] theorem fixed_coe (x : SourceFixed (σ := σ)) :
    (e.fixed x : ExtensionField P) = e.extension (x : F) := rfl

@[simp] theorem fixed_symm_coe (x : fixedField P) :
    (e.fixed.symm x : F) = e.extension.symm (x : ExtensionField P) := rfl

/-- Cubic norm on the original source scalars, with its actual fixed-field codomain. -/
def norm (x : F) : SourceFixed (σ := σ) :=
  ⟨x * σ x * σ (σ x), by
    change σ _ = _
    simp only [map_mul, e.cubic]
    ring⟩

/-- Cubic trace on the original source scalars. -/
def trace (x : F) : SourceFixed (σ := σ) :=
  ⟨x + σ x + σ (σ x), by
    change σ _ = _
    simp only [map_add, e.cubic]
    abel⟩

@[simp] theorem fixed_norm (x : F) :
    e.fixed (e.norm x) = cubicNorm P (e.extension x) := by
  apply Subtype.ext
  simp only [fixed_coe, norm, cubicNorm, map_mul, e.frobenius]

@[simp] theorem fixed_trace (x : F) :
    e.fixed (e.trace x) = cubicTrace P (e.extension x) := by
  apply Subtype.ext
  simp only [fixed_coe, trace, cubicTrace_coe, map_add, e.frobenius]

/-- Preservation of the position-7 coefficient, retaining its original orbit origin. -/
theorem higher (x y : F) :
    e.extension (x * σ y + σ x * y) =
      higherCoefficient P (e.extension x) (e.extension y) := by
  simp only [higherCoefficient, map_add, map_mul, e.frobenius]

/-- Mark original source roots using the inverse field equivalences.
The values themselves stay in the original target group. -/
def positiveRoots {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    {Y : Type*} [Group Y]
    (s : Fin 3 → Multiplicative F →* Y)
    (l : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y) : PositiveRoots n hn Y where
  shortRoot i := (s i).comp e.extension.symm.toRingHom.toAddMonoidHom.toMultiplicative
  longRoot i := (l i).comp e.fixed.symm.toRingHom.toAddMonoidHom.toMultiplicative

@[simp] theorem positiveRoots_short {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    {Y : Type*} [Group Y]
    (s : Fin 3 → Multiplicative F →* Y)
    (l : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y)
    (i : Fin 3) (x : F) :
    (e.positiveRoots s l).shortValue i (e.extension x) = s i (.ofAdd x) := by
  change s i (.ofAdd (e.extension.symm (e.extension x))) = _
  rw [RingEquiv.symm_apply_apply]

@[simp] theorem positiveRoots_long {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    {Y : Type*} [Group Y]
    (s : Fin 3 → Multiplicative F →* Y)
    (l : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y)
    (i : Fin 3) (x : SourceFixed (σ := σ)) :
    (e.positiveRoots s l).longValue i (e.fixed x) = l i (.ofAdd x) := by
  change l i (.ofAdd (e.fixed.symm (e.fixed x))) = _
  rw [RingEquiv.symm_apply_apply]

/-- Evaluate a source short root at an additive field parameter. -/
abbrev sourceShort {Y : Type*} [Group Y]
    (s : Fin 3 → Multiplicative F →* Y) (i : Fin 3) (x : F) : Y := s i (.ofAdd x)

/-- Evaluate a source long root in the actual source fixed field. -/
abbrev sourceLong {Y : Type*} [Group Y]
    (l : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y)
    (i : Fin 3) (x : SourceFixed (σ := σ)) : Y := l i (.ofAdd x)

/-- The fifteen positive equations on the original source fields.
Their norm and trace are the literal three σ-conjugates in those fields. -/
structure SourceRelations {Y : Type*} [Group Y]
    (shortRoot : Fin 3 → Multiplicative F →* Y)
    (longRoot : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y) : Prop where
  short0_long1 : ∀ s t, Commute (sourceShort shortRoot 0 s) (sourceLong longRoot 1 t)
  short0_long2 : ∀ s t, Commute (sourceShort shortRoot 0 s) (sourceLong longRoot 2 t)
  long0_short1 : ∀ s t, Commute (sourceLong longRoot 0 s) (sourceShort shortRoot 1 t)
  long0_short2 : ∀ s t, Commute (sourceLong longRoot 0 s) (sourceShort shortRoot 2 t)
  long0_long2 : ∀ s t, Commute (sourceLong longRoot 0 s) (sourceLong longRoot 2 t)
  short1_long1 : ∀ s t, Commute (sourceShort shortRoot 1 s) (sourceLong longRoot 1 t)
  short1_long2 : ∀ s t, Commute (sourceShort shortRoot 1 s) (sourceLong longRoot 2 t)
  short2_long1 : ∀ s t, Commute (sourceShort shortRoot 2 s) (sourceLong longRoot 1 t)
  short2_long2 : ∀ s t, Commute (sourceShort shortRoot 2 s) (sourceLong longRoot 2 t)
  long1_long2 : ∀ s t, Commute (sourceLong longRoot 1 s) (sourceLong longRoot 2 t)
  short0_long0 : ∀ s t,
    sourceShort shortRoot 0 s * sourceLong longRoot 0 t =
      sourceLong longRoot 0 t * sourceShort shortRoot 0 s * sourceShort shortRoot 1 (s*t.val) *
        sourceShort shortRoot 2 (s * σ s * t.val) * sourceLong longRoot 1 (e.norm s * t)
  short0_short1 : ∀ s t,
    sourceShort shortRoot 0 s * sourceShort shortRoot 1 t =
      sourceShort shortRoot 1 t * sourceShort shortRoot 0 s * sourceShort shortRoot 2 ((s * σ t + σ s * t)) *
        sourceLong longRoot 1 (e.trace (s * σ s *
          σ (σ t))) *
        sourceLong longRoot 2 (e.trace (s * σ t *
          σ (σ t)))
  short0_short2 : ∀ s t,
    sourceShort shortRoot 0 s * sourceShort shortRoot 2 t =
      sourceShort shortRoot 2 t * sourceShort shortRoot 0 s *
        sourceLong longRoot 1 (e.trace (σ (σ s) * t))
  short1_short2 : ∀ s t,
    sourceShort shortRoot 1 s * sourceShort shortRoot 2 t =
      sourceShort shortRoot 2 t * sourceShort shortRoot 1 s *
        sourceLong longRoot 2 (e.trace (σ (σ s) * t))
  long0_long1 : ∀ s t, sourceLong longRoot 0 s * sourceLong longRoot 1 t =
    sourceLong longRoot 1 t * sourceLong longRoot 0 s * sourceLong longRoot 2 (s*t)

/-- Compatible scalar transport preserves all fifteen equations, including
both cubic trace terms and the Frobenius-shifted short coefficient. -/
theorem transport_relations {n : ℕ} {hn : 0 < n}
    (e : ScalarMarking (binaryParameters n hn) σ)
    {Y : Type*} [Group Y]
    (s : Fin 3 → Multiplicative F →* Y)
    (l : Fin 3 → Multiplicative (SourceFixed (σ := σ)) →* Y)
    (h : e.SourceRelations s l) : (e.positiveRoots s l).Relations where
  commuting := {
    short0_long1 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short0_long1 a b
    short0_long2 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short0_long2 a b
    long0_short1 a b := by
      obtain ⟨a, rfl⟩ := e.fixed.surjective a
      obtain ⟨b, rfl⟩ := e.extension.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.long0_short1 a b
    long0_short2 a b := by
      obtain ⟨a, rfl⟩ := e.fixed.surjective a
      obtain ⟨b, rfl⟩ := e.extension.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.long0_short2 a b
    long0_long2 a b := by
      obtain ⟨a, rfl⟩ := e.fixed.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_long] using h.long0_long2 a b
    short1_long1 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short1_long1 a b
    short1_long2 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short1_long2 a b
    short2_long1 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short2_long1 a b
    short2_long2 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_short, positiveRoots_long] using h.short2_long2 a b
    long1_long2 a b := by
      obtain ⟨a, rfl⟩ := e.fixed.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [positiveRoots_long] using h.long1_long2 a b
  }
  shortExchange := {
    short0_long0 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.fixed.surjective b
      simpa only [fixed_coe, ← e.frobenius, ← e.extension.map_mul,
        ← e.fixed_norm, ← e.fixed.map_mul, positiveRoots_short, positiveRoots_long] using h.short0_long0 a b
    short0_short1 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.extension.surjective b
      simpa only [← e.frobenius, ← e.extension.map_mul,
        ← e.higher, ← e.fixed_trace, positiveRoots_short, positiveRoots_long] using h.short0_short1 a b
    short0_short2 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.extension.surjective b
      simpa only [← e.frobenius, ← e.extension.map_mul,
        ← e.fixed_trace, positiveRoots_short, positiveRoots_long] using h.short0_short2 a b
    short1_short2 a b := by
      obtain ⟨a, rfl⟩ := e.extension.surjective a
      obtain ⟨b, rfl⟩ := e.extension.surjective b
      simpa only [← e.frobenius, ← e.extension.map_mul,
        ← e.fixed_trace, positiveRoots_short, positiveRoots_long] using h.short1_short2 a b
  }
  longExchange a b := by
    obtain ⟨a, rfl⟩ := e.fixed.surjective a
    obtain ⟨b, rfl⟩ := e.fixed.surjective b
    simpa only [← e.fixed.map_mul, positiveRoots_long] using h.long0_long1 a b

end ScalarMarking
end Triality.Standard.RootPresentationRecognition
