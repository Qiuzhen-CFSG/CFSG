module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Theory.AlgebraicGroup.ClosedSubgroup.Invariant
public import Theory.AlgebraicGroup.CoordinateRing.FiniteTranslate
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Tensor

universe u v

/-! The augmentation ideal of the normal right-invariant coordinate ring. -/

/-! Finite-type subalgebras stable under the coordinate Hopf operations. -/

namespace Theory.AlgebraicGroup

section
open scoped TensorProduct

variable {k : Type u} [Field k]

lemma exists_finiteType_coordinateHopfStableSubalgebra
    (G : Variety k) [AlgebraicGroup G]
    (t : Finset (Variety.PolynomialFunction G)) :
    ∃ C : Subalgebra k (Variety.PolynomialFunction G),
      Algebra.FiniteType k C ∧
      (↑t : Set (Variety.PolynomialFunction G)) ⊆ C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  obtain ⟨C, hCfinite, htC, hleft, hright, hantipode⟩ :=
    AlgebraicGroup.exists_finiteType_translate_antipode_stableSubalgebra G t
  refine ⟨C, hCfinite, htC, hleft, hright, hantipode, ?_⟩
  intro q hq
  exact AlgebraicGroup.exists_tensorSubalgebra_comultiplication_of_translate_stable
    G C hleft hright q hq

end

public lemma Ideal.exists_finset_map_span_eq_of_map_fg
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (h : (I.map f).FG) :
    ∃ t : Finset R, (↑t : Set R) ⊆ I ∧
      Ideal.map f (Ideal.span (t : Set R)) = I.map f := by
  classical
  have hc : IsCompactElement (I.map f) :=
    (Submodule.fg_iff_compact (I.map f)).mp h
  have hle : I.map f ≤ ⨆ x : I, Ideal.span ({f x.val} : Set S) := by
    rw [Ideal.map, Ideal.span_le]
    rintro y ⟨x, hx, rfl⟩
    exact (le_iSup (fun x : I => Ideal.span ({f x.val} : Set S))
      (⟨x, hx⟩ : I)) (Ideal.subset_span (Set.mem_singleton _))
  obtain ⟨s, hs⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup
    (Ideal S) hc (fun x : I => Ideal.span ({f x.val} : Set S)) hle
  let t : Finset R := s.image Subtype.val
  have htI : (↑t : Set R) ⊆ I := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, -, rfl⟩
    exact y.property
  refine ⟨t, htI, ?_⟩
  apply le_antisymm
  · apply Ideal.map_mono
    rw [Ideal.span_le]
    exact htI
  · refine hs.trans ?_
    rw [iSup_le_iff]
    intro x
    rw [iSup_le_iff]
    intro hx
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.mem_map_of_mem
    apply Ideal.subset_span
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem Subtype.val hx)

/-! The coordinate counit restricted to right-invariants. -/

section
variable {k : Type u} [Field k]

@[expose]
public noncomputable def rightInvariantCoordinateAugmentationIdeal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Ideal (AlgebraicGroup.rightInvariantCoordinateRing H) :=
  RingHom.ker (AlgebraicGroup.rightInvariantCoordinateCounit H).toRingHom

end

/-! Finite generation after extending the invariant augmentation ideal to the ambient ring. -/

section
variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_map_fg
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (Ideal.map
      (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
        (Variety.PolynomialFunction G))
      (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H)).FG := by
  let : Algebra.FiniteType k (Variety.PolynomialFunction G) :=
    polynomialFunction_finiteType G
  let : IsNoetherianRing (Variety.PolynomialFunction G) :=
    Algebra.FiniteType.isNoetherianRing k (Variety.PolynomialFunction G)
  exact Ideal.fg_of_isNoetherianRing _

end

/-! Finite source generators for the extended invariant augmentation ideal. -/

section

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteSourceGenerators_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) =
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) := by
  exact Ideal.exists_finset_map_span_eq_of_map_fg
    (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
      (Variety.PolynomialFunction G))
    (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H)
    (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_map_fg H)

end

/-! A finite Hopf-stable ambient localization of invariant augmentation generators. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteHopfLocalization_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H))
      (C : Subalgebra k (Variety.PolynomialFunction G)),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      (∀ f ∈ t, (f.1 : Variety.PolynomialFunction G) ∈ C) ∧
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) =
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ∧
      Algebra.FiniteType k C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  classical
  obtain ⟨t, ht, hmap⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteSourceGenerators_exists H
  obtain ⟨C, hCfinite, htC, hleft, hright, hantipode, hcomul⟩ :=
    AlgebraicGroup.exists_finiteType_coordinateHopfStableSubalgebra G
      (t.image fun f => f.1)
  refine ⟨t, C, ht, ?_, hmap, hCfinite, hleft, hright, hantipode, hcomul⟩
  intro f hf
  apply htC
  simp only [Finset.coe_image, Set.mem_image]
  exact ⟨f, hf, rfl⟩

end

/-! Finite augmentation generators in the localized invariant intersection. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteHopfInvariantLocalization_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H))
      (C : Subalgebra k (Variety.PolynomialFunction G))
      (r : Finset ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H)),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      ((fun q : ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H) =>
          (q.1 : Variety.PolynomialFunction G)) ''
        (r : Set ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H))) =
        ((algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G)) ''
          (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) ∧
      Ideal.map (C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H).val.toRingHom
          (Ideal.span (r : Set ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H))) =
        Ideal.map
          (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
            (Variety.PolynomialFunction G))
          (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ∧
      Algebra.FiniteType k C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  classical
  obtain ⟨t, C, ht, htC, hmap, hCfinite, hleft, hright, hantipode, hcomul⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteHopfLocalization_exists H
  let lift : ↥t → ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H) :=
    fun f => ⟨f.1.1, htC f.1 f.2, f.1.2⟩
  let r : Finset ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H) :=
    t.attach.image lift
  have hrimage :
      ((fun q : ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H) =>
          (q.1 : Variety.PolynomialFunction G)) ''
        (r : Set ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H))) =
        ((algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G)) ''
          (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) := by
    ext q
    constructor
    · rintro ⟨qD, hqD, rfl⟩
      simp only [r, Finset.coe_image, Set.mem_image] at hqD
      obtain ⟨f, hf, rfl⟩ := hqD
      exact ⟨f.1, f.2, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      refine ⟨lift ⟨f, hf⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩
      · rfl
  refine ⟨t, C, r, ht, hrimage, ?_, hCfinite, hleft, hright, hantipode, hcomul⟩
  rw [Ideal.map_span]
  change Ideal.span
    ((fun q : ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H) =>
      (q.1 : Variety.PolynomialFunction G)) ''
      (r : Set ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H))) = _
  rw [hrimage, ← Ideal.map_span, hmap]

end
/-! Factoring ideal extension through one side of a subalgebra intersection. -/

section

variable {k : Type u} [CommSemiring k]
variable {A : Type v} [CommSemiring A] [Algebra k A]

public lemma Ideal.map_subalgebra_inf_eq_map_map_left
    (C B : Subalgebra k A) (I : Ideal ↥(C ⊓ B)) :
    Ideal.map (C ⊓ B).val.toRingHom I =
      Ideal.map C.val.toRingHom
        (Ideal.map (Subalgebra.inclusion inf_le_left).toRingHom I) := by
  rw [Ideal.map_map]
  congr 1

end
/-! An actual finite Hopf-algebra localization of invariant augmentation generators. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteHopfAlgebraLocalization_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H))
      (C : Subalgebra k (Variety.PolynomialFunction G)),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      (∀ f ∈ t, (f.1 : Variety.PolynomialFunction G) ∈ C) ∧
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) =
      Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ∧
      Algebra.FiniteType k C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      Nonempty (HopfAlgebra k C) := by
  obtain ⟨t, C, ht, htC, hmap, hCfinite, hleft, hright, hantipode, hcomul⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteHopfLocalization_exists H
  exact ⟨t, C, ht, htC, hmap, hCfinite, hleft, hright,
    ⟨AlgebraicGroup.coordinateSubalgebraHopfAlgebra G C hcomul hantipode⟩⟩

end

/-! Factoring the localized invariant augmentation ideal through the finite Hopf algebra. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteHopfInvariantIdealFactorization_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ (C : Subalgebra k (Variety.PolynomialFunction G))
      (r : Finset ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H)),
      Ideal.map C.val.toRingHom
          (Ideal.map
            (Subalgebra.inclusion
              (show C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H ≤ C from inf_le_left)).toRingHom
            (Ideal.span (r : Set ↥(C ⊓ AlgebraicGroup.rightInvariantCoordinateRing H)))) =
        Ideal.map
          (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
            (Variety.PolynomialFunction G))
          (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ∧
      Algebra.FiniteType k C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  obtain ⟨t, C, r, ht, hrimage, hmap, hCfinite, hleft, hright, hantipode, hcomul⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteHopfInvariantLocalization_exists H
  refine ⟨C, r, ?_, hCfinite, hleft, hright, hantipode, hcomul⟩
  rw [← Ideal.map_subalgebra_inf_eq_map_map_left]
  exact hmap

end

/-! A finite ideal inside the finite Hopf-stable ambient localization. -/

section
open scoped TensorProduct

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteHopfLocalizedIdeal_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ (t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H))
      (C : Subalgebra k (Variety.PolynomialFunction G)) (s : Finset C),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      ((fun q : C => (q.1 : Variety.PolynomialFunction G)) '' (s : Set C)) =
        ((algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G)) ''
          (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) ∧
      Ideal.map C.val.toRingHom (Ideal.span (s : Set C)) =
        Ideal.map
          (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
            (Variety.PolynomialFunction G))
          (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ∧
      Algebra.FiniteType k C ∧
      (∀ a q, q ∈ C →
        (AlgebraicGroup.leftMulMorphism G a).pullbackAlgHom q ∈ C) ∧
      (∀ b q, q ∈ C →
        (AlgebraicGroup.rightMulMorphism G b).pullbackAlgHom q ∈ C) ∧
      (∀ q, q ∈ C → AlgebraicGroup.coordinateAntipode G q ∈ C) ∧
      (∀ q, q ∈ C → ∃ w : C ⊗[k] C,
        TensorProduct.map C.toSubmodule.subtype C.toSubmodule.subtype w =
          AlgebraicGroup.coordinateComultiplication G q) := by
  classical
  obtain ⟨t, C, ht, htC, hmap, hCfinite, hleft, hright, hantipode, hcomul⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteHopfLocalization_exists H
  let lift : ↥t → C := fun f => ⟨f.1.1, htC f.1 f.2⟩
  let s : Finset C := t.attach.image lift
  have hsimage :
      ((fun q : C => (q.1 : Variety.PolynomialFunction G)) '' (s : Set C)) =
        ((algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G)) ''
          (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H))) := by
    ext q
    constructor
    · rintro ⟨qC, hqC, rfl⟩
      simp only [s, Finset.coe_image, Set.mem_image] at hqC
      obtain ⟨f, hf, rfl⟩ := hqC
      exact ⟨f.1, f.2, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      refine ⟨lift ⟨f, hf⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩
      · rfl
  refine ⟨t, C, s, ht, hsimage, ?_, hCfinite, hleft, hright, hantipode, hcomul⟩
  rw [Ideal.map_span]
  change Ideal.span ((fun q : C => (q.1 : Variety.PolynomialFunction G)) '' (s : Set C)) = _
  rw [hsimage, ← Ideal.map_span, hmap]

end

/-! Extension and contraction of the invariant augmentation ideal. -/

section

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_comap_map
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (Ideal.map
      (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
        (Variety.PolynomialFunction G))
      (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H)).comap
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G)) =
      AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H := by
  apply le_antisymm
  · intro x hx
    change AlgebraicGroup.rightInvariantCoordinateCounit H x = 0
    have hle : Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ≤
        RingHom.ker (AlgebraicGroup.coordinateCounit G).toRingHom := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      change AlgebraicGroup.coordinateCounit G y.val = 0
      change AlgebraicGroup.rightInvariantCoordinateCounit H y = 0 at hy
      exact hy
    have hx' := hle hx
    change AlgebraicGroup.coordinateCounit G x.val = 0 at hx'
    exact hx'
  · exact Ideal.le_comap_map

end

/-! A finite invariant ideal whose ambient extension contracts to the augmentation ideal. -/

section

variable {k : Type u} [Field k]

public lemma rightInvariantCoordinateAugmentationIdeal_finiteSpan_comap_map_exists
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    ∃ t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      (Ideal.map
        (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
          (Variety.PolynomialFunction G))
        (Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)))).comap
          (algebraMap (AlgebraicGroup.rightInvariantCoordinateRing H)
            (Variety.PolynomialFunction G)) =
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H := by
  obtain ⟨t, ht, hmap⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteSourceGenerators_exists H
  refine ⟨t, ht, ?_⟩
  rw [hmap, AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_comap_map]

end

/-! Finite generation of the invariant augmentation ideal under faithful flatness. -/

section

variable {k : Type u} [Field k]

/-- Faithful flatness turns the finite ambient extension-contraction package
into finite generators for the invariant augmentation ideal itself. -/
public lemma rightInvariantCoordinateAugmentationIdeal_eq_finiteSpan_of_faithfullyFlat
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    [Module.FaithfullyFlat
      (AlgebraicGroup.rightInvariantCoordinateRing H)
      (Variety.PolynomialFunction G)] :
    ∃ t : Finset (AlgebraicGroup.rightInvariantCoordinateRing H),
      (↑t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) ⊆
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ∧
      Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)) =
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H := by
  obtain ⟨t, ht, hcontract⟩ :=
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal_finiteSpan_comap_map_exists H
  have hpure := Ideal.comap_map_eq_self_of_faithfullyFlat
    (B := Variety.PolynomialFunction G)
    (Ideal.span (t : Set (AlgebraicGroup.rightInvariantCoordinateRing H)))
  rw [hpure] at hcontract
  exact ⟨t, ht, hcontract⟩

end

section

variable {k : Type u} [Field k]

/-- The invariant-coordinate counit is surjective because every scalar is the
image of the corresponding constant polynomial. -/
public lemma rightInvariantCoordinateCounit_surjective
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Function.Surjective (AlgebraicGroup.rightInvariantCoordinateCounit H) := by
  let ε := AlgebraicGroup.rightInvariantCoordinateCounit H
  intro c
  refine ⟨algebraMap k _ c, ?_⟩
  exact ε.commutes c

end

section

variable {k : Type u} [Field k]

/-- The invariant-coordinate augmentation ideal is maximal because it is the
kernel of the counit, a surjective `k`-algebra homomorphism onto the field. -/
public lemma rightInvariantCoordinateAugmentationIdeal_isMaximal
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H).IsMaximal := by
  let ε := AlgebraicGroup.rightInvariantCoordinateCounit H
  exact RingHom.ker_isMaximal_of_surjective ε.toRingHom
    (rightInvariantCoordinateCounit_surjective H)

end

section

variable {k : Type u} [Field k]

/-- The invariant-coordinate augmentation ideal is prime, since it is
maximal. -/
public lemma rightInvariantCoordinateAugmentationIdeal_isPrime
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    (AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H).IsPrime :=
  (rightInvariantCoordinateAugmentationIdeal_isMaximal H).isPrime

end

section
variable {k : Type u} [Field k]

/-- The invariant-coordinate augmentation ideal is a proper ideal, since it
is maximal. -/
public lemma rightInvariantCoordinateAugmentationIdeal_ne_top
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H ≠ ⊤ :=
  (rightInvariantCoordinateAugmentationIdeal_isMaximal H).ne_top

end

section

variable {k : Type u} [Field k]

/-- Quotienting the invariant-coordinate ring by its augmentation ideal gives
the base field, via the surjective counit. -/
public lemma rightInvariantCoordinateAugmentationIdeal_quotient_eq_k
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Nonempty
      ((AlgebraicGroup.rightInvariantCoordinateRing H ⧸
        AlgebraicGroup.rightInvariantCoordinateAugmentationIdeal H) ≃ₐ[k] k) := by
  let ε := AlgebraicGroup.rightInvariantCoordinateCounit H
  exact ⟨Ideal.quotientKerAlgEquivOfSurjective (f := ε)
    (rightInvariantCoordinateCounit_surjective H)⟩

end

section
variable {k : Type u} [Field k]

/-- The invariant-coordinate counit maps a constant to that constant. -/
public lemma rightInvariantCoordinateCounit_algebraMap
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) (c : k) :
    AlgebraicGroup.rightInvariantCoordinateCounit H (algebraMap k _ c) = c :=
  (AlgebraicGroup.rightInvariantCoordinateCounit H).commutes c

end
end Theory.AlgebraicGroup
