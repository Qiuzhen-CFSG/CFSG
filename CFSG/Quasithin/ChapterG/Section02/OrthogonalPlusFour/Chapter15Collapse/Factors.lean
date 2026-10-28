module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Modules
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.LinearAlgebra.Projection
/-!
# The actual residual factors and natural sums in 15.3.54

The source actors are Nᵢ, the preimages of the ordered S₃ factors, and
Yᵢ = O²(Y ∩ Nᵢ). Transport of the residual through the literal quotient
map shows its image contains the corresponding cubic. On a sum of binary
natural planes, cubic displacement is surjective, so [P/V,Yᵢ] is exactly
that summand. The opposite N-factor fixes the same space.

The finite sums and the relative quotient are related by actual equivariant
isomorphisms. The common multiplicity is explicitly supplied by full
G.2.6(5); the separate multiplicities of general product recognition do not
prove it. Zero multiplicity is allowed. The consumer in Chapter15Collapse
constructs the P/V section by proving the central middle-layer collapse.

Source: Aschbacher–Smith, G.2.6(5), printed p.336/PDF p.347, and
15.3.53–54, printed pp.1145–1146/PDF pp.1162–1163.
-/

@[expose] public section
open scoped IsMulCommutative
open Subgroup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G]

/-- The literal preimage in the acting group, embedded in the ambient group. -/
def actorPreimage {I : Subgroup G} (π : I →* S₃ × S₃) (K : Subgroup (S₃ × S₃)) :
    Subgroup G := (K.comap π).map I.subtype

/-- O²(Y ∩ Nᵢ), with the residual taken inside the intersection. -/
def oddFactor {I : Subgroup G} (π : I →* S₃ × S₃) (Y : Subgroup G)
    (K : Subgroup (S₃ × S₃)) : Subgroup G :=
  (pResidual 2 (Y ⊓ actorPreimage π K : Subgroup G)).map (Y ⊓ actorPreimage π K).subtype

theorem actorPreimage_le {I : Subgroup G} (π : I →* S₃ × S₃) (K : Subgroup (S₃ × S₃)) :
    actorPreimage π K ≤ I := by
  rintro x ⟨a, _, rfl⟩
  exact a.property

theorem oddFactor_le {I : Subgroup G} (π : I →* S₃ × S₃) (Y : Subgroup G)
    (K : Subgroup (S₃ × S₃)) : oddFactor π Y K ≤ actorPreimage π K := by
  rintro x ⟨a, _, rfl⟩
  exact a.property.2

theorem oddFactor_image [Finite G] {I : Subgroup G} (π : I →* S₃ × S₃) (Y : Subgroup G)
    (hYI : Y ≤ I) (K : Subgroup (S₃ × S₃)) :
    ((oddFactor π Y K).subgroupOf I).map π =
      (pResidual 2 (((Y.subgroupOf I).map π) ⊓ K : Subgroup (S₃ × S₃))).map
        (((Y.subgroupOf I).map π) ⊓ K).subtype := by
  let C := Y.subgroupOf I ⊓ K.comap π
  have hC : C.map I.subtype = Y ⊓ actorPreimage π K := by
    rw [map_inf _ _ _ I.subtype_injective, map_subgroupOf_eq_of_le hYI]
    rfl
  have he : oddFactor π Y K = ((pResidual 2 C).map C.subtype).map I.subtype := by
    rw [map_embedded_pResidual, hC]
    rfl
  rw [he, subgroupOf, comap_map_eq_self_of_injective I.subtype_injective,
    map_embedded_pResidual]
  have hm : C.map π = (Y.subgroupOf I).map π ⊓ K := by
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      exact ⟨mem_map_of_mem π ha.1, ha.2⟩
    · rintro x ⟨⟨a, ha, rfl⟩, hk⟩
      exact mem_map_of_mem π ⟨ha, hk⟩
  rw [hm]

variable {M : Type*} [AddCommGroup M] [Module F M]

private theorem natural_cubic_displacement (n : BinaryPermutation.core (Fin 3)) :
    BinaryPermutation.coreRepresentation (Fin 3) cubic
      (BinaryPermutation.coreRepresentation (Fin 3) cubic n) -
        BinaryPermutation.coreRepresentation (Fin 3) cubic n = n := by
  apply Subtype.ext
  simp only [Submodule.coe_sub, BinaryPermutation.coreRepresentation_apply]
  have h : ∀ x : Fin 3 → ZMod 2, (∑ i, x i) = 0 → ∀ i,
      x (cubic.symm (cubic.symm i)) - x (cubic.symm i) = x i := by decide +kernel
  exact funext (h n.val n.property)

/-- A subgroup containing the first cubic and contained in the first factor
has exactly the first natural summand as its displacement space. -/
theorem left_cubic_commutator {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (K : Subgroup (S₃ × S₃))
    (hK : K ≤ ProductDecomposition.leftFactor) (hc : (cubic, 1) ∈ K) :
    subspaceCommutator σ ⊤ K = r.left.toSubmodule := by
  apply le_antisymm
  · rw [r.left_commutator]
    apply Submodule.span_mono
    rintro v ⟨a, ha, w, hw, he⟩
    exact ⟨a, hK ha, w, hw, he⟩
  · intro v hv
    obtain ⟨x, hx⟩ := r.leftEquiv.surjective ⟨v, hv⟩
    have he (x) : (r.leftEquiv (fun j =>
        BinaryPermutation.coreRepresentation (Fin 3) cubic (x j)) : M) =
        σ (cubic, 1) (r.leftEquiv x) :=
      congrArg (fun w : r.left.toSubmodule => (w : M)) (r.left_equivariant (cubic, 1) x)
    have hv' : σ (cubic, 1) (σ (cubic, 1) v) - σ (cubic, 1) v = v := by
      rw [← show (r.leftEquiv x : M) = v from congrArg Subtype.val hx,
        ← he, ← he]
      rw [← Submodule.coe_sub, ← map_sub]
      congr 2
      funext j
      exact natural_cubic_displacement (x j)
    exact Submodule.subset_span ⟨(cubic, 1), hc, σ (cubic, 1) v, Submodule.mem_top, hv'.symm⟩

/-- The corresponding displacement calculation for the second natural factor. -/
theorem right_cubic_commutator {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (K : Subgroup (S₃ × S₃))
    (hK : K ≤ ProductDecomposition.rightFactor) (hc : (1, cubic) ∈ K) :
    subspaceCommutator σ ⊤ K = r.right.toSubmodule := by
  apply le_antisymm
  · rw [r.right_commutator]
    apply Submodule.span_mono
    rintro v ⟨a, ha, w, hw, he⟩
    exact ⟨a, hK ha, w, hw, he⟩
  · intro v hv
    obtain ⟨x, hx⟩ := r.rightEquiv.surjective ⟨v, hv⟩
    have he (x) : (r.rightEquiv (fun j =>
        BinaryPermutation.coreRepresentation (Fin 3) cubic (x j)) : M) =
        σ (1, cubic) (r.rightEquiv x) :=
      congrArg (fun w : r.right.toSubmodule => (w : M)) (r.right_equivariant (1, cubic) x)
    have hv' : σ (1, cubic) (σ (1, cubic) v) - σ (1, cubic) v = v := by
      rw [← show (r.rightEquiv x : M) = v from congrArg Subtype.val hx,
        ← he, ← he]
      rw [← Submodule.coe_sub, ← map_sub]
      congr 2
      funext j
      exact natural_cubic_displacement (x j)
    exact Submodule.subset_span ⟨(1, cubic), hc, σ (1, cubic) v, Submodule.mem_top, hv'.symm⟩

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

@[expose] public section
open Subgroup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G]
variable {I P B : Subgroup G} {M : Type*} [AddCommGroup M] [Module F M]

theorem mem_oddFactor_image_of_cube [Finite G]
    (π : I →* S₃ × S₃) (Y : Subgroup G) (hYI : Y ≤ I)
    (K : Subgroup (S₃ × S₃)) (a : S₃ × S₃)
    (ha : a ∈ (Y.subgroupOf I).map π ⊓ K) (h3 : a ^ 3 = 1) :
    a ∈ ((oddFactor π Y K).subgroupOf I).map π := by
  rw [oddFactor_image π Y hYI K]
  refine ⟨⟨a, ha⟩, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (show Nat.Coprime 2 3 by decide).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show (⟨a, ha⟩ : ((Y.subgroupOf I).map π ⊓ K : Subgroup (S₃ × S₃))) ^ 3 = 1
      from Subtype.ext h3))

theorem oddFactor_image_le (π : I →* S₃ × S₃) (Y : Subgroup G)
    (K : Subgroup (S₃ × S₃)) : ((oddFactor π Y K).subgroupOf I).map π ≤ K := by
  rintro x ⟨a, ha, rfl⟩
  obtain ⟨b, hb, he⟩ := oddFactor_le π Y K ha
  have he' : b = a := Subtype.ext he
  exact he' ▸ hb

/-- Displacement under any actual subgroup equals its commutator quotient image. -/
theorem section_commutator_image (π : I →* S₃ × S₃)
    (σ : Representation F (S₃ × S₃) M)
    (c : Representation.BinaryConjugationSection I P B (σ.comp π))
    (X : Subgroup G) (hXI : X ≤ I) :
    c.imageSpace ⁅P, X⁆ = subspaceCommutator σ ⊤ ((X.subgroupOf I).map π) := by
  let f := π.comp (inclusion hXI)
  have hr : f.range = (X.subgroupOf I).map π := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_map_of_mem π x.property
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  let : Module F (Additive (Multiplicative M)) := inferInstanceAs (Module F M)
  have hh := commutator_image_eq (Q := Multiplicative M) σ P P X
    (hXI.trans c.normalized) le_rfl f c.coordinates
    (by intro x p; exact (c.equivariant (inclusion hXI x) p).symm)
    (⊤ : Submodule F M) (by
      rw [subgroupOf_self, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr c.onto]
      rfl)
  rw [hr] at hh
  ext v
  change Multiplicative.ofAdd v ∈ (⁅P, X⁆.subgroupOf P).map c.coordinates ↔ _
  rw [hh]
  rfl

/-- The literal residual Yᵢ, rather than the full S₃ factor, moves exactly
its own natural summand. -/
theorem source_oddFactor_modules [Finite G] (π : I →* S₃ × S₃)
    (Y : Subgroup G) (hYI : Y ≤ I)
    (hY : (Y.subgroupOf I).map π =
      (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)))
    (σ : Representation F (S₃ × S₃) M)
    (c : Representation.BinaryConjugationSection I P B (σ.comp π))
    (r : ProductDecomposition σ) :
    c.imageSpace ⁅P, oddFactor π Y ProductDecomposition.leftFactor⁆ = r.left.toSubmodule ∧
    c.imageSpace ⁅P, oddFactor π Y ProductDecomposition.rightFactor⁆ = r.right.toSubmodule := by
  have hl := mem_oddFactor_image_of_cube π Y hYI ProductDecomposition.leftFactor
    (cubic, 1) (by
      rw [hY]
      simp only [ProductDecomposition.leftFactor,
        mem_inf, mem_prod, mem_top, mem_bot, and_true,
        Equiv.Perm.mem_alternatingGroup]
      decide +kernel) (by decide +kernel)
  have hr := mem_oddFactor_image_of_cube π Y hYI ProductDecomposition.rightFactor
    (1, cubic) (by
      rw [hY]
      simp only [ProductDecomposition.rightFactor,
        mem_inf, mem_prod, mem_top, mem_bot, and_true,
        Equiv.Perm.mem_alternatingGroup]
      decide +kernel) (by decide +kernel)
  constructor
  · rw [section_commutator_image π σ c _
      ((oddFactor_le π Y _).trans (actorPreimage_le π _))]
    exact left_cubic_commutator r _ (oddFactor_image_le π Y _) hl
  · rw [section_commutator_image π σ c _
      ((oddFactor_le π Y _).trans (actorPreimage_le π _))]
    exact right_cubic_commutator r _ (oddFactor_image_le π Y _) hr

/-- The opposite literal preimage fixes exactly the opposite model factor's fixed space. -/
theorem actorPreimage_fixed (π : I →* S₃ × S₃) (hπ : Function.Surjective π)
    (σ : Representation F (S₃ × S₃) M) (K : Subgroup (S₃ × S₃)) :
    fixedSpace (σ.comp π) ((actorPreimage π K).subgroupOf I) = fixedSpace σ K := by
  rw [fixedSpace_comp_map]
  congr 1
  rw [actorPreimage, subgroupOf, comap_map_eq_self_of_injective I.subtype_injective]
  exact map_comap_eq_self_of_surjective hπ K

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

@[expose] public section
open Subgroup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- Reindex the second natural sum by the common printed multiplicity.
Equality of the multiplicities is retained as a full G.2.6 premise. -/
def commonRightEquiv {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity) :
    (Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3)) ≃ₗ[F] r.right.toSubmodule :=
  (LinearEquiv.piCongrLeft F (fun _ => BinaryPermutation.core (Fin 3))
    (finCongr h)).trans r.rightEquiv

theorem commonRightEquiv_equivariant {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity)
    (a : S₃ × S₃) (x : Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3)) :
    commonRightEquiv r h (fun j => BinaryPermutation.coreRepresentation (Fin 3) a.2 (x j)) =
      r.right.toRepresentation a (commonRightEquiv r h x) := by
  exact r.right_equivariant a _

/-- The two sums with the same index set, retaining the ordered actors. -/
noncomputable def commonSumEquiv {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity) :
    (Fin 2 → Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3)) ≃ₗ[F] M :=
  (LinearEquiv.piFinTwo F (fun _ => Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3))).trans
    ((r.leftEquiv.prodCongr (commonRightEquiv r h)).trans
      (Submodule.prodEquivOfIsCompl _ _ r.complementary))

theorem commonSumEquiv_equivariant {σ : Representation F (S₃ × S₃) M}
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity)
    (a : S₃ × S₃) (x : Fin 2 → Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3)) :
    commonSumEquiv r h (fun i j => BinaryPermutation.coreRepresentation (Fin 3)
      (if i = 0 then a.1 else a.2) (x i j)) = σ a (commonSumEquiv r h x) := by
  change (r.leftEquiv (fun j => BinaryPermutation.coreRepresentation (Fin 3)
      (if (0 : Fin 2) = 0 then a.1 else a.2) (x 0 j)) : M) +
    (commonRightEquiv r h (fun j => BinaryPermutation.coreRepresentation (Fin 3)
      (if (1 : Fin 2) = 0 then a.1 else a.2) (x 1 j)) : M) = _
  simp only [ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false,
    r.left_equivariant, commonRightEquiv_equivariant]
  exact (map_add (σ a) _ _).symm

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

@[expose] public section
open Subgroup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G] {I P B : Subgroup G}
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- The common finite-sum coordinates on the literal relative quotient. -/
noncomputable def commonQuotientEquiv {π : I →* S₃ × S₃}
    {σ : Representation F (S₃ × S₃) M}
    (c : Representation.BinaryConjugationSection I P B (σ.comp π))
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity)
    [(B.subgroupOf P).Normal] :
    (P ⧸ B.subgroupOf P) ≃*
      Multiplicative (Fin 2 → Fin r.leftMultiplicity → BinaryPermutation.core (Fin 3)) :=
  c.quotientEquiv.trans (commonSumEquiv r h).symm.toAddEquiv.toMultiplicative

theorem commonQuotientEquiv_mk {π : I →* S₃ × S₃}
    {σ : Representation F (S₃ × S₃) M}
    (c : Representation.BinaryConjugationSection I P B (σ.comp π))
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity)
    [(B.subgroupOf P).Normal] (p : P) :
    (commonQuotientEquiv c r h (QuotientGroup.mk' (B.subgroupOf P) p)).toAdd =
      (commonSumEquiv r h).symm (c.coordinates p).toAdd := rfl

/-- These quotient coordinates intertwine the actual ambient conjugation and
the two specified binary natural actions, including at multiplicity zero. -/
theorem commonQuotientEquiv_conjugation {π : I →* S₃ × S₃}
    {σ : Representation F (S₃ × S₃) M}
    (c : Representation.BinaryConjugationSection I P B (σ.comp π))
    (r : ProductDecomposition σ) (h : r.leftMultiplicity = r.rightMultiplicity)
    [(B.subgroupOf P).Normal] (i : I) (p : P) :
    (commonQuotientEquiv c r h (QuotientGroup.mk' (B.subgroupOf P)
      ⟨(i : G) * p * (i : G)⁻¹,
        le_normalizer_iff.mp c.normalized i i.property p p.property⟩)).toAdd =
      fun k j => BinaryPermutation.coreRepresentation (Fin 3)
        (if k = 0 then (π i).1 else (π i).2)
        ((commonQuotientEquiv c r h (QuotientGroup.mk' (B.subgroupOf P) p)).toAdd k j) := by
  apply (commonSumEquiv r h).injective
  rw [commonQuotientEquiv_mk, LinearEquiv.apply_symm_apply,
    commonSumEquiv_equivariant, commonQuotientEquiv_mk,
    LinearEquiv.apply_symm_apply]
  exact c.equivariant i p

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse

@[expose] public section
open Subgroup InvertedCubicTensor
open Representation.BinaryOffender Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
variable {G : Type*} [Group G]
variable {M : Type*} [AddCommGroup M] [Module F M]

/-- Clause 15.3.54(4) on the literal P/V conjugation section. The summands
are both residual commutator images and opposite-factor fixed spaces.
The two finite sums have the same nonnegative multiplicity. -/
structure FactorModuleConclusion (I P V Y : Subgroup G)
    (π : I →* S₃ × S₃) (σ : Representation F (S₃ × S₃) M) where
  conjugation : Representation.BinaryConjugationSection I P V (σ.comp π)
  decomposition : ProductDecomposition σ
  sameMultiplicity : decomposition.leftMultiplicity = decomposition.rightMultiplicity
  left_residual : conjugation.imageSpace ⁅P, oddFactor π Y ProductDecomposition.leftFactor⁆ =
    decomposition.left.toSubmodule
  right_residual : conjugation.imageSpace ⁅P, oddFactor π Y ProductDecomposition.rightFactor⁆ =
    decomposition.right.toSubmodule
  left_fixed : decomposition.left.toSubmodule = fixedSpace (σ.comp π)
    ((actorPreimage π ProductDecomposition.rightFactor).subgroupOf I)
  right_fixed : decomposition.right.toSubmodule = fixedSpace (σ.comp π)
    ((actorPreimage π ProductDecomposition.leftFactor).subgroupOf I)

variable {I P V Y : Subgroup G} {π : I →* S₃ × S₃}
  {σ : Representation F (S₃ × S₃) M}

/-- The commutator descriptions are complementary inside the actual quotient. -/
theorem FactorModuleConclusion.complementary (f : FactorModuleConclusion I P V Y π σ) :
    IsCompl (f.conjugation.imageSpace ⁅P, oddFactor π Y ProductDecomposition.leftFactor⁆)
      (f.conjugation.imageSpace ⁅P, oddFactor π Y ProductDecomposition.rightFactor⁆) := by
  rw [f.left_residual, f.right_residual]
  exact f.decomposition.complementary

/-- Actual quotient coordinates, including the common printed multiplicity.
The action equation is `commonQuotientEquiv_conjugation`. -/
noncomputable def FactorModuleConclusion.quotientEquiv
    (f : FactorModuleConclusion I P V Y π σ) :
    letI := f.conjugation.kernel_normal
    (P ⧸ V.subgroupOf P) ≃*
      Multiplicative (Fin 2 → Fin f.decomposition.leftMultiplicity →
        BinaryPermutation.core (Fin 3)) :=
  letI := f.conjugation.kernel_normal
  commonQuotientEquiv f.conjugation f.decomposition f.sameMultiplicity

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15Collapse
