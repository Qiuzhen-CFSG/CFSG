module

public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.NormalJoinQuotientProduct
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Representation.BinaryQuadraticPair

/-!
# Subgroup images in an actual binary conjugation section

The coordinate homomorphism of a BinaryConjugationSection sends literal
subgroups to binary subspaces. Killing exactly an intersection makes two
generating subgroup images complementary. Equivariance transports conjugate
images and identifies commutator coordinates with linear displacement.
Neither finite dimension nor normality of the two summands is needed.

These are the quotient bridges for the binary quadratic-pair criterion in
Aschbacher--Smith G.2.3(6), used in 12.8.9(2)--(3), printed pp.334 and 853.
-/

@[expose] public section

namespace Representation.BinaryConjugationSection

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H S E ρ)

/-- The image of a literal subgroup under the supplied coordinate quotient. -/
def imageSpace (B : Subgroup G) : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2 ((B.subgroupOf S).map d.coordinates).toAddSubgroup'

/-- Image membership retains a representative in the original quotient domain. -/
theorem mem_imageSpace_iff (B : Subgroup G) (v : W) :
    v ∈ d.imageSpace B ↔
      ∃ b : S, (b : G) ∈ B ∧ (d.coordinates b).toAdd = v := by
  change Multiplicative.ofAdd v ∈ (B.subgroupOf S).map d.coordinates ↔ _
  constructor
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, congrArg Multiplicative.toAdd he⟩
  · rintro ⟨b, hb, he⟩
    exact ⟨b, hb, Multiplicative.toAdd.injective he⟩

/-- Inclusion of the literal subgroups gives inclusion of their quotient images. -/
theorem imageSpace_mono {B C : Subgroup G} (hBC : B ≤ C) :
    d.imageSpace B ≤ d.imageSpace C := by
  intro v hv
  obtain ⟨b, hb, he⟩ := (d.mem_imageSpace_iff B v).mp hv
  exact (d.mem_imageSpace_iff C v).mpr ⟨b, hBC hb, he⟩

/-- The original subgroup join and intersection give complementary quotient
images, without assuming either subgroup normal. -/
theorem isCompl_imageSpace (B C : Subgroup G)
    (hS : S = B ⊔ C) (hE : E = B ⊓ C) :
    IsCompl (d.imageSpace B) (d.imageSpace C) := by
  let f : Subgroup (Multiplicative W) ≃o Submodule (ZMod 2) W :=
    Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2)
  have hk : d.coordinates.ker = B.subgroupOf S ⊓ C.subgroupOf S := by
    rw [d.kernel_eq, hE]
    rfl
  have hcod : Codisjoint (B.subgroupOf S) (C.subgroupOf S) := by
    rw [hS]
    exact codisjoint_subgroupOf_sup B C
  change IsCompl (f ((B.subgroupOf S).map d.coordinates))
    (f ((C.subgroupOf S).map d.coordinates))
  exact f.isCompl ⟨disjoint_map_of_ker_eq_inf d.coordinates _ _ hk,
    Subgroup.codisjoint_map d.onto hcod⟩

/-- Conjugation of the literal subgroup agrees with the supplied linear actor. -/
theorem imageSpace_conjBy (B : Subgroup G) (hB : B ≤ S) (g : H) :
    d.imageSpace (B.conjBy (g : G)) = (d.imageSpace B).map (ρ g) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := (d.mem_imageSpace_iff _ v).mp hv
    obtain ⟨b, hb, he⟩ := ha
    let bS : S := ⟨b, hB hb⟩
    let c : S := ⟨(g : G) * bS * (g : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized g.property) bS).mp bS.property⟩
    have hca : c = a := Subtype.ext he
    refine ⟨(d.coordinates bS).toAdd,
      (d.mem_imageSpace_iff B _).mpr ⟨bS, hb, rfl⟩, ?_⟩
    calc
      ρ g (d.coordinates bS).toAdd = (d.coordinates c).toAdd :=
        (d.equivariant g bS).symm
      _ = (d.coordinates a).toAdd := congrArg (fun x : S => (d.coordinates x).toAdd) hca
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (d.mem_imageSpace_iff B v).mp hv
    let c : S := ⟨(g : G) * a * (g : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized g.property) a).mp a.property⟩
    exact (d.mem_imageSpace_iff _ _).mpr
      ⟨c, ⟨(a : G), ha, rfl⟩, d.equivariant g a⟩

private theorem coordinates_commutator (u : H) (a : S) :
    (d.coordinates
      ((⟨(u : G) * a * (u : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized u.property) a).mp a.property⟩ : S) * a⁻¹)).toAdd =
      ρ u (d.coordinates a).toAdd - (d.coordinates a).toAdd := by
  rw [map_mul, map_inv]
  change (d.coordinates ⟨(u : G) * a * (u : G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized u.property) a).mp a.property⟩).toAdd +
    -(d.coordinates a).toAdd = _
  rw [d.equivariant, sub_eq_add_neg]

/-- A commutator bound into the actual quotient kernel gives pointwise fixation. -/
theorem fixed_on_imageSpace_of_commutator_le (U B : Subgroup G)
    (hUB : ⁅U, B⁆ ≤ E) (u : H) (hu : (u : G) ∈ U) :
    ∀ v ∈ d.imageSpace B, ρ u v = v := by
  intro v hv
  obtain ⟨a, ha, rfl⟩ := (d.mem_imageSpace_iff B v).mp hv
  let c : S := (⟨(u : G) * a * (u : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized u.property) a).mp a.property⟩ : S) * a⁻¹
  have hc : (c : G) ∈ E := hUB (commutator_mem_commutator hu ha)
  have hz : (d.coordinates c).toAdd = 0 :=
    congrArg Multiplicative.toAdd ((d.coordinates_eq_one_iff c).mpr hc)
  exact sub_eq_zero.mp ((d.coordinates_commutator u a).symm.trans hz)

/-- The displacement of one actual actor lies in the image of the supplied
commutator-bound subgroup; its lift need not have prime order. -/
theorem displacement_range_le_imageSpace_of_commutator_le (U B : Subgroup G)
    (hUS : ⁅U, S⁆ ≤ B) (u : H) (hu : (u : G) ∈ U) :
    LinearMap.range (ρ u - 1) ≤ d.imageSpace B := by
  rintro _ ⟨v, rfl⟩
  obtain ⟨a, ha⟩ := d.onto (Multiplicative.ofAdd v)
  let c : S := (⟨(u : G) * a * (u : G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized u.property) a).mp a.property⟩ : S) * a⁻¹
  have hc : (c : G) ∈ B := hUS (commutator_mem_commutator hu a.property)
  apply (d.mem_imageSpace_iff B _).mpr
  refine ⟨c, hc, ?_⟩
  change (d.coordinates c).toAdd = ρ u v - v
  rw [d.coordinates_commutator, ha]
  rfl

end Representation.BinaryConjugationSection

/-!
# Natural binary sections from a literal subgroup pair

The actual section quotient turns generating conjugate subgroups with the
prescribed intersection into complementary subspaces. Two source commutator
bounds make the chosen quotient involution quadratic and fix the first image.
The binary quadratic-pair theorem supplies a full S3-equivariant natural
tensor and identifies the original subgroup image as both kernel and range.

The source conjugate uses inverse conjugation, so its linear actor is
pi(g^{-1}). Neither u itself nor g's quotient image receives an extra order
assumption. Zero natural multiplicity remains allowed.

Source: Aschbacher--Smith G.2.3(6) and 12.8.9(2)--(3), printed pp.334 and 853.
-/

public section

namespace Representation.BinaryConjugationSection

open Subgroup InvertedCubicTensor
open scoped _root_.TensorProduct

variable {G : Type*} [Group G] {H S E : Subgroup G}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The binary natural-module criterion with its original quotient and
subgroup markings. All linear hypotheses are proved from the source pair. -/
theorem natural_tensor_and_marks_of_subgroup_pair
    (σ : Representation (ZMod 2) S₃ W) (π : H →* S₃)
    (d : BinaryConjugationSection H S E (σ.comp π))
    (U B C : Subgroup G) (u g : H) (hu : (u : G) ∈ U)
    (hS : S = B ⊔ C) (hE : E = B ⊓ C)
    (hC : C = B.conjBy ((g : G)⁻¹))
    (hUB : ⁅U, B⁆ ≤ E) (hUS : ⁅U, S⁆ ≤ B)
    (ht : (π u) ^ 2 = 1) (ht1 : π u ≠ 1) :
    (∃ e : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2] W,
      ∀ a z, e ((Representation.tprod (Representation.trivial (ZMod 2) S₃
          (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
        σ a (e z)) ∧
      LinearMap.ker (σ (π u) - 1) = d.imageSpace B ∧
      LinearMap.range (σ (π u) - 1) = d.imageSpace B ∧
      (d.imageSpace C).map (σ (π u) - 1) = d.imageSpace B := by
  have hB : B ≤ S := le_sup_left.trans hS.ge
  have hconj : d.imageSpace C = (d.imageSpace B).map (σ (π g⁻¹)) := by
    rw [hC]
    exact d.imageSpace_conjBy B hB g⁻¹
  have hc : IsCompl (d.imageSpace B) ((d.imageSpace B).map (σ (π g⁻¹))) :=
    hconj ▸ d.isCompl_imageSpace B C hS hE
  obtain ⟨hn, hk, hr, hCr⟩ := BinaryQuadraticPair.natural_tensor_and_marks
    σ (d.imageSpace B) (π u) (π g⁻¹) (by simpa only [pow_two] using ht) ht1
    (d.fixed_on_imageSpace_of_commutator_le U B hUB u hu)
    (d.displacement_range_le_imageSpace_of_commutator_le U B hUS u hu) hc
  refine ⟨hn, hk, hr, ?_⟩
  rw [hconj]
  exact hCr

end Representation.BinaryConjugationSection
