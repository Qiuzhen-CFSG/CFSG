module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# The natural summand of the paired symplectic action

Embedding v as (v,0) identifies the natural fixed space with the first
summand of the paired fixed space. Consequently the plane radical and Sylow
center fix exactly the natural plane, while the point radical fixes exactly
the natural point. Restriction of scalars gives codimensions 2n, 2n and 3n.
These are the local fixed spaces used in the natural-module family argument;
the classification of the family A_(2n) requires further subgroup analysis.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
variable {F : Type*} [Field F] [Algebra (ZMod 2) F]

noncomputable abbrev binaryNatural : Representation (ZMod 2) (Sp F) (Vector F) :=
  restrictScalars (symplecticNatural 2)

variable [CharP F 2] [Finite F]
lemma mem_binaryNatural_fixedSpace_iff (A : Subgroup (Sp F)) (v : Vector F) :
    v ∈ fixedSpace binaryNatural A ↔ (v,0) ∈ fixedSpace graphPair A := by
  constructor
  · intro h g
    change (symplecticNatural 2 (g : Sp F) v,
      symplecticNatural 2 (graphAut (g : Sp F)) 0) = (v,0)
    exact Prod.ext (h g) (map_zero _)
  · intro h g
    exact congrArg Prod.fst (h g)

lemma planeRadical_natural_fixedSpace : fixedSpace (binaryNatural (F := F)) planeRadical =
    (plane F).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_binaryNatural_fixedSpace_iff,planeRadical_fixedSpace]
  change (v ∈ plane F ∧ (0 : Vector F) ∈ point F) ↔ v ∈ plane F
  simp only [Submodule.zero_mem,and_true]

lemma pointRadical_natural_fixedSpace : fixedSpace (binaryNatural (F := F)) pointRadical =
    (point F).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_binaryNatural_fixedSpace_iff,pointRadical_fixedSpace]
  change (v ∈ point F ∧ (0 : Vector F) ∈ plane F) ↔ v ∈ point F
  simp only [Submodule.zero_mem,and_true]

lemma sylowCenter_natural_fixedSpace : fixedSpace (binaryNatural (F := F)) sylowCenter =
    (plane F).restrictScalars (ZMod 2) := by
  ext v
  rw [mem_binaryNatural_fixedSpace_iff,sylowCenter_fixedSpace]
  change (v ∈ plane F ∧ (0 : Vector F) ∈ plane F) ↔ v ∈ plane F
  simp only [Submodule.zero_mem,and_true]

omit [CharP F 2] in
lemma finrank_binary_plane {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) ((plane F).restrictScalars (ZMod 2)) = 2*n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F,coefficient_finrank hF,
    ((plane F).restrictScalarsEquiv (ZMod 2)).finrank_eq,finrank_plane]
  omega

omit [CharP F 2] in
lemma finrank_binary_point {n : ℕ} (hF : Nat.card F = 2^n) :
    Module.finrank (ZMod 2) ((point F).restrictScalars (ZMod 2)) = n := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F,coefficient_finrank hF,
    ((point F).restrictScalarsEquiv (ZMod 2)).finrank_eq,finrank_point,mul_one]

lemma planeRadical_natural_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (binaryNatural (F := F)) planeRadical = 2*n := by
  have h := fixedCodim_add_finrank (binaryNatural (F := F)) planeRadical
  rw [planeRadical_natural_fixedSpace,finrank_binary_plane hF,finrank_vector hF] at h
  omega

lemma pointRadical_natural_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (binaryNatural (F := F)) pointRadical = 3*n := by
  have h := fixedCodim_add_finrank (binaryNatural (F := F)) pointRadical
  rw [pointRadical_natural_fixedSpace,finrank_binary_point hF,finrank_vector hF] at h
  omega

lemma sylowCenter_natural_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (binaryNatural (F := F)) sylowCenter = 2*n := by
  have h := fixedCodim_add_finrank (binaryNatural (F := F)) sylowCenter
  rw [sylowCenter_natural_fixedSpace,finrank_binary_plane hF,finrank_vector hF] at h
  omega

end SymplecticConjugatePair
