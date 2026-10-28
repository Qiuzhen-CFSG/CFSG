module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.Radical
public import Theory.GroupTheory.CyclicExtension
import Mathlib.Tactic.Group

/-!
# Collecting the full Ree second-endpoint graph

Ten reflection conjugation identities preserve the image of the order-2048
coordinate kernel. The first root and the reflection generate a complement
with at most six words. Two applications of cyclic collection therefore give
2048 × 3 × 2 normal forms in every finite image satisfying the displayed
relations. The graph consumer applies this to pairs of original and proposed
images; the relations here remain explicit obligations.

Source coordinates: Shinoda (1975), pp.81–83; Parrott (1972), p.683.
The graph proof follows the existing Tits LocalRestrictions/SecondExtension
construction, with the entire full-Ree Sylow homomorphism retained.
-/

@[expose] public section
namespace Tits.AmalgamRigidity.FullRee.SecondExtension
open ReeTwo Theory.GroupTheory

/-- The specified reflection action on the radical generators. -/
def weylImage (i : Fin 10) : SylowModel :=
  ![SylowModel.root 1, SylowModel.rootOne, SylowModel.root 3,
    SylowModel.root 2, SylowModel.root 6, SylowModel.rootOne ^ 2,
    SylowModel.root 4, SylowModel.root 7, SylowModel.root 9, SylowModel.root 8] i

theorem weylImage_mem (i : Fin 10) : weylImage i ∈ radical := by
  exact (by decide +kernel : ∀ i : Fin 10, (weylImage i).left.b0 = 0) i

/-- Twelve literal word equations suffice for collection. This is a relation
contract, with no automorphism, factorization, or isomorphism premise. -/
structure WeylRelations {G : Type*} [Group G] (f : SylowModel →* G) (r : G) : Prop where
  square : r ^ 2 = 1
  cube : (f (SylowModel.root 0) * r) ^ 3 = 1
  conjugate (i : Fin 10) :
    r * f (radicalGenerator i) * r⁻¹ = f (weylImage i)

variable {G : Type*} [Group G] (f : SylowModel →* G) (r : G)

private theorem conjugate_radical (h : WeylRelations f r) {x : SylowModel}
    (hx : x ∈ radical) : r * f x * r⁻¹ ∈ radical.map f := by
  have hle : radical ≤ (radical.map f).comap ((MulAut.conj r).toMonoidHom.comp f) := by
    nth_rw 1 [← radical_generated]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change r * f (radicalGenerator i) * r⁻¹ ∈ radical.map f
    rw [h.conjugate]
    exact Subgroup.mem_map_of_mem f (weylImage_mem i)
  exact hle hx

private theorem conjugate_image_radical (x : SylowModel) {y : G}
    (hy : y ∈ radical.map f) : f x * y * (f x)⁻¹ ∈ radical.map f := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [← map_inv, ← map_mul, ← map_mul]
  apply Subgroup.mem_map_of_mem
  change radicalCharacter (x * z * x⁻¹) = 1
  simp only [map_mul, map_inv, show radicalCharacter z = 1 from hz, mul_one, mul_inv_cancel]

/-- Normal forms with 2048 radical entries and at most six complement words. -/
def normalForm (p : radical × Fin 3 × Fin 2) : G :=
  f p.1 * (f (SylowModel.root 0) * r) ^ p.2.1.val * r ^ p.2.2.val

variable [Finite G]

/-- Collection in every finite image satisfying the twelve word equations. -/
theorem normalForm_surjective (h : WeylRelations f r) {x : G}
    (hx : x ∈ Subgroup.closure (insert r (Set.range f))) :
    ∃ p : radical × Fin 3 × Fin 2, normalForm f r p = x := by
  let K := radical.map f
  let d := f (SylowModel.root 0) * r
  let C := Subgroup.closure (insert d (K : Set G))
  let D := Subgroup.closure (insert r (insert d (K : Set G)))
  have hrK {y : G} (hy : y ∈ K) : r * y * r⁻¹ ∈ K := by
    obtain ⟨z, hz, rfl⟩ := hy
    exact conjugate_radical f r h hz
  have hdK {y : G} (hy : y ∈ K) : d * y * d⁻¹ ∈ K := by
    have hm := conjugate_image_radical f (SylowModel.root 0) (hrK hy)
    convert hm using 1
    dsimp [d]
    group
  have hd : r * d * r⁻¹ = d⁻¹ := by
    have hx0 : f (SylowModel.root 0) ^ 2 = 1 := by
      rw [← map_pow]
      exact (congrArg f (by decide +kernel : SylowModel.root 0 ^ 2 = 1)).trans (map_one f)
    have hr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using h.square)
    have hx : (f (SylowModel.root 0))⁻¹ = f (SylowModel.root 0) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx0)
    dsimp [d]
    rw [mul_inv_rev, hx]
    calc
      r * (f (SylowModel.root 0) * r) * r⁻¹ = r * f (SylowModel.root 0) := by group
      _ = r⁻¹ * f (SylowModel.root 0) := by rw [hr]
  have hDC : ∀ y ∈ insert d (K : Set G), r * y * r⁻¹ ∈ C := by
    rintro y (rfl | hy)
    · rw [hd]
      exact C.inv_mem (Subgroup.subset_closure (Or.inl rfl))
    · exact Subgroup.subset_closure (Or.inr (hrK hy))
  have hKD : ∀ y ∈ K, y ∈ D := fun y hy =>
    Subgroup.subset_closure (Or.inr (Or.inr hy))
  have hdD : d ∈ D := Subgroup.subset_closure (Or.inr (Or.inl rfl))
  have hrD : r ∈ D := Subgroup.subset_closure (Or.inl rfl)
  have hx0D : f (SylowModel.root 0) ∈ D := by
    have he : f (SylowModel.root 0) = d * r⁻¹ := by dsimp [d]; group
    rw [he]
    exact D.mul_mem hdD (D.inv_mem hrD)
  have hcover : Subgroup.closure (insert r (Set.range f)) ≤ D := by
    apply (Subgroup.closure_le _).mpr
    rintro y (rfl | ⟨z, rfl⟩)
    · exact hrD
    · obtain ⟨k, i, he⟩ := sylow_split z
      rw [← he, map_mul, map_pow]
      exact D.mul_mem (hKD _ (Subgroup.mem_map_of_mem f k.property)) (D.pow_mem hx0D _)
  obtain ⟨y, hy, j, hj⟩ := exists_mul_pow_of_mem_closure_insert
    (insert d (K : Set G)) r 2 (by decide) h.square hDC (hcover hx)
  obtain ⟨z, hz, i, hi⟩ := exists_mul_pow_of_mem_closure_insert
    (K : Set G) d 3 (by decide) h.cube
    (by intro z hz; simpa only [Subgroup.closure_eq] using hdK hz) hy
  rw [Subgroup.closure_eq] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  refine ⟨(⟨k, hk⟩, i, j), ?_⟩
  change f k * d ^ i.val * r ^ j.val = x
  rw [hi, hj]

end Tits.AmalgamRigidity.FullRee.SecondExtension
