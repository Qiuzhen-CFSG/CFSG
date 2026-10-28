module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Canonical.DBounds.Tables
/-!
# Transporting the binary subgroup table into the permutation group

The actual equivalence `binaryEquivD` embeds all 67 coordinate subgroups into
`S₈`. Permuting the four pairs reduces their ranks and fixed-space calculations
to sixteen representatives. Every conjugacy is an equality of actual subgroups,
not a label identifying an abstract family.

Source: Aschbacher–Smith, Proposition B.3.2, printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
open Representation.BinaryOffender BinaryPermutation
/-- The coordinate embedding is the given multiplicative equivalence with `D`. -/
noncomputable def dHom : BinaryFour →* Perm :=
  (D 8).subtype.comp binaryEquivD.toMonoidHom

theorem dHom_eq : dHom = binaryPermutation := rfl

theorem dHom_vector (x : Fin 16) : dHom (vectorEquiv x) = dWords x := by
  change dWords (finFunctionFinEquiv ((finFunctionFinEquiv (m := 2) (n := 4)).symm x)) = _
  rw [Equiv.apply_symm_apply]

/-- The subgroup of permutations belonging to a binary subspace. -/
noncomputable def group (i : Fin 67) : Subgroup Perm := (binaryGroup i).map dHom

theorem group_exhaustive (B : Subgroup Perm) (hB : B ≤ D 8) : ∃ i, group i = B := by
  obtain ⟨i, hi⟩ := binaryGroup_exhaustive (B.comap dHom)
  refine ⟨i, ?_⟩
  rw [group, hi, Subgroup.map_comap_eq]
  apply inf_eq_right.mpr
  simpa only [dHom_eq, binaryPermutation_range] using hB

theorem mem_group (i : Fin 67) (g : Perm) :
    g ∈ group i ↔ ∃ x ∈ members i, dWords x = g := by
  rw [group, Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨vectorEquiv.symm x, hx, ?_⟩
    rw [← dHom_vector, vectorEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨vectorEquiv x, (vector_mem i x).mpr hx, dHom_vector x⟩

/-- The complete member set can serve as generators. -/
def perms (i : Fin 67) : Finset Perm := (members i).image dWords

theorem group_eq_closure (i : Fin 67) :
    group i = Subgroup.closure (perms i : Set Perm) := by
  have he : (perms i : Set Perm) = (group i : Set Perm) := by
    ext g
    simp only [perms, Finset.mem_image, mem_group, SetLike.mem_coe]
  rw [he, Subgroup.closure_eq]

theorem card_group (i : Fin 67) : Nat.card (group i) = (members i).card := by
  let f : {x // x ∈ members i} → group i := fun x =>
    ⟨dWords x.val, (mem_group i _).mpr ⟨x.val, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      exact Subtype.ext (dWords_injective (congrArg Subtype.val h))
    · intro g
      obtain ⟨x, hx, he⟩ := (mem_group i g.val).mp g.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card,
    Fintype.card_coe]

/-- Representatives under permutations of the four coordinate pairs. -/
def representative : Fin 16 → Fin 67 := ![0, 1, 3, 7, 15, 16, 18, 22, 30, 33, 34, 51, 53, 57, 65, 66]

def representativeIndex : Fin 67 → Fin 16 := ![0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 5, 6, 6, 7, 6, 8, 6, 8, 9, 10, 5, 6, 6, 7, 6, 8, 9, 10, 6, 9, 8, 10, 7, 10, 10, 10, 11, 11, 12, 11, 12, 12, 13, 11, 12, 12, 13, 12, 13, 13, 14, 15]

private def conjugatingMap : Fin 67 → Fin 8 → Fin 8 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![2, 3, 6, 7, 0, 1, 4, 5],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![2, 3, 6, 7, 0, 1, 4, 5],
  ![2, 3, 0, 1, 6, 7, 4, 5],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![4, 5, 0, 1, 6, 7, 2, 3],
  ![4, 5, 2, 3, 6, 7, 0, 1],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![6, 7, 0, 1, 4, 5, 2, 3],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![6, 7, 2, 3, 4, 5, 0, 1],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![2, 3, 6, 7, 0, 1, 4, 5],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![2, 3, 6, 7, 0, 1, 4, 5],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7]]

private def inverseMap : Fin 67 → Fin 8 → Fin 8 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![4, 5, 0, 1, 6, 7, 2, 3],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![4, 5, 0, 1, 6, 7, 2, 3],
  ![2, 3, 0, 1, 6, 7, 4, 5],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![2, 3, 6, 7, 0, 1, 4, 5],
  ![6, 7, 2, 3, 0, 1, 4, 5],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![2, 3, 6, 7, 4, 5, 0, 1],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![6, 7, 2, 3, 4, 5, 0, 1],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![4, 5, 0, 1, 6, 7, 2, 3],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 6, 7, 4, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 6, 7, 2, 3, 4, 5],
  ![0, 1, 4, 5, 2, 3, 6, 7],
  ![0, 1, 4, 5, 6, 7, 2, 3],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![6, 7, 0, 1, 2, 3, 4, 5],
  ![4, 5, 0, 1, 2, 3, 6, 7],
  ![4, 5, 0, 1, 6, 7, 2, 3],
  ![2, 3, 0, 1, 4, 5, 6, 7],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![2, 3, 4, 5, 0, 1, 6, 7],
  ![2, 3, 4, 5, 6, 7, 0, 1],
  ![0, 1, 2, 3, 4, 5, 6, 7],
  ![0, 1, 2, 3, 4, 5, 6, 7]]

/-- A permutation of the four pairs, acting on the eight actual points. -/
private def conjugator (i : Fin 67) : Perm where
  toFun := conjugatingMap i
  invFun := inverseMap i
  left_inv := by revert i; decide +kernel
  right_inv := by revert i; decide +kernel

private theorem conjugate_perms (i : Fin 67) :
    (perms (representative (representativeIndex i))).image (MulAut.conj (conjugator i)) =
      perms i := by
  revert i
  decide +kernel

/-- The small coordinate classification is actual permutation conjugacy. -/
theorem group_conjugate (i : Fin 67) :
    IsConjugateTo (group i) (group (representative (representativeIndex i))) := by
  refine ⟨conjugator i, ?_⟩
  rw [group_eq_closure, group_eq_closure, MonoidHom.map_closure]
  congr 1
  exact (Finset.coe_image.symm.trans (congrArg (fun s : Finset Perm => (s : Set Perm))
    (conjugate_perms i))).symm

end CFSG.Quasithin.ChapterB.Offenders.Eight.DBounds
