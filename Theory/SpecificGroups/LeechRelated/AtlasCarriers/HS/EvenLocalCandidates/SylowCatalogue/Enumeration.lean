module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.SylowCatalogue.Checks
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# A bijective word enumeration of the specified HS two-subgroup

Packed point maps are checked against words in the three actual generators.
Generator and inverse-generator transitions show, by closure induction, that
all subgroup elements occur. Their images on two points distinguish the rows.
Thus the word enumeration gives an equivalence with `Fin 512`.

Source: the fixed ATLAS permutations; GLS volume 3, Table 5.3m, printed p.274.
Candidate data and their reproduction script are in `source/`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
open Subgroup Theory.GroupTheory
set_option maxRecDepth 100000
set_option Elab.async false

theorem element_mem (i : Fin 512) : element i ∈ subgroup := by
  unfold element
  induction word i with
  | nil => exact subgroup.one_mem
  | cons j w ih =>
    exact subgroup.mul_mem (subset_closure ⟨j, rfl⟩) ih

private theorem evalWord_point (w : List (Fin 3)) (x : Fin 100) :
    ((evalWord sylowGenerator w : Carrier) : Equiv.Perm (Fin 100)) x =
      point (rowOfWord w) x := by
  induction w with
  | nil => exact (point_zero x).symm
  | cons j w ih =>
    change (sylowGenerator j : Equiv.Perm (Fin 100))
      (((evalWord sylowGenerator w : Carrier) : Equiv.Perm (Fin 100)) x) = _
    rw [ih, generatorPoint_spec]
    exact (point_transition j (rowOfWord w) x).symm

theorem element_point (i : Fin 512) (x : Fin 100) :
    (element i : Equiv.Perm (Fin 100)) x = point i x := by
  change ((evalWord sylowGenerator (word i) : Carrier) : Equiv.Perm (Fin 100)) x = _
  rw [evalWord_point, rowOfWord_word]

theorem element_injective : Function.Injective element := by
  intro i j hij
  apply Fin.ext
  rw [← decode_point i, ← decode_point j]
  have h := congrArg (fun g : Carrier =>
    decode ((g : Equiv.Perm (Fin 100)) 1) ((g : Equiv.Perm (Fin 100)) 4)) hij
  simpa only [element_point] using h

theorem element_next (j : Fin 3) (i : Fin 512) :
    element (next (Fin.castAdd 3 j) i) = sylowGenerator j * element i := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (element (next (Fin.castAdd 3 j) i) : Equiv.Perm (Fin 100)) x =
    (sylowGenerator j : Equiv.Perm (Fin 100)) ((element i : Equiv.Perm (Fin 100)) x)
  simp only [element_point]
  exact (point_transition j i x).trans (generatorPoint_spec j (point i x)).symm

theorem element_next_inv (j : Fin 3) (i : Fin 512) :
    element (next (Fin.natAdd 3 j) i) = (sylowGenerator j)⁻¹ * element i := by
  have h := element_next j (next (Fin.natAdd 3 j) i)
  rw [next_cancel] at h
  have h' := congrArg (fun z : Carrier => (sylowGenerator j)⁻¹ * z) h
  simpa using h'.symm

theorem element_zero : element 0 = 1 := by rfl

theorem element_surjective {x : Carrier} (hx : x ∈ subgroup) :
    ∃ i : Fin 512, element i = x := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, element_zero⟩
  | mul_left x hx y _ ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    exact ⟨next (Fin.castAdd 3 j) i, element_next j i⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨j, rfl⟩ := hx
    obtain ⟨i, rfl⟩ := ih
    exact ⟨next (Fin.natAdd 3 j) i, element_next_inv j i⟩

noncomputable def enumeration : Fin 512 ≃ subgroup :=
  Equiv.ofBijective (fun i => ⟨element i, element_mem i⟩)
    ⟨fun _ _ h => element_injective (congrArg Subtype.val h),
      fun x => by
        obtain ⟨i, hi⟩ := element_surjective x.property
        exact ⟨i, Subtype.ext hi⟩⟩

theorem subgroup_card : Nat.card subgroup = 2 ^ 9 := by
  rw [← Nat.card_congr enumeration]
  exact Nat.card_fin 512

end Sporadic.LeechRelated.HS.EvenLocalCandidates.SylowCatalogueData
