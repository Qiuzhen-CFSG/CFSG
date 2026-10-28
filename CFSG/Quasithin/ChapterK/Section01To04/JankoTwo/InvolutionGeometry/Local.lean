module
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.InvolutionGeometry.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion
public import Theory.Representation.BinaryOffender.Defs

/-!
# Elementary actors inside the concrete Hall--Janko Sylow subgroups

The certified color maps are injective on pairwise commuting elements. Every
inner Sylow element squaring to one and fixing a permutation point belongs to
the four-colored list. Every outer Sylow element squaring to one belongs to
the full list, and an actual outer element selects its eight-color map.
Thus these elementary subgroups have order at most four and eight respectively.
The inclusion into the degree-100 permutations and the inner-to-outer inclusion
remain the literal maps of the existing J₂ carrier.

Source: Aschbacher--Smith K.4.5, printed p.460 / PDF p.471.
-/

public section
namespace CFSG.Quasithin.ChapterK.JankoTwo.InvolutionGeometry
open Sporadic.LeechRelated.J2
open ExceptionalParabolics ExceptionalParabolics.Seed ExceptionalParabolics.PairNormalizer
open ExceptionalParabolics.PairNormalizer.SylowData ExceptionalParabolics.SecondParabolic
open Certificate

private theorem squareKeys_of_pow {p : Equiv.Perm (Fin 100)} (hp : p ^ 2 = 1) :
    squareKeys p := by
  exact ⟨congrArg (fun q : Equiv.Perm (Fin 100) => q 0) hp,
    congrArg (fun q : Equiv.Perm (Fin 100) => q 1) hp,
    congrArg (fun q : Equiv.Perm (Fin 100) => q 2) hp⟩

private theorem commuteKeys_of_eq {p q : Equiv.Perm (Fin 100)} (hp : p * q = q * p) :
    commuteKeys p q := by
  exact ⟨congrArg (fun r : Equiv.Perm (Fin 100) => r 0) hp,
    congrArg (fun r : Equiv.Perm (Fin 100) => r 1) hp,
    congrArg (fun r : Equiv.Perm (Fin 100) => r 2) hp⟩

private theorem pure_cover {x : Carrier} (hx : x ∈ s) (hs : x ^ 2 = 1)
    (hf : ∃ p, inclusion x p = p) :
    ∃ i : Fin 12, sTable (pureIndex i) = inclusion x := by
  obtain ⟨i, rfl⟩ := exists_sElement hx
  rw [sElement_inclusion] at hf ⊢
  have hsq : sTable i ^ 2 = 1 := by
    rw [← sElement_inclusion, ← map_pow, hs, map_one]
  rcases pure_cover_check i (squareKeys_of_pow hsq) with h | h
  · exact ⟨pureDecode i, congrArg sTable h⟩
  · exact (h hf.choose hf.choose_spec).elim

/-- A fixed-point elementary actor in the actual inner Sylow has order at most four. -/
theorem inner_sylow_card_le (A : Subgroup Carrier) [IsElementaryAbelian 2 A]
    (hAs : A ≤ s) (hfix : ∀ x ∈ A, ∃ p, inclusion x p = p) : Nat.card A ≤ 4 := by
  classical
  have cover (x : A) := pure_cover (hAs x.property)
    (elemPow_eq_one_of_isElementaryAbelian (x : Carrier) x.property) (hfix x x.property)
  let f : A → Fin 12 := fun x => (cover x).choose
  have hf (x : A) : sTable (pureIndex (f x)) = inclusion x := (cover x).choose_spec
  have hi : Function.Injective (fun x : A => pureColor (f x)) := by
    intro x y h
    have hc : commuteKeys (sTable (pureIndex (f x))) (sTable (pureIndex (f y))) := by
      rw [hf, hf]
      apply commuteKeys_of_eq
      simpa only [map_mul] using congrArg inclusion
        (setLike_mul_comm x.property y.property)
    have he := pure_color_check (f x) (f y) hc h
    apply Subtype.ext
    apply inclusion_injective
    rw [← hf, ← hf, he]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hi

private theorem outer_table_cover {x : Extension} (hx : x ∈ outerS) :
    ∃ i : Fin 256, table i = extension.subtype x := by
  classical
  by_cases hr : x ∈ intoExtension.range
  · have hm : x ∈ s.map intoExtension := outerS_inf_range ▸ (show x ∈ outerS ⊓ intoExtension.range from ⟨hx, hr⟩)
    obtain ⟨y, hy, rfl⟩ := hm
    obtain ⟨i, rfl⟩ := exists_sElement hy
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    change table ⟨i.val, by omega⟩ = inclusion (sElement i)
    simpa [table, i.isLt, Nat.mod_eq_of_lt i.isLt] using (sElement_inclusion i).symm
  · obtain ⟨i, rfl⟩ := OuterInvolutionFusion.outerSylow_coset_cover hx hr
    refine ⟨⟨i.val + 128, by omega⟩, ?_⟩
    have hm : (i.val + 128) % 128 = i.val := by omega
    simp only [table, show ¬i.val + 128 < 128 by omega, ↓reduceIte, hm, map_mul,
      outerElement_inclusion]
    change sTable i * outerTable = inclusion (sElement i) * outerTable
    rw [sElement_inclusion]

private theorem square_cover {x : Extension} (hx : x ∈ outerS) (hs : x ^ 2 = 1) :
    ∃ i : Fin 60, table (candidate i) = extension.subtype x := by
  obtain ⟨i, hi⟩ := outer_table_cover hx
  have hsq : table i ^ 2 = 1 := by rw [hi, ← map_pow, hs, map_one]
  exact ⟨decode i, (congrArg table (square_cover_check i (squareKeys_of_pow hsq))).trans hi⟩

private theorem outer_involution_cover {x : Extension} (hx : x ∈ outerS)
    (hs : x ^ 2 = 1) (ho : x ∉ intoExtension.range) :
    ∃ o : Fin 24, table (candidate (outerIndex o)) = extension.subtype x := by
  obtain ⟨j, rfl⟩ := OuterInvolutionFusion.outerSylow_coset_cover hx ho
  let i : Fin 256 := ⟨j.val + 128, by omega⟩
  have hi : table i = extension.subtype (intoExtension (sElement j) * outerElement) := by
    have hm : (j.val + 128) % 128 = j.val := by omega
    simp only [table, i, show ¬j.val + 128 < 128 by omega, ↓reduceIte, hm, map_mul,
      outerElement_inclusion]
    change sTable j * outerTable = inclusion (sElement j) * outerTable
    rw [sElement_inclusion]
  have hsq : table i ^ 2 = 1 := by rw [hi, ← map_pow, hs, map_one]
  exact ⟨outerDecode i,
    (congrArg table (outer_cover_check i (by dsimp [i]; omega)
      (squareKeys_of_pow hsq))).trans hi⟩

/-- The literal outer Sylow calculation, retaining its actual outer actor. -/
theorem outer_sylow_card_le (A : Subgroup Extension) [IsElementaryAbelian 2 A]
    (hAs : A ≤ outerS) (x : Extension) (hx : x ∈ A)
    (ho : x ∉ intoExtension.range) : Nat.card A ≤ 8 := by
  classical
  have cover (y : A) := square_cover (hAs y.property)
    (elemPow_eq_one_of_isElementaryAbelian (y : Extension) y.property)
  let f : A → Fin 60 := fun y => (cover y).choose
  have hf (y : A) : table (candidate (f y)) = extension.subtype y := (cover y).choose_spec
  obtain ⟨o, he⟩ := outer_involution_cover (hAs hx)
    (elemPow_eq_one_of_isElementaryAbelian x hx) ho
  have hc (y z : A) : adjacent (f y) (f z) = true := by
    apply commute_check
    rw [hf, hf]
    apply commuteKeys_of_eq
    simpa only [map_mul] using congrArg extension.subtype
      (setLike_mul_comm y.property z.property)
  have ho' (y : A) : adjacent (outerIndex o) (f y) = true := by
    apply commute_check
    rw [he, hf]
    apply commuteKeys_of_eq
    simpa only [map_mul] using congrArg extension.subtype
      (setLike_mul_comm hx y.property)
  have hi : Function.Injective (fun y : A => outerColor o (f y)) := by
    intro y z h
    have heq := outer_color_check o (f y) (f z) (ho' y) (ho' z) (hc y z) h
    apply Subtype.ext
    apply extension.subtype_injective
    rw [← hf, ← hf, heq]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective _ hi

end CFSG.Quasithin.ChapterK.JankoTwo.InvolutionGeometry
