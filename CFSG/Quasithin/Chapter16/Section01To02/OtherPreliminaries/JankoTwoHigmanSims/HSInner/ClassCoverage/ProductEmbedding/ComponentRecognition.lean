module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding.ComponentRecognition.Checks

/-!
# Recognition of the fixed alternating component in HS

Pair the two exact HS generators with the specified even six-letter
permutations. Checked left transitions show that the paired word subgroup
has 360 elements. Both projections are injective. The first projects onto
exactly `D`; the second projects onto A₆, since it has 360 distinct images.
Their composite gives an actual group isomorphism, with no recognition or
faithfulness premise.

This supplies the alternating factor needed for the marked product centralizer
in Aschbacher–Smith 16.1.5(10), printed p.1172, and GLS3 Table 5.3m.
The six-letter generator permutations were discovered from the six left
cosets of `A` in `D`; the proof here independently certifies the correspondence
by paired words, without assuming that coset enumeration.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
open Sporadic.LeechRelated.HS Theory.GroupTheory Subgroup

namespace ComponentRecognition

private def paired : Subgroup (Carrier × A6) :=
  wordSubgroup letter inverseLetter letter_inv

private def enumerated (r : Fin 360) : paired := ⟨row r, ⟨word r, rfl⟩⟩

private theorem enumerated_surjective : Function.Surjective enumerated := by
  have hw (w : List (Fin 4)) : ∃ r, row r = evalWord letter w := by
    induction w with
    | nil => exact ⟨0, row_zero⟩
    | cons i w ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨next i r, (step i r).symm.trans (congrArg (letter i * ·) hr)⟩
  rintro ⟨g, w, hg⟩
  obtain ⟨r, hr⟩ := hw w
  exact ⟨r, Subtype.ext (hr.trans hg)⟩

private theorem enumerated_injective : Function.Injective enumerated := by
  intro r s h
  exact six_injective (congrArg (fun g : paired => g.val.2) h)

private theorem paired_card : Nat.card paired = 360 := by
  have h := Nat.card_congr (Equiv.ofBijective enumerated
    ⟨enumerated_injective, enumerated_surjective⟩).symm
  simpa using h

private theorem fst_word (w : List (Fin 4)) :
    (evalWord letter w).1 = evalWord dLetter w := by
  induction w with
  | nil => rfl
  | cons i w ih => exact congrArg (dLetter i * ·) ih

private def first : paired →* D :=
  ((MonoidHom.fst Carrier A6).comp paired.subtype).codRestrict D (by
    rintro ⟨g, w, rfl⟩
    change (evalWord letter w).1 ∈ D
    rw [fst_word]
    exact dWord_mem w)

private theorem first_injective : Function.Injective first := by
  intro x y h
  obtain ⟨r, rfl⟩ := enumerated_surjective x
  obtain ⟨s, rfl⟩ := enumerated_surjective y
  exact congrArg enumerated (hs_injective (congrArg Subtype.val h))

private theorem first_surjective : Function.Surjective first := by
  have hD : D ≤ ((MonoidHom.fst Carrier A6).comp paired.subtype).range := by
    apply (closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · refine ⟨⟨letter 0, ?_⟩, rfl⟩
      exact ⟨[0], mul_one _⟩
    · rw [Set.mem_singleton_iff.mp hx]
      refine ⟨⟨letter 1, ?_⟩, rfl⟩
      exact ⟨[1], mul_one _⟩
  intro d
  obtain ⟨g, hg⟩ := hD d.property
  exact ⟨g, Subtype.ext hg⟩

private def second : paired →* A6 :=
  (MonoidHom.snd Carrier A6).comp paired.subtype

private theorem second_injective : Function.Injective second := by
  intro x y h
  obtain ⟨r, rfl⟩ := enumerated_surjective x
  obtain ⟨s, rfl⟩ := enumerated_surjective y
  exact congrArg enumerated (six_injective h)

private theorem second_bijective : Function.Bijective second := by
  apply (Nat.bijective_iff_injective_and_card second).mpr
  refine ⟨second_injective, ?_⟩
  rw [paired_card]
  change 360 = Nat.card (alternatingGroup (Fin 6))
  rw [nat_card_alternatingGroup]
  norm_num

/-- The isomorphism obtained from the two faithful projections of the paired
word subgroup. It uses the exact `D` of `Seed` and the actual A₆ carrier. -/
noncomputable def equiv : D ≃* A6 :=
  (MulEquiv.ofBijective first ⟨first_injective, first_surjective⟩).symm.trans
    (MulEquiv.ofBijective second second_bijective)

end ComponentRecognition

/-- Unconditional recognition of the fixed HS alternating component. -/
theorem D_equiv_A6 : Nonempty (D ≃* A6) := ⟨ComponentRecognition.equiv⟩

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.ClassCoverage.ProductEmbedding
