module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.RegularEven
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Dihedral

/-!
# Numerical consequences for the two actual action maps

The concrete positions and quotient diagram determine both the quotient rank
and the first action-kernel intersection rank. Inclusion bounds the second
kernel-action image, yielding all upper bounds used by the source inequality
and the disjoint/disjoint replacement step. The regular/transposition pairings
and the equal nonstrong cases give strict numerical bounds; the source owner
still supplies the rank inequality and the conjugation comparison of cases.

For the genuine even preimage S0, the action-kernel identity puts P inside S0.
If S and T have equal quotient images, relative normality of the alternating
preimage descends and lifts to give T-normalization of S0.

Source: Aschbacher–Smith, proof of 15.3.25, printed pp.1133–1134.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient
variable {G H : Type*} [Group G] [Group H]

namespace SylowCoordinates
variable {S A : Subgroup G} {f : G →* Perm} {q : G →* H}
variable (d : SylowCoordinates S f q)
include d

/-- The source ranks follow from the four permutation calculations and the
commuting quotient diagram, with no position or numerical premise. -/
theorem ranks_of_realizes {c : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hA : c.Realizes (A.map f)) :
    rank (A.map q) = quotientRank c ∧
      rank (A.map f ⊓ q.ker.map f) = kernelRank c :=
  d.ranks_of_position hAS hP hA
    (realizes_position hA (d.action_image_le hAS)) card_center

end SylowCoordinates

/-- No actual offender family can lie in P when its action image is the block kernel. -/
theorem realizes_not_le_kernel {A : Subgroup G} {f : G →* Perm} {q : G →* H}
    {c : EightCase} (hP : q.ker.map f = blockCore) (hA : c.Realizes (A.map f)) :
    ¬ A ≤ q.ker :=
  SylowCoordinates.not_le_kernel hP (realizes_not_le_blockCore hA)

/-- The complete numerical bound used in the paired offender inequality.
The three ranks are ranks of the actual quotient and action images. -/
theorem paired_rank_bound_of_realizes
    {S A : Subgroup G} {f g : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) (e : SylowCoordinates S g q)
    {c c' : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) ≤
      quotientRank c + kernelRank c + kernelRank c' :=
  paired_rank_bound d e hAS hP hP' hA hA'
    (realizes_position hA (d.action_image_le hAS))
    (realizes_position hA' (e.action_image_le hAS)) card_center

/-- Both orientations of the regular/transposition pairing violate the rank
inequality once its right side is replaced by the computed fixed codimensions. -/
theorem paired_rank_lt_of_regular_transposition
    {S A : Subgroup G} {f g : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) (e : SylowCoordinates S g q)
    {c c' : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g))
    (hc : (c = .regular ∧ c' = .transposition) ∨ (c = .transposition ∧ c' = .regular)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) <
      c.codim + c'.codim := by
  have hb := paired_rank_bound_of_realizes d e hAS hP hP' hA hA'
  rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals norm_num [quotientRank, kernelRank, EightCase.actorRank, EightCase.codim] at hb ⊢
  all_goals omega

/-- In a common case other than disjoint transpositions, the computed upper
bound is strictly smaller than the sum of the two fixed codimensions. -/
theorem paired_rank_lt_of_same_case
    {S A : Subgroup G} {f g : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) (e : SylowCoordinates S g q)
    {c : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c.Realizes (A.map g)) (hc : c ≠ .disjoint) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) <
      c.codim + c.codim := by
  have hb := paired_rank_bound_of_realizes d e hAS hP hP' hA hA'
  cases c <;> simp_all [quotientRank, kernelRank, EightCase.actorRank, EightCase.codim]
  all_goals omega

/-- When T and S have the same quotient image, T normalizes the actual preimage
of the even action image. The parity description is an explicit identification
of S0, and the action-kernel identity proves that this preimage contains P. -/
theorem normalizes_even_preimage_of_equal_quotient_images
    (S T S0 : Subgroup G) (f : S →* Perm) (q : G →* H)
    (hS0 : S0 = ((alternatingGroup (Fin 8)).comap f).map S.subtype)
    (hPS : q.ker ≤ S) (hP : (q.ker.subgroupOf S).map f = blockCore)
    (he : S.map q = T.map q) :
    T ≤ Subgroup.normalizer (S0 : Set G) := by
  have hS0S : S0 ≤ S := by rw [hS0]; exact map_subtype_le _
  have hPS0 : q.ker ≤ S0 := by
    intro x hx
    rw [hS0]
    refine ⟨⟨x, hPS hx⟩, ?_, rfl⟩
    apply blockCore_le_alternating
    rw [← hP]
    exact mem_map_of_mem f hx
  have hn : (S0.subgroupOf S).Normal := by
    have hh : S0.subgroupOf S = (alternatingGroup (Fin 8)).comap f := by
      rw [hS0, ← comap_subtype]
      exact comap_map_eq_self_of_injective S.subtype_injective _
    rw [hh]
    infer_instance

  have hm : (S0.subgroupOf S).map (q.subgroupMap S) =
      (S0.map q).subgroupOf (S.map q) := by
    ext x
    constructor
    · rintro ⟨a, ha, he⟩
      exact ⟨a, ha, congrArg (fun z : S.map q => z.val) he⟩
    · rintro ⟨a, ha, he⟩
      exact ⟨⟨a, hS0S ha⟩, ha, Subtype.ext he⟩
  have hnormal := hn.map (q.subgroupMap S) (q.subgroupMap_surjective S)
  rw [hm] at hnormal
  exact normalizes_of_equal_quotient_images S T S0 q hS0S hPS0 he hnormal

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
