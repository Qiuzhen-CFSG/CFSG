module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Positions

/-!
# Transporting the quotient geometry to the paired action maps

`SylowCoordinates` is a commuting diagram between the actual Sylow action,
the actual quotient image, and the canonical quotient of the degree-eight
Sylow group. Its multiplicative equivalence preserves the cardinalities of
all subgroup images. The action-kernel identity then identifies the first
intersection term in the source inequality; the second term is bounded by
its intersection in the second permutation action.

The rank bound is conditional on the explicitly stated geometric positions.
Those premises must come from the concrete permutation calculations, rather
than prescribed ranks. The final lemma lifts relative normality to the actual
preimage when T and S have equal quotient images.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.25, inequality (!) and the following argument, printed pp.1133–1134.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient
variable {G H : Type*} [Group G] [Group H]

/-- Compatible coordinates for the actual Sylow action and quotient image. -/
structure SylowCoordinates (S : Subgroup G) (f : G →* Perm) (q : G →* H) where
  action_le : S.map f ≤ canonicalSylow
  quotientEquiv : S.map q ≃* Quotient
  compatible (s : S) :
    quotientEquiv ⟨q s, mem_map_of_mem q s.property⟩ =
      quotientMap ⟨f s, action_le (mem_map_of_mem f s.property)⟩

namespace SylowCoordinates
variable {S A : Subgroup G} {f : G →* Perm} {q : G →* H}
variable (d : SylowCoordinates S f q)
include d

theorem action_image_le (hAS : A ≤ S) : A.map f ≤ canonicalSylow :=
  (Subgroup.map_mono hAS).trans d.action_le

theorem quotient_image_eq (hAS : A ≤ S) :
    ((A.subgroupOf S).map (q.subgroupMap S)).map d.quotientEquiv.toMonoidHom =
      quotientImage (A.map f) := by
  ext z
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨⟨f a, d.action_le (mem_map_of_mem f a.property)⟩,
      mem_map_of_mem f ha, (d.compatible a).symm⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨b, hb, he⟩ := ha
    let s : S := ⟨b, hAS hb⟩
    refine ⟨q.subgroupMap S s, mem_map_of_mem _ hb, ?_⟩
    rw [show d.quotientEquiv.toMonoidHom (q.subgroupMap S s) =
      quotientMap ⟨f s, d.action_le (mem_map_of_mem f s.property)⟩ from d.compatible s]
    exact congrArg quotientMap (Subtype.ext he)

theorem card_quotient_image (hAS : A ≤ S) :
    Nat.card (A.map q) = Nat.card (quotientImage (A.map f)) := by
  have he := Subgroup.card_map_of_injective
    (K := (A.subgroupOf S).map (q.subgroupMap S))
    (f := d.quotientEquiv.toMonoidHom) d.quotientEquiv.injective
  rw [d.quotient_image_eq hAS] at he
  have hi := Subgroup.card_map_of_injective
    (K := (A.subgroupOf S).map (q.subgroupMap S)) (S.map q).subtype_injective
  have hm : ((A.subgroupOf S).map (q.subgroupMap S)).map (S.map q).subtype = A.map q := by
    rw [Subgroup.map_map]
    change (A.subgroupOf S).map (q.comp S.subtype) = _
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAS]
  rw [hm] at hi
  exact hi.trans he.symm

theorem rank_quotient_image (hAS : A ≤ S) :
    rank (A.map q) = rank (quotientImage (A.map f)) :=
  congrArg (Nat.log 2) (d.card_quotient_image hAS)

omit d in
theorem not_le_kernel (hP : q.ker.map f = blockCore)
    (hA : ¬ A.map f ≤ blockCore) : ¬ A ≤ q.ker := by
  intro h
  exact hA (hP ▸ Subgroup.map_mono h)

theorem kernel_rank_add_quotient_rank (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) :
    rank (A.map f ⊓ q.ker.map f) + rank (A.map q) = rank (A.map f) := by
  rw [hP, d.rank_quotient_image hAS]
  exact rank_inf_add_rank_quotientImage (d.action_image_le hAS)

/-- Once the concrete position has been proved, both numerical terms follow
from it and the action-kernel identity. This does not assume a rank tuple. -/
theorem ranks_of_position {c : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hA : c.Realizes (A.map f))
    (hpos : Position c evenFour (quotientImage (A.map f)))
    (hZ : Nat.card (Subgroup.center Quotient) = 2) :
    rank (A.map q) = quotientRank c ∧
      rank (A.map f ⊓ q.ker.map f) = kernelRank c := by
  have hr : rank (A.map q) = quotientRank c :=
    (d.rank_quotient_image hAS).trans (hpos.rank hZ)
  have hk := d.kernel_rank_add_quotient_rank hAS hP
  have ha := (EightCase.dimensions hA).1
  exact ⟨hr, by unfold kernelRank; omega⟩

end SylowCoordinates

/-- The second kernel image is bounded by the intersection calculated in the
permutation model; equality of these two subgroups is not needed. -/
theorem kernel_action_rank_le (A : Subgroup G) (f : G →* Perm) (q : G →* H) :
    rank ((A ⊓ q.ker).map f) ≤ rank (A.map f ⊓ q.ker.map f) := by
  have hle : (A ⊓ q.ker).map f ≤ A.map f ⊓ q.ker.map f :=
    le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  exact Nat.log_mono_right
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle))

/-- Conditional numerical transport, to be applied to the two concrete case
calculations. It supplies exactly the upper bound used by the paired inequality. -/
theorem paired_rank_bound {S A : Subgroup G} {f g : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) (e : SylowCoordinates S g q)
    {c c' : EightCase} (hAS : A ≤ S)
    (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : c.Realizes (A.map f)) (hA' : c'.Realizes (A.map g))
    (hpos : Position c evenFour (quotientImage (A.map f)))
    (hpos' : Position c' evenFour (quotientImage (A.map g)))
    (hZ : Nat.card (Subgroup.center Quotient) = 2) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) ≤
      quotientRank c + kernelRank c + kernelRank c' := by
  obtain ⟨hr, hk⟩ := d.ranks_of_position hAS hP hA hpos hZ
  have hk' := (e.ranks_of_position hAS hP' hA' hpos' hZ).2
  have hb := kernel_action_rank_le A g q
  omega

/-- Lift relative normality through the actual quotient. In the source this
applies to S0 when the images of T and S coincide. -/
theorem normalizes_of_equal_quotient_images
    (S T S0 : Subgroup G) (q : G →* H)
    (hS0 : S0 ≤ S) (hker : q.ker ≤ S0) (he : S.map q = T.map q)
    (hn : ((S0.map q).subgroupOf (S.map q)).Normal) :
    T ≤ Subgroup.normalizer (S0 : Set G) := by
  have hm := (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_mono hS0)).mp hn
  rw [he] at hm
  have hc := (Subgroup.map_le_iff_le_comap).mp hm
  have ht := hc.trans (Subgroup.le_normalizer_comap (H := S0.map q) q)
  rwa [Subgroup.comap_map_eq_self hker] at ht

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
