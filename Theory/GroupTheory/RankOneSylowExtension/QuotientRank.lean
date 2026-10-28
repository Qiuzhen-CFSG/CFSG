module
public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.GroupTheory.SolvableRadical.Transport

/-!
# Rank comparison through a quotient with a simple section

Suppose the image of an actor lies in a nonsolvable simple
subgroup L of the image of K. A solvable normal subgroup R of K has
solvable image, so its intersection with L is trivial. The actor's image
rank is therefore bounded by its rank in K/R. The full kernel of the
original map is retained; no lifting of elementary subgroups is asserted.

Source application: Aschbacher--Smith E.1.2 and E.1.5, pp.209--210,
and the original A5 generation bound in 13.2.8(1), printed p.880.
-/

public section
open Subgroup
namespace Subgroup.RankOneSylowExtension
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

/-- Solvable kernels retain the rank of the actor image inside the simple section. -/
theorem rank_image_le_solvable_quotient_image (q : G →* Q)
    (L : Subgroup Q) [IsSimpleGroup L] (hL : ¬ Group.IsSolvable L)
    (A K : Subgroup G) (hAK : A ≤ K) (hAL : A.map q ≤ L)
    (hLK : L ≤ K.map q) (R : Subgroup K) [R.Normal] [Group.IsSolvable R] :
    Group.rank (A.map q) ≤ Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' R)) := by
  let f : K →* K.map q := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  let D := R.map f
  let : D.Normal := Subgroup.Normal.map inferInstance f hf
  let : Group.IsSolvable D := Group.isSolvable_of_surjective (f.subgroupMap_surjective R)
  have hAf : (A.subgroupOf K).map f = (A.map q).subgroupOf (K.map q) := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map_of_mem q ha
    · rintro ⟨a,ha,he⟩
      exact ⟨⟨a,hAK ha⟩,ha,Subtype.ext he⟩
  let g := (QuotientGroup.mk' D).comp f
  have hk : R ≤ g.ker := by
    intro r hr
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem f hr)
  let l := QuotientGroup.lift R g hk
  let B := (A.subgroupOf K).map (QuotientGroup.mk' R)
  have he : B.map l = ((A.map q).subgroupOf (K.map q)).map (QuotientGroup.mk' D) := by
    rw [map_map]
    change (A.subgroupOf K).map g = _
    rw [← map_map,hAf]
  have hr := Group.rank_le_of_surjective (l.subgroupMap B) (l.subgroupMap_surjective B)
  rw [he,rank_image_solvable_quotient_eq L (A.map q) (K.map q) hL hAL hLK D] at hr
  exact hr
end Subgroup.RankOneSylowExtension
