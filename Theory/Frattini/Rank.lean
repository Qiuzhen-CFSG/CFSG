module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Rank

/-!
# Generator rank and the Frattini quotient

A finite group and its Frattini quotient need the same number of generators.
Lift a minimal generating set of the quotient. Its lifts together with the
Frattini subgroup generate the group; the nongenerating property of the
Frattini subgroup then removes that extra subgroup. The reverse inequality
is monotonicity under surjections.

This is the generator-lifting argument used in Burnside's basis theorem;
no p-group or commutativity hypothesis is required for this finite-group form.
-/

public section

namespace Group

theorem rank_eq_rank_quotient_frattini
    (G : Type*) [Group G] [Finite G] :
    Group.rank G = Group.rank (G ⧸ frattini G) := by
  classical
  apply le_antisymm _ (Group.rank_le_of_surjective
    (QuotientGroup.mk' (frattini G)) (QuotientGroup.mk'_surjective _))
  let q := QuotientGroup.mk' (frattini G)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let s := Function.surjInv hq
  have hs : Function.RightInverse s q := Function.rightInverse_surjInv hq
  obtain ⟨T, hTcard, hT⟩ := Group.rank_spec (G ⧸ frattini G)
  let S := T.image s
  have himage : q '' (S : Set G) = (T : Set (G ⧸ frattini G)) := by
    simp only [S, Finset.coe_image, Set.image_image]
    have hcomp : (fun x => q (s x)) = id := funext hs
    rw [hcomp, Set.image_id]
  have hmap : (Subgroup.closure (S : Set G)).map q = ⊤ := by
    rw [MonoidHom.map_closure, himage, hT]
  have hsup : Subgroup.closure (S : Set G) ⊔ frattini G = ⊤ := by
    have h := congrArg (Subgroup.comap q) hmap
    simpa only [Subgroup.comap_map_eq, q, QuotientGroup.ker_mk',
      Subgroup.comap_top] using h
  exact (Group.rank_le (frattini_nongenerating hsup)).trans
    (Finset.card_image_le.trans_eq hTcard)

end Group
