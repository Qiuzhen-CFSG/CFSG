module
public import Theory.GroupTheory.OmegaCenterProduct

/-!
# Omega centers of two commuting factors with center order two

A center of order two consists of involutions, so it equals its first
omega subgroup. For two disjoint commuting factors these subgroups form
an internal direct product of order four. This supplies the center-order
input in the paired-block conclusion of Aschbacher--Smith 14.6.9,
printed p.1027, without another model hypothesis.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G]

theorem omegaOneCenterAmbient_card_two_of_center_card_two (R : Subgroup G)
    (h : Nat.card (center R) = 2) : Nat.card (omegaOneCenterAmbient R) = 2 := by
  have heq : omegaOneCenterAmbient R = (center R).map R.subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxR,_,hc⟩ := (mem_omegaOneCenterAmbient_iff R x).mp hx
      exact ⟨⟨x,hxR⟩,mem_center_iff.mpr (fun r => Subtype.ext (hc r r.property)),rfl⟩
    · rintro ⟨r,hr,rfl⟩
      refine (mem_omegaOneCenterAmbient_iff R r).mpr ⟨r.property,?_,?_⟩
      · have hh := pow_card_eq_one' (x := (⟨r,hr⟩ : center R))
        rw [h] at hh
        exact congrArg (fun z : center R => (z : G)) hh
      · intro y hy
        exact congrArg Subtype.val ((mem_center_iff.mp hr) ⟨y,hy⟩)
  rw [heq,card_map_of_injective R.subtype_injective,h]

theorem omegaOneCenterAmbient_card_four_of_disjoint_of_center_card_two (A B : Subgroup G)
    (hd : Disjoint A B) (hc : A ≤ centralizer (B : Set G))
    (hA : Nat.card (center A) = 2) (hB : Nat.card (center B) = 2) :
    Nat.card (omegaOneCenterAmbient (A ⊔ B)) = 4 := by
  have hle (R : Subgroup G) : omegaOneCenterAmbient R ≤ R :=
    fun x hx => ((mem_omegaOneCenterAmbient_iff R x).mp hx).1
  rw [omegaOneCenterAmbient_sup_of_disjoint_of_commuting A B hd hc]
  obtain ⟨e,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (omegaOneCenterAmbient A) (omegaOneCenterAmbient B)
    (hd.mono (hle A) (hle B))
    ((hle A).trans (hc.trans (centralizer_le (hle B))))
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,
    omegaOneCenterAmbient_card_two_of_center_card_two A hA,omegaOneCenterAmbient_card_two_of_center_card_two B hB]


end Stellmacher
