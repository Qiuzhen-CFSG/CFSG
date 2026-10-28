module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.GroupTheory.NormalCenterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Moving abelian subgroups of index two

An abelian index-two subgroup of a noncommutative group is self-centralizing.
Two distinct abelian index-two subgroups generate the group and have central
intersection, so the whole center has index at most four. In a normal subgroup,
a nonnormal marked abelian subgroup supplies the second subgroup by conjugation.

Source application: the one-abelian-core branch of Aschbacher–Smith F.1.12
and F.6.5, printed pp.262–263 and 305.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

 theorem centralizer_eq_of_abelian_index_two (W : Subgroup G)
    [IsMulCommutative W] (hi : W.index=2) (hn : ¬ IsMulCommutative G) :
    centralizer (W : Set G)=W := by
  let := W.normal_of_index_eq_two hi
  have hdiv : (centralizer (W : Set G)).index ∣ 2 := hi ▸ index_dvd_of_le W.le_centralizer
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
  · have hc : W≤center G := centralizer_eq_top_iff_subset.mp (index_eq_one.mp h1)
    let : IsCyclic (G⧸W) := isCyclic_of_prime_card (show Nat.card (G⧸W)=2 from hi)
    exact (hn ((QuotientGroup.mk' W).isMulCommutative_of_isCyclic_of_ker_le_center
      (by simpa only [QuotientGroup.ker_mk'] using hc))).elim
  · apply Eq.symm
    apply eq_of_le_of_card_ge W.le_centralizer
    have ha := W.index_mul_card
    have hb := (centralizer (W : Set G)).index_mul_card
    rw [hi] at ha
    rw [h2] at hb
    omega

 theorem center_le_abelian_index_two (W : Subgroup G)
    [IsMulCommutative W] (hi : W.index=2) (hn : ¬ IsMulCommutative G) :
    center G≤W := by
  rw [←centralizer_eq_of_abelian_index_two W hi hn]
  exact center_le_centralizer _

 theorem center_card_bound_of_two_abelian_index_two (U W : Subgroup G)
    [IsMulCommutative U] [IsMulCommutative W] (hi : U.index=2) (hj : W.index=2)
    (hne : U≠W) : Nat.card G ≤ 4*Nat.card (center G) := by
  have hout : ¬W≤U := by
    intro h
    apply hne
    apply Eq.symm
    apply eq_of_le_of_card_ge h
    have ha := U.index_mul_card
    have hb := W.index_mul_card
    rw [hi] at ha
    rw [hj] at hb
    omega
  have hsup : U⊔W=⊤ := by
    obtain ⟨t,ht,htr⟩ := SetLike.not_le_iff_exists.mp hout
    apply top_unique
    intro x _
    by_cases hx : x∈U
    · exact mem_sup_left hx
    · have hxt : x*t⁻¹∈U := by
        rw [U.mul_mem_iff_of_index_two hi,U.inv_mem_iff]
        exact iff_of_false hx htr
      simpa using (U⊔W).mul_mem (mem_sup_left hxt) (mem_sup_right ht)
  have hc : U⊓W≤center G := by
    have h := sup_le (U.le_centralizer.trans (centralizer_le inf_le_left))
      (W.le_centralizer.trans (centralizer_le inf_le_right))
    exact centralizer_eq_top_iff_subset.mp (top_unique (hsup ▸ h))
  let := U.normal_of_index_eq_two hi
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes U W
    (by rw [U.normalizer_eq_top];exact le_top)
  have he : Nat.card (U⊔W : Subgroup G)=Nat.card G := by
    rw [hsup]
    exact Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup G)≃*G).toEquiv
  rw [he] at hprod
  have ha := U.index_mul_card
  have hb := W.index_mul_card
  rw [hi] at ha
  rw [hj] at hb
  have hcard := card_le_of_le hc
  have hp := Nat.card_pos (α := G)
  nlinarith

/-- Moving an abelian index-two subgroup of a normal subgroup gives the
same center bound without assuming an abstract local model. -/
theorem center_card_bound_of_moving_abelian_index_two (R : Subgroup G) [R.Normal]
    (W : Subgroup R) [IsMulCommutative W] (hi : W.index=2)
    (hn : ¬ (W.map R.subtype).Normal) :
    Nat.card R ≤ 4*Nat.card (center R) := by
  have hex : ∃ g : G, W.map (MulAut.conjNormal g).toMonoidHom ≠ W := by
    by_contra! hh
    apply hn
    rw [normal_iff_map_conj_eq]
    intro g
    have he : (W.map R.subtype).map (MulAut.conj g).toMonoidHom =
        (W.map (MulAut.conjNormal g).toMonoidHom).map R.subtype := by
      rw [map_map,map_map]
      rfl
    exact he.trans (congrArg (fun K : Subgroup R => K.map R.subtype) (hh g))
  obtain ⟨g,hg⟩ := hex
  exact center_card_bound_of_two_abelian_index_two W
    (W.map (MulAut.conjNormal g).toMonoidHom) hi
    (by
      exact (index_map_of_bijective (f := (MulAut.conjNormal g : MulAut R).toMonoidHom)
        (MulAut.conjNormal g).bijective W).trans hi) hg.symm

end Subgroup
