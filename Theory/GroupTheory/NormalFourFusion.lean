module

public import Theory.GroupTheory.PGroup.RankTwoNormalFour

/-!
# Conjugacy in a noncentral normal four-group

A normal subgroup of order four with a nonidentity central element has just
two other elements. If the subgroup is not central, conjugation interchanges
these two. Therefore one ambient conjugacy from the central element to either
of them fuses all three nonidentity elements.

This elementary action argument is the final fusion reduction in
Janko–Thompson, Math. Z. 113 (1970), Lemma 4.1, printed p.393. It does not
assert the existence of that ambient conjugacy.
-/

namespace Subgroup

/-- The two noncentral elements of a noncentral normal four are conjugate. -/
public theorem normal_four_noncentral_isConj {P : Type*} [Group P] [Finite P]
    (E : Subgroup P) [E.Normal] (hE : Nat.card E = 4)
    (hnot : ¬ E ≤ center P)
    (z : E) (hz : (z : P) ∈ center P) (hz1 : z ≠ 1)
    (x y : E) (hx : x ≠ 1) (hxz : x ≠ z) (hy : y ≠ 1) (hyz : y ≠ z) :
    IsConj (x : P) (y : P) := by
  classical
  obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hnot
  have ha1 : a ≠ 1 := by intro h; exact ha (h ▸ one_mem _)
  have haz : a ≠ z := by intro h; exact ha (h ▸ hz)
  have hmove : ∃ g : P, g * a * g⁻¹ ≠ a := by
    by_contra! h
    apply ha
    rw [mem_center_iff]
    intro g
    exact mul_inv_eq_iff_eq_mul.mp (h g)
  obtain ⟨g, hg⟩ := hmove
  let a' : E := ⟨a, haE⟩
  let b : E := ⟨g * a * g⁻¹, (inferInstance : E.Normal).conj_mem a haE g⟩
  have hab : IsConj (a' : P) (b : P) := isConj_iff.mpr ⟨g, rfl⟩
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    exact isConj_one_left.mp (by simpa only [h, Subgroup.coe_one] using hab)
  have hbz : b ≠ z := by
    intro h
    apply haz
    exact (h ▸ hab).eq_of_right_mem_center hz
  have hba : b ≠ a' := fun h => hg (congrArg Subtype.val h)
  have ha'1 : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  have ha'z : a' ≠ z := fun h => haz (congrArg Subtype.val h)
  let : Fintype E := Fintype.ofFinite E
  have huniv : ({1, z, a', b} : Finset E) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card, hE]
    simp [Ne.symm hz1, Ne.symm ha'1, Ne.symm hb1, Ne.symm ha'z,
      Ne.symm hbz, Ne.symm hba]
  have hcases (v : E) (hv : v ≠ 1) (hvz : v ≠ z) : v = a' ∨ v = b := by
    have hvu : v ∈ ({1, z, a', b} : Finset E) := huniv ▸ Finset.mem_univ v
    simpa only [Finset.mem_insert, Finset.mem_singleton, hv, hvz, false_or] using hvu
  rcases hcases x hx hxz with rfl | rfl <;>
    rcases hcases y hy hyz with rfl | rfl
  · exact IsConj.refl _
  · exact hab
  · exact hab.symm
  · exact IsConj.refl _

/-- One conjugacy joining the central element to another element fuses a
noncentral normal four under any homomorphism to an ambient group. -/
public theorem normal_four_fusion_of_central_isConj
    {P G : Type*} [Group P] [Finite P] [Group G]
    (E : Subgroup P) [E.Normal] (hE : Nat.card E = 4)
    (hnot : ¬ E ≤ center P)
    (z : E) (hz : (z : P) ∈ center P) (hz1 : z ≠ 1)
    (f : P →* G) (u : E) (hu : u ≠ 1) (huz : u ≠ z)
    (hconj : IsConj (f z) (f u)) :
    ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj (f x) (f y) := by
  have hf (v : E) (hv : v ≠ 1) : IsConj (f z) (f v) := by
    by_cases hvz : v = z
    · subst v
      exact IsConj.refl _
    · exact hconj.trans (f.map_isConj
        (normal_four_noncentral_isConj E hE hnot z hz hz1 u v hu huz hv hvz))
  intro x y hx hy
  exact (hf x hx).symm.trans (hf y hy)

end Subgroup
