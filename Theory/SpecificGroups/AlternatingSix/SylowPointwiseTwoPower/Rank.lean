module

public import Theory.SpecificGroups.AlternatingSix.SylowPointwiseTwoPower

/-!
# The size of a two-group fixing an alternating-six Sylow subgroup

If J ≤ Aut(A₆) is a two-group fixing a Sylow subgroup P pointwise, J
centralizes Inn(P). Their join is a two-group, so it lies in a Sylow Q
of Aut(A₆). Order comparison identifies Inn(P) with Q ∩ Inn(A₆).
The marked holomorph model then embeds J into the centralizer of its
inner dihedral group, which is an actual four-group.

This is the numerical consequence of the Sylow action calculation used
in Aschbacher–Smith, E.6.8(2) and 16.1.6. The marked holomorph geometry
is developed on printed pp.568–570 of the combined 1 March 2004 manuscript.
-/

public section
open Subgroup
namespace AlternatingSix.ShadowLocal

/-- A two-subgroup of Aut(A₆) fixing a Sylow subgroup pointwise has order
at most four. No assumption that its actors are inner is imposed. -/
theorem twoSubgroup_fixes_sylow_card_le_four (P : Sylow 2 A6)
    (J : Subgroup AutA6) (hJ : IsPGroup 2 J)
    (hfix : ∀ a ∈ J, ∀ x ∈ (P : Subgroup A6), a x = x) : Nat.card J ≤ 4 := by
  let D := (P : Subgroup A6).map (MulAut.conj : A6 →* AutA6)
  have hD : IsPGroup 2 D := P.isPGroup'.map _
  have hc : J ≤ centralizer (D : Set AutA6) := by
    intro a ha
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    ext y
    simp [hfix a ha x hx]
  have hj : IsPGroup 2 (D ⊔ J : Subgroup AutA6) :=
    hD.to_sup_of_normal_left' hJ (hc.trans (centralizer_le_normalizer _))
  obtain ⟨Q, hQ⟩ := hj.exists_le_sylow
  have hDQ : D ≤ (Q : Subgroup AutA6) := le_sup_left.trans hQ
  have hJQ : J ≤ (Q : Subgroup AutA6) := le_sup_right.trans hQ
  have hDinner : D ≤ inner := by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  have hDcard : Nat.card (D.subgroupOf Q) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,
      card_map_of_injective inner_injective]
    exact alternatingSylow_card P
  have he : D.subgroupOf Q = sylowInner Q :=
    Subgroup.eq_of_le_of_card_ge (fun x hx => hDinner hx)
      (by rw [sylowInner_card, hDcard])
  let e := Identification.sylowEquiv Q
  let B := (J.subgroupOf Q).map e.symm.toMonoidHom
  have hB : B ≤ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    apply e.injective
    simp only [map_mul]
    change e x * e (e.symm a) = e (e.symm a) * e x
    rw [e.apply_symm_apply]
    apply Subtype.ext
    have hxI : e x ∈ sylowInner Q := by
      rw [← Identification.sylowEquiv_innerD Q]
      exact mem_map_of_mem _ hx
    have hxD : (e x : AutA6) ∈ D := by rwa [← he] at hxI
    exact mem_centralizer_iff.mp (hc ha) (e x) hxD
  calc
    Nat.card J = Nat.card (J.subgroupOf Q) :=
      (Nat.card_congr (subgroupOfEquivOfLe hJQ).toEquiv).symm
    _ = Nat.card B := (card_map_of_injective e.symm.injective).symm
    _ ≤ Nat.card (centralizer (Holomorph.innerD : Set Holomorph.Model)) :=
      Nat.card_le_card_of_injective (inclusion hB) (inclusion_injective hB)
    _ = 4 := by
      rw [Nat.card_congr Holomorph.centralizerInnerEquiv.toEquiv]
      simp [Holomorph.E4, Holomorph.C2]

end AlternatingSix.ShadowLocal
