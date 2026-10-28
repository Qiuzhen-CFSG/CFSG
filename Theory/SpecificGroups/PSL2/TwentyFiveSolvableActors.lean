module
public import Theory.SpecificGroups.PSL2.TwentyFiveCartanNormalizer
public import Theory.GroupTheory.SolvableSylowOvergroups.OddActors
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Quintic actors above a normal PSL₂(25)

Dickson's classification shows that a solvable full-Sylow overgroup in
PSL₂(25) has order prime to five. Its two-part is at least eight, excluding
the A₅ and affine rows; the torus rows and A₄/S₄ have prime-to-five order,
and the projective subfield rows are nonsolvable.

The actual two-group outer quotient then detects a faithful quintic actor
inside such a solvable subgroup. This excludes quintic actors on a normal
PSL₂(25) whenever their ambient Sylow join is solvable, with the action
kernel kept as the centralizer of the actual normal subgroup.

Source: Huppert II.8.27 (Dickson), applied in Aschbacher–Smith
5.1.13 and 5.2.2, printed pp.636–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace Theory.PSL2.TwentyFive
variable {F : Type*} [Field F] [Finite F]

/-- Solvable full-Sylow overgroups of PSL₂(25) are prime to five. -/
theorem solvable_sylow_not_five (hF : Nat.card F = 25)
    (S : Sylow 2 (PSL2MatrixGroup F)) (H : Subgroup (PSL2MatrixGroup F))
    (hSH : (S : Subgroup _) ≤ H) [Group.IsSolvable H] : ¬ 5 ∣ Nat.card H := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h8 : 8 ∣ Nat.card H :=
    (S.pow_dvd_card_of_pow_dvd_card (n := 3) (by rw [card hF]; decide)).trans
      (card_dvd_of_le hSH)
  intro h5
  have hsmall (hc : Nat.card H ∣ 24 ∨ Nat.card H ∣ 26 ∨ Nat.card H ∣ 60) : False := by
    rcases hc with hc | hc | hc
    · exact (by decide : ¬ 5 ∣ 24) (h5.trans hc)
    · exact (by decide : ¬ 5 ∣ 26) (h5.trans hc)
    · exact (by decide : ¬ 8 ∣ 60) (h8.trans hc)
  have hFp : Nat.card F = 5 ^ 2 := hF
  rcases Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification hFp H with
    hEl | hCy | hDi | hA4 | hS4 | hA5 | hAff | hPSL | hPGL
  · let := hEl
    obtain ⟨a,ha⟩ := (IsElementaryAbelian.isPGroup 5 H).exists_card_eq
    have hh : 2 ∣ 5 ^ a := ha ▸ (dvd_trans (by decide : 2 ∣ 8) h8)
    have hh := Nat.prime_two.dvd_of_dvd_pow hh
    norm_num at hh
  · obtain ⟨a,ha,hc,_⟩ := hCy
    norm_num [hF] at ha
    apply hsmall
    rw [hc]
    rcases ha with ha | ha
    · exact .inl (ha.trans (by decide))
    · exact .inr (.inl (ha.trans (by decide)))
  · obtain ⟨a,ha,hc,_⟩ := hDi
    norm_num [hF] at ha
    apply hsmall
    rw [hc]
    rcases ha with ha | ha
    · exact .inl (Nat.mul_dvd_mul_left 2 ha)
    · exact .inr (.inl (Nat.mul_dvd_mul_left 2 ha))
  · obtain ⟨_,⟨e⟩⟩ := hA4
    apply hsmall
    left
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  · obtain ⟨_,⟨e⟩⟩ := hS4
    apply hsmall
    left
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    norm_num
  · obtain ⟨_,⟨e⟩⟩ := hA5
    apply hsmall
    right; right
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  · obtain ⟨a,t,_,ht,N,C,hN,_,hcN,_,hcC,hdisj,hsup⟩ := hAff
    let := hN
    have hc : Nat.card H = 5 ^ a * t := by
      have hh := card_sup_eq_mul_of_normalizes_of_disjoint N C
        (by rw [N.normalizer_eq_top]; exact le_top) hdisj
      simpa [hsup,hcN,hcC] using hh
    rw [hc] at h8
    have ht8 : 8 ∣ t := ((by decide : Nat.Coprime 8 5).pow_right a).dvd_of_dvd_mul_left h8
    norm_num at ht
    exact (by decide : ¬ 8 ∣ 12) (ht8.trans ht)
  · obtain ⟨a,ha,had,⟨e⟩⟩ := hPSL
    have hac : Nat.card (GaloisField 5 a) = 5 ^ a := GaloisField.card 5 a ha
    have hl : 3 < Nat.card (GaloisField 5 a) := by
      rw [hac]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 5) (Nat.one_le_iff_ne_zero.mpr ha)
      norm_num at hh
      omega
    let : Group.IsPerfect (PSL2MatrixGroup (GaloisField 5 a)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ hl
    exact Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField 5 a))
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  · obtain ⟨a,ha,had,⟨e⟩⟩ := hPGL
    have hac : Nat.card (GaloisField 5 a) = 5 ^ a := GaloisField.card 5 a ha
    have hl : 3 < Nat.card (GaloisField 5 a) := by
      rw [hac]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 5) (Nat.one_le_iff_ne_zero.mpr ha)
      norm_num at hh
      omega
    let : Group.IsPerfect (PSL2MatrixGroup (GaloisField 5 a)) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ hl
    let : Group.IsSolvable (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 5 a)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact Group.IsPerfect.not_isSolvable (PSL2MatrixGroup (GaloisField 5 a))
      (Group.isSolvable_of_isSolvable_injective
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := GaloisField 5 a)))
end Theory.PSL2.TwentyFive

namespace Theory.PSL2.TwentyFive
variable {G : Type*} [_root_.Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F]

/-- A quintic actor cannot generate a solvable Sylow join over a normal PSL₂(25). -/
theorem no_five_actor (K E : Subgroup G) [K.Normal]
    (hF : Nat.card F = 25) (e : K ≃* PSL2MatrixGroup F) (S : Sylow 2 G)
    (hE : Nat.card E = 5) (hd : Disjoint E (centralizer (K : Set G)))
    (hs : Group.IsSolvable (E ⊔ (S : Subgroup G) : Subgroup G)) : False := by
  have hz : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := (centerCongr e ⟨x,hx⟩).property
    change e x ∈ center (PSL2MatrixGroup F) at hh
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
    exact e.map_eq_one_iff.mp hh
  have hout : IsPGroup 2 (MulAut.Outer K) :=
    (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (by decide : Nat.Prime 5) (by decide : Odd 5) (by decide : 2 ≤ 2)
      (show Nat.card F = 5 ^ 2 from hF)).of_equiv (MulAut.outerCongr e).symm
  apply no_odd_actor_of_solvable_sylow_bound K E S (by decide : Odd 5) hz hout _ hE hd hs
  intro P J hJ hPJ
  let := hJ
  have hsol : Group.IsSolvable (J.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective J)
  have hh := solvable_sylow_not_five hF (P.mapSurjective e.surjective)
    (J.map e.toMonoidHom) (map_mono hPJ)
  rwa [card_map_of_injective e.injective] at hh
end Theory.PSL2.TwentyFive
