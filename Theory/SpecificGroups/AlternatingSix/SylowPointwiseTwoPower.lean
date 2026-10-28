module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Centralizers
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Dihedral

/-!
# Two-power automorphisms fixing a Sylow subgroup of A₆

An actor fixing a Sylow D₈ commutes with its inner image. If the actor has
power-of-two order, they lie in a common Sylow subgroup of Aut(A₆). The
marked holomorph model identifies the inner image with its distinguished
D₈, whose centralizer lies in the natural S₆. This treats every two-power
actor directly, without reducing its order to two.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.1.6, printed p.1172. The marked Sylow
calculation is developed in `ShadowLocal/Identification` and
`ShadowLocal/HolomorphGeometry/Centralizers` from printed pp.568–570.
-/

public section

open Subgroup
namespace AlternatingSix.ShadowLocal

private theorem model_centralizer_le_natural :
    centralizer (Holomorph.innerD : Set Holomorph.Model) ≤ Holomorph.natural := by
  intro x hx
  rw [Holomorph.centralizer_innerD, Holomorph.mem_centralTwo_sup_transposition] at hx
  rw [Holomorph.mem_natural]
  revert x
  decide +kernel

/-- Every two-power actor fixing a Sylow subgroup of A₆ is induced by an
actual permutation of the six letters. -/
theorem twoPower_mem_natural_of_fixes_sylow (P : Sylow 2 A6) (β : AutA6) {k : ℕ}
    (hβ : β ^ (2 ^ k) = 1) (hfix : ∀ x ∈ (P : Subgroup A6), β x = x) :
    β ∈ natural := by
  let D := (P : Subgroup A6).map (MulAut.conj : A6 →* AutA6)
  have hD : IsPGroup 2 D := P.isPGroup'.map _
  have hc : β ∈ centralizer (D : Set AutA6) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    ext y
    simp [hfix x hx]
  have hz : IsPGroup 2 (zpowers β) := IsPGroup.of_card_dvd_pow (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hβ)
  have hj : IsPGroup 2 (D ⊔ zpowers β : Subgroup AutA6) :=
    hD.to_sup_of_normal_left' hz
      (zpowers_le.mpr (centralizer_le_normalizer _ hc))
  obtain ⟨Q, hQ⟩ := hj.exists_le_sylow
  have hDQ : D ≤ (Q : Subgroup AutA6) := le_sup_left.trans hQ
  have hβQ : β ∈ (Q : Subgroup AutA6) :=
    hQ ((show zpowers β ≤ D ⊔ zpowers β from le_sup_right) (mem_zpowers β))
  have hDinner : D ≤ inner := by rintro _ ⟨x, _, rfl⟩; exact ⟨x, rfl⟩
  have hDcard : Nat.card (D.subgroupOf Q) = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv,
      card_map_of_injective inner_injective]
    exact alternatingSylow_card P
  have he : D.subgroupOf Q = sylowInner Q :=
    Subgroup.eq_of_le_of_card_ge (fun x hx => hDinner hx)
      (by rw [sylowInner_card, hDcard])
  let e := Identification.sylowEquiv Q
  let b := e.symm ⟨β, hβQ⟩
  have hb : b ∈ centralizer (Holomorph.innerD : Set Holomorph.Model) := by
    rw [mem_centralizer_iff]
    intro x hx
    apply e.injective
    apply Subtype.ext
    simp only [map_mul]
    have hxI : e x ∈ sylowInner Q := by
      rw [← Identification.sylowEquiv_innerD Q]
      exact mem_map_of_mem _ hx
    have hxD : (e x : AutA6) ∈ D := by rwa [← he] at hxI
    have hc' := mem_centralizer_iff.mp hc (e x) hxD
    simpa [b] using hc'
  have hbn := model_centralizer_le_natural hb
  have hn : e b ∈ sylowNatural Q := by
    rw [← Identification.sylowEquiv_natural Q]
    exact mem_map_of_mem _ hbn
  have hn' : (e b : AutA6) ∈ natural := hn
  simpa [e, b] using hn'

end AlternatingSix.ShadowLocal
