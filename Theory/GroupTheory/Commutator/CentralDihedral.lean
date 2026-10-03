module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# Central derived elements of a dihedral cover

A finite central extension of a finite dihedral group has at most two
elements in the intersection of its center and derived subgroup. Choose
lifts of a rotation and a reflection. Their commutator commutes with the
rotation and is inverted by the reflection, so its cyclic subgroup is normal.
The quotient is abelian, so the cyclic subgroup contains the whole derived
subgroup. A central element in this cyclic subgroup equals its inverse,
and a cyclic group of exponent at most two has order at most two.

This is the elementary dihedral calculation used with Sylow transfer in the
two-primary Schur-cover argument for Alperin--Brauer--Gorenstein, Chapter II,
Section 3, Proposition 2. The kernel is only assumed central; no cyclicity,
prime-power order, or multiplier formula is an input.
-/

open scoped commutatorElement
open Subgroup

namespace CentralExtension

private theorem commutator_conj_relations
    {G : Type*} [Group G] (r s : G)
    (hs : s ^ 2 ∈ center G)
    (hr : s * r * s⁻¹ * r ∈ center G) :
    Commute r ⁅s, r⁆ ∧ s * ⁅s, r⁆ * s⁻¹ = ⁅s, r⁆⁻¹ := by
  let a := s * r * s⁻¹ * r
  have hform : s * r * s⁻¹ = a * r⁻¹ := by dsimp [a]; group
  have hacomm : Commute a r := (mem_center_iff.mp hr r).symm
  have htcomm : Commute (s * r * s⁻¹) r := by
    rw [hform]
    exact hacomm.mul_left (Commute.refl r).inv_left
  have hrc : Commute r ⁅s, r⁆ := by
    change r * (s * r * s⁻¹ * r⁻¹) = (s * r * s⁻¹ * r⁻¹) * r
    calc
      r * (s * r * s⁻¹ * r⁻¹) = (r * (s * r * s⁻¹)) * r⁻¹ := by group
      _ = ((s * r * s⁻¹) * r) * r⁻¹ := by rw [htcomm.eq]
      _ = (s * r * s⁻¹ * r⁻¹) * r := by group
  have hsconj : s * (s * r * s⁻¹) * s⁻¹ = r := by
    calc
      s * (s * r * s⁻¹) * s⁻¹ = s ^ 2 * r * (s ^ 2)⁻¹ := by
        simp only [pow_two]; group
      _ = r := by rw [← (mem_center_iff.mp hs r)]; group
  refine ⟨hrc, ?_⟩
  calc
    s * ⁅s, r⁆ * s⁻¹ =
        (s * (s * r * s⁻¹) * s⁻¹) * (s * r * s⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
    _ = r * (s * r * s⁻¹)⁻¹ := by rw [hsconj]
    _ = ⁅s, r⁆⁻¹ := by simp only [commutatorElement_def]; group

private theorem eq_top_of_dihedral_lifts
    {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (f : G →* DihedralGroup n) (r s : G)
    (hr : f r = DihedralGroup.r 1) (hs : f s = DihedralGroup.sr 0)
    (H : Subgroup G) (hker : f.ker ≤ H) (hrH : r ∈ H) (hsH : s ∈ H) :
    H = ⊤ := by
  apply top_unique
  intro g _
  have lift_mem (d : G) (hd : d ∈ H) (hfd : f d = f g) : g ∈ H := by
    have hk : g * d⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hfd, mul_inv_cancel]
    simpa using H.mul_mem (hker hk) hd
  cases hfg : f g with
  | r i =>
      apply lift_mem (r ^ i.val) (H.pow_mem hrH i.val)
      simp [map_pow, hr, hfg]
  | sr i =>
      apply lift_mem (s * r ^ i.val) (H.mul_mem hsH (H.pow_mem hrH i.val))
      simp [map_pow, hr, hs, hfg]

private theorem derived_le_lift_commutator
    {G : Type*} [Group G] {n : ℕ} [NeZero n]
    (f : G →* DihedralGroup n) (hker : f.ker ≤ center G)
    (r s : G) (hr : f r = DihedralGroup.r 1) (hs : f s = DihedralGroup.sr 0) :
    _root_.commutator G ≤ zpowers ⁅s, r⁆ ∧
      s * ⁅s, r⁆ * s⁻¹ = ⁅s, r⁆⁻¹ := by
  have hs2 : s ^ 2 ∈ center G := by
    apply hker
    simp [MonoidHom.mem_ker, hs, pow_two]
  have hsr : s * r * s⁻¹ * r ∈ center G := by
    apply hker
    simp [MonoidHom.mem_ker, hr, hs, map_mul, map_inv]
  obtain ⟨hrc, hsc⟩ := commutator_conj_relations r s hs2 hsr
  let C : Subgroup G := zpowers ⁅s, r⁆
  have hnorm : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_of_dihedral_lifts f r s hr hs
    · intro k hk
      rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      congr 1
      change k * ⁅s, r⁆ * k⁻¹ = ⁅s, r⁆
      rw [← mem_center_iff.mp (hker hk) ⁅s, r⁆]
      group
    · rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      congr 1
      change r * ⁅s, r⁆ * r⁻¹ = ⁅s, r⁆
      rw [hrc.eq]
      group
    · rw [mem_normalizer_iff_map_conj_eq]
      dsimp [C]
      rw [MonoidHom.map_zpowers]
      change zpowers (s * ⁅s, r⁆ * s⁻¹) = zpowers ⁅s, r⁆
      rw [hsc, zpowers_inv]
  let : C.Normal := hnorm
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  have hqcomm : Commute (q s) (q r) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_zpowers ⁅s, r⁆)
  have hqker (k : G) (hk : k ∈ f.ker) : q k ∈ center (G ⧸ C) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    simpa only [map_mul] using congrArg q (mem_center_iff.mp (hker hk) x)
  have hqcentral (a : G) (har : Commute (q a) (q r))
      (has : Commute (q a) (q s)) : q a ∈ center (G ⧸ C) := by
    have hH : (centralizer ({q a} : Set (G ⧸ C))).comap q = ⊤ := by
      apply eq_top_of_dihedral_lifts f r s hr hs
      · intro k hk
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp (hqker k hk) (q a)).symm
      · exact mem_centralizer_singleton_iff.mpr har.eq.symm
      · exact mem_centralizer_singleton_iff.mpr has.eq.symm
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    have hx : q x ∈ centralizer ({q a} : Set (G ⧸ C)) := by
      change x ∈ (centralizer ({q a} : Set (G ⧸ C))).comap q
      rw [hH]; trivial
    exact mem_centralizer_singleton_iff.mp hx
  have hqr := hqcentral r (Commute.refl _) hqcomm.symm
  have hqs := hqcentral s hqcomm (Commute.refl _)
  have htop : (center (G ⧸ C)).comap q = ⊤ :=
    eq_top_of_dihedral_lifts f r s hr hs _ hqker hqr hqs
  have habel : IsMulCommutative (G ⧸ C) := by
    apply center_eq_top_iff.mp
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C y
    change x ∈ (center (G ⧸ C)).comap q
    rw [htop]; trivial
  exact ⟨Normal.quotient_commutative_iff_commutator_le.mp habel, hsc⟩

/-- A central extension of a finite dihedral group has at most two central
elements in its derived subgroup. The central kernel need not be cyclic. -/
public theorem card_center_inf_commutator_le_two_of_dihedral
    {G : Type*} [Group G] [Finite G] {n : ℕ} [NeZero n]
    (f : G →* DihedralGroup n) (hf : Function.Surjective f)
    (hker : f.ker ≤ center G) :
    Nat.card (center G ⊓ _root_.commutator G : Subgroup G) ≤ 2 := by
  obtain ⟨r, hr⟩ := hf (DihedralGroup.r 1)
  obtain ⟨s, hs⟩ := hf (DihedralGroup.sr 0)
  obtain ⟨hderived, hconj⟩ := derived_le_lift_commutator f hker r s hr hs
  let H : Subgroup G := center G ⊓ _root_.commutator G
  have hH : H ≤ zpowers ⁅s, r⁆ := inf_le_right.trans hderived
  let : IsCyclic H := isCyclic_of_le hH
  obtain ⟨x, hxorder⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have hxinv : s * (x : G) * s⁻¹ = (x : G)⁻¹ := by
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hH x.property)
    rw [← hi, ← conj_zpow, hconj, inv_zpow]
  have hxcenter : (x : G) ∈ center G := x.property.1
  have hxself : s * (x : G) * s⁻¹ = (x : G) := by
    rw [mem_center_iff.mp hxcenter s]
    group
  have hxsq : x ^ 2 = 1 := by
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    calc
      (x : G) ^ 2 = (x : G) * (x : G) := pow_two _
      _ = (x : G)⁻¹ * (x : G) := congrArg (fun y : G => y * (x : G)) (hxself.symm.trans hxinv)
      _ = 1 := inv_mul_cancel _
  have hcard : Nat.card H ∣ 2 := by
    rw [← hxorder]
    exact orderOf_dvd_of_pow_eq_one hxsq
  exact Nat.le_of_dvd (by decide) hcard

end CentralExtension
