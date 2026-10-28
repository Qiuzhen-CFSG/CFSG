module

public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

/-!
# The transvection obstruction for the six-letter groups

Every nonidentity involution of A₆ has an inner conjugate whose product
with it has order five. The explicit conjugator is either (12345) or its
square (with zero-based letters); a finite certificate checks these two
choices. A product of two binary transvections has cube or fourth power
one, ruling out a faithful transvection image of that involution.

A subgroup of S₆ whose elements move at most one dimension therefore
intersects A₆ trivially. The sign homomorphism embeds it in the two-element
group. In particular an actor with a common displacement line has order
at most two. The proof applies to every faithful finite-dimensional binary
representation, without identifying distinct natural actions.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), Lemma 13.8.34, printed p.968
(PDF p.985). This supplies its common-center obstruction directly, without
requiring the full classification of transvection groups in G.6.4.
-/

public section

open LinearMap LinearEquiv
namespace Representation.SixLetterTransvections
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem binary (x : ZMod 2) : x = 0 ∨ x = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x

private theorem binary_transvection_of_small_displacement [Module.Finite (ZMod 2) V] (e : V ≃ₗ[ZMod 2] V)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1) :
    e ∈ LinearEquiv.transvections (ZMod 2) V := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h
  have hfv : f v = 0 := by
    rcases binary (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change e.toLinearMap v = 0
      rw [he, LinearMap.transvection.apply, ho, one_smul, ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv, map_zero] at ho
    exact (zero_ne_one ho).elim
  exact LinearEquiv.mem_transvections_iff.mpr ⟨f, v, hfv, by ext x; exact congrArg (fun l : V →ₗ[ZMod 2] V => l x) he⟩

private theorem transvection_product_cube_or_fourth (t u : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V)
    (hu : u ∈ LinearEquiv.transvections (ZMod 2) V) :
    (t * u) ^ 3 = 1 ∨ (t * u) ^ 4 = 1 := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  obtain ⟨g, w, hgw, rfl⟩ := LinearEquiv.mem_transvections_iff.mp hu
  rcases binary (f w) with hfw | hfw <;> rcases binary (g v) with hgv | hgv
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self]
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]
  · right; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]
  · left; ext x
    simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
    match_scalars <;> simp [ZModModule.add_self, add_comm, add_left_comm]

private theorem conjugate_transvection (e t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V) :
    e * t * e⁻¹ ∈ LinearEquiv.transvections (ZMod 2) V := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  let g := f.comp e.symm.toLinearMap
  have hgv : g (e v) = 0 := by simpa [g] using hfv
  apply LinearEquiv.mem_transvections_iff.mpr
  refine ⟨g, e v, hgv, ?_⟩
  ext x
  simp [g, LinearMap.transvection.apply]

private def cycleFive : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5, by
    change Equiv.Perm.sign _ = 1
    decide⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private lemma involution_certificate : ∀ t : alternatingGroup (Fin 6),
    t ≠ 1 → t ^ 2 = 1 →
    ((t * (cycleFive * t * cycleFive⁻¹)) ^ 5 = 1 ∧
      t * (cycleFive * t * cycleFive⁻¹) ≠ 1) ∨
    ((t * (cycleFive ^ 2 * t * (cycleFive ^ 2)⁻¹)) ^ 5 = 1 ∧
      t * (cycleFive ^ 2 * t * (cycleFive ^ 2)⁻¹) ≠ 1) := by
  decide +kernel

private theorem exists_five_product_conjugate (t : alternatingGroup (Fin 6)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : alternatingGroup (Fin 6),
      (t * (g * t * g⁻¹)) ^ 5 = 1 ∧ t * (g * t * g⁻¹) ≠ 1 := by
  rcases involution_certificate t ht ht2 with h | h
  · exact ⟨cycleFive, h⟩
  · exact ⟨cycleFive ^ 2, h⟩

private theorem transvection_square (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ LinearEquiv.transvections (ZMod 2) V) : t ^ 2 = 1 := by
  obtain ⟨f, v, hfv, rfl⟩ := LinearEquiv.mem_transvections_iff.mp ht
  ext x
  simp [pow_succ, LinearMap.transvection.apply, hfv]
  match_scalars <;> simp [ZModModule.add_self]

private theorem no_five_product {G : Type*} [Group G] (e : G →* (V ≃ₗ[ZMod 2] V))
    (he : Function.Injective e) (t g : G)
    (ht : e t ∈ LinearEquiv.transvections (ZMod 2) V)
    (hfive : (t * (g * t * g⁻¹)) ^ 5 = 1)
    (hne : t * (g * t * g⁻¹) ≠ 1) : False := by
  have ht' : e (g * t * g⁻¹) ∈ LinearEquiv.transvections (ZMod 2) V := by
    simpa only [map_mul, map_inv] using conjugate_transvection (e g) (e t) ht
  have hf : (e t * e (g * t * g⁻¹)) ^ 5 = 1 := by
    simpa only [map_mul, map_pow, map_one] using congrArg e hfive
  have hn : e t * e (g * t * g⁻¹) ≠ 1 := by
    intro h
    apply hne
    apply he
    simpa only [map_mul, map_one] using h
  rcases transvection_product_cube_or_fourth (e t) (e (g * t * g⁻¹)) ht ht' with h3 | h4
  · have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf) (orderOf_dvd_of_pow_eq_one h3)
    norm_num at hd
    exact hn (by simpa only [map_mul, map_inv] using hd)
  · have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf) (orderOf_dvd_of_pow_eq_one h4)
    norm_num at hd
    exact hn (by simpa only [map_mul, map_inv] using hd)

/-- An even six-letter permutation cannot move only one dimension in a faithful binary representation unless it is the identity. -/
theorem even_eq_one_of_displacement_le_one [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hρ : Function.Injective ρ) (t : Equiv.Perm (Fin 6))
    (ht : t.sign = 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) : t = 1 := by
  let e : Equiv.Perm (Fin 6) →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hinj : Function.Injective e := fun x y h => hρ (congrArg LinearEquiv.toLinearMap h)
  have htrans : e t ∈ LinearEquiv.transvections (ZMod 2) V := binary_transvection_of_small_displacement (e t) hr
  by_contra hn
  have ht2 : t ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact transvection_square (e t) htrans
  let a : alternatingGroup (Fin 6) := ⟨t, ht⟩
  have ha : a ≠ 1 := fun h => hn (congrArg Subtype.val h)
  have ha2 : a ^ 2 = 1 := Subtype.ext ht2
  obtain ⟨g, hg, hgn⟩ := exists_five_product_conjugate a ha ha2
  apply no_five_product e hinj t g.val htrans
  · exact congrArg Subtype.val hg
  · intro h
    apply hgn
    exact Subtype.ext h

/-- No nonidentity element of A₆ is a transvection in a faithful binary representation. This requires no choice of natural module. -/
theorem alternating_eq_one_of_displacement_le_one [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hρ : Function.Injective ρ) (t : alternatingGroup (Fin 6))
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) : t = 1 := by
  let e : alternatingGroup (Fin 6) →* (V ≃ₗ[ZMod 2] V) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp ρ.asGroupHom
  have hinj : Function.Injective e := fun x y h => hρ (congrArg LinearEquiv.toLinearMap h)
  have htrans : e t ∈ LinearEquiv.transvections (ZMod 2) V := binary_transvection_of_small_displacement (e t) hr
  by_contra hn
  have ht2 : t ^ 2 = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact transvection_square (e t) htrans
  obtain ⟨g, hg, hgn⟩ := exists_five_product_conjugate t hn ht2
  exact no_five_product e hinj t g htrans hg hgn

open Representation.BinaryOffender
private theorem individual_displacement_le_one {G : Type*} [Group G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (h : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1)
    (a : G) (ha : a ∈ A) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1 := by
  refine (Submodule.finrank_mono ?_).trans h
  rintro v ⟨w, rfl⟩
  exact Submodule.subset_span ⟨a, ha, w, Submodule.mem_top, rfl⟩

/-- In a faithful binary representation of A₆ or S₆, a subgroup all of whose elements move at most one dimension has order at most two. In the symmetric case the sign map is injective on that subgroup. -/
theorem card_le_two_of_element_displacements {G : Type*} [Group G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (model : Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 6)))
    (A : Subgroup G)
    (h : ∀ a ∈ A, Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) ≤ 1) :
    Nat.card A ≤ 2 := by
  rcases model with hm | hm
  · obtain ⟨e⟩ := hm
    have hA : A = ⊥ := by
      apply le_antisymm _ bot_le
      intro a ha
      apply e.injective
      rw [map_one]
      apply alternating_eq_one_of_displacement_le_one (ρ.comp e.symm.toMonoidHom) (hρ.comp e.symm.injective) (e a)
      exact h (e.symm (e a)) (by simpa only [e.symm_apply_apply] using ha)
    rw [hA, Subgroup.card_bot]
    decide
  · obtain ⟨e⟩ := hm
    let s := Equiv.Perm.sign.comp (e.toMonoidHom.comp A.subtype)
    have hs : Function.Injective s := by
      apply (MonoidHom.ker_eq_bot_iff s).mp
      apply le_antisymm _ bot_le
      intro a ha
      apply Subtype.ext
      apply e.injective
      change e a.val = e 1
      rw [e.map_one]
      apply even_eq_one_of_displacement_le_one (ρ.comp e.symm.toMonoidHom) (hρ.comp e.symm.injective) (e a) ha
      exact h (e.symm (e a.val)) (by simpa only [e.symm_apply_apply] using a.property)
    have hc := Nat.card_le_card_of_injective s hs
    have hc2 : Nat.card (ℤˣ) = 2 := by rw [Nat.card_eq_fintype_card]; decide
    rwa [hc2] at hc

/-- The common-center obstruction for every faithful binary A₆ or S₆ module, including reducible modules and extensions. -/
theorem card_le_two_of_common_displacement {G : Type*} [Group G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (model : Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 6)))
    (A : Subgroup G)
    (h : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1) :
    Nat.card A ≤ 2 :=
  card_le_two_of_element_displacements ρ hρ model A (individual_displacement_le_one ρ A h)

/-- The logarithmic rank form of the common-center obstruction used in 13.8.34(2). -/
theorem rank_le_one_of_common_displacement {G : Type*} [Group G] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (model : Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 6)))
    (A : Subgroup G)
    (h : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 1) :
    rank A ≤ 1 := by
  have hc := Nat.log_monotone (b := 2) (card_le_two_of_common_displacement ρ hρ model A h)
  change Nat.log 2 (Nat.card A) ≤ 1
  exact hc.trans (by decide : Nat.log 2 2 ≤ 1)
end Representation.SixLetterTransvections
