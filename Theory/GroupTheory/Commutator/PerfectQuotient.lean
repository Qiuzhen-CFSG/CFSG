module

public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect quotients and the derived subgroup

For a surjection `f : E → Q` onto a perfect group, the kernel of `f` and
the derived subgroup of `E` generate `E`.  If their intersection is trivial,
the restriction of `f` to the derived subgroup is an isomorphism, whose inverse
gives a group-homomorphic section of `f`.  Thus every nonsplit extension of a
perfect group has nontrivial intersection between its kernel and its derived
subgroup.

This elementary reduction isolates the group-theoretic part of the Schur-cover
argument used by Alperin--Brauer--Gorenstein in Chapter II, Section 3,
Proposition 2 (article p.22).  The later classification step must determine the
size of that intersection and recognize the resulting perfect central cover.
-/

namespace CentralExtension

open Subgroup

variable {E Q : Type*} [Group E] [Group Q]

/-- The kernel and derived subgroup generate the domain of a surjection onto a
perfect group. -/
public theorem ker_sup_commutator_eq_top_of_surjective
    [Group.IsPerfect Q] (f : E →* Q) (hf : Function.Surjective f) :
    f.ker ⊔ commutator E = ⊤ := by
  have hmap : (commutator E).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  apply top_unique
  intro x _
  have hx : f x ∈ (commutator E).map f := by
    rw [hmap]
    trivial
  obtain ⟨d, hd, hdx⟩ := hx
  have hk : x * d⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hdx]
    simp
  have hkd : (x * d⁻¹) * d ∈ f.ker ⊔ commutator E :=
    (f.ker ⊔ commutator E).mul_mem
      ((show f.ker ≤ f.ker ⊔ commutator E from le_sup_left) hk)
      ((show commutator E ≤ f.ker ⊔ commutator E from le_sup_right) hd)
  simpa using hkd

/-- A surjection onto a perfect group splits when its kernel is disjoint from
the derived subgroup of its domain. -/
public theorem exists_section_of_ker_inf_commutator_eq_bot
    [Group.IsPerfect Q] (f : E →* Q) (hf : Function.Surjective f)
    (hdisj : f.ker ⊓ commutator E = ⊥) :
    ∃ s : Q →* E, f.comp s = MonoidHom.id Q := by
  let D := commutator E
  let fD : D →* Q := f.comp D.subtype
  have hfD : Function.Surjective fD := by
    have hmap : D.map f = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map f := by
      rw [hmap]
      trivial
    obtain ⟨d, hd, hdy⟩ := hy
    exact ⟨⟨d, hd⟩, hdy⟩
  have hfDinj : Function.Injective fD := by
    intro x y hxy
    apply Subtype.ext
    have hker : x.1 / y.1 ∈ f.ker := MonoidHom.mem_ker.mpr (by
      rw [map_div]
      change fD x / fD y = 1
      rw [hxy]
      simp)
    have hD : x.1 / y.1 ∈ D := D.div_mem x.2 y.2
    have : x.1 / y.1 ∈ f.ker ⊓ commutator E := ⟨hker, by simpa [D] using hD⟩
    rw [hdisj] at this
    exact div_eq_one.mp (Subgroup.mem_bot.mp this)
  let e : D ≃* Q := MulEquiv.ofBijective fD ⟨hfDinj, hfD⟩
  let s : Q →* E := D.subtype.comp e.symm.toMonoidHom
  refine ⟨s, ?_⟩
  apply MonoidHom.ext
  intro y
  change fD (e.symm y) = y
  exact e.apply_symm_apply y

/-- The kernel of a nonsplit extension of a perfect group meets the derived
subgroup nontrivially. -/
public theorem ker_inf_commutator_ne_bot_of_no_section
    [Group.IsPerfect Q] (f : E →* Q) (hf : Function.Surjective f)
    (hnonsplit : ¬ ∃ s : Q →* E, f.comp s = MonoidHom.id Q) :
    f.ker ⊓ commutator E ≠ ⊥ := by
  intro hbot
  exact hnonsplit (exists_section_of_ker_inf_commutator_eq_bot f hf hbot)

/-- The quotient kernel and derived subgroup generate a group whose quotient is
perfect. -/
public theorem quotientKernel_sup_commutator_eq_top
    (Z : Subgroup E) [Z.Normal] [Group.IsPerfect (E ⧸ Z)] :
    Z ⊔ commutator E = ⊤ := by
  simpa only [QuotientGroup.ker_mk'] using
    ker_sup_commutator_eq_top_of_surjective (QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z)

/-- In a nonsplit extension with perfect quotient, the quotient kernel meets
the derived subgroup nontrivially. -/
public theorem quotientKernel_inf_commutator_ne_bot_of_no_section
    (Z : Subgroup E) [Z.Normal] [Group.IsPerfect (E ⧸ Z)]
    (hnonsplit : ¬ ∃ s : (E ⧸ Z) →* E,
      (QuotientGroup.mk' Z).comp s = MonoidHom.id (E ⧸ Z)) :
    Z ⊓ commutator E ≠ ⊥ := by
  simpa only [QuotientGroup.ker_mk'] using
    ker_inf_commutator_ne_bot_of_no_section (QuotientGroup.mk' Z)
      (QuotientGroup.mk'_surjective Z) hnonsplit

/-- A bound of two on the derived part of a nonsplit quotient kernel is sharp. -/
public theorem quotientKernel_inf_commutator_card_eq_two_of_no_section_of_card_le_two
    [Finite E] (Z : Subgroup E) [Z.Normal] [Group.IsPerfect (E ⧸ Z)]
    (hnonsplit : ¬ ∃ s : (E ⧸ Z) →* E,
      (QuotientGroup.mk' Z).comp s = MonoidHom.id (E ⧸ Z))
    (hcard : Nat.card ↑(Z ⊓ commutator E) ≤ 2) :
    Nat.card ↑(Z ⊓ commutator E) = 2 := by
  let : Nontrivial ↑(Z ⊓ commutator E) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr
      (quotientKernel_inf_commutator_ne_bot_of_no_section Z hnonsplit)
  apply Nat.le_antisymm hcard
  exact (Nat.succ_le_iff).mpr Finite.one_lt_card

end CentralExtension
