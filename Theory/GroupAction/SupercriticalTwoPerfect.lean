module

public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.PResidual.OddCoreSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Two-perfect actors detected by a supercritical subgroup

Restriction to a supercritical subgroup of an odd p-group has p-group
kernel. Thus it preserves a nontrivial two-subgroup image. If the original
actor is two-perfect and its two-core moves the p-group, the supercritical
subgroup cannot be cyclic: automorphisms of a cyclic group are abelian,
and an abelian image of a two-perfect group has odd order.

Source: the supercritical selection in Aschbacher–Smith 13.3.14(d),
printed p.892, using A.1.21. The action throughout is the original
homomorphism, with no replacement of its image by an abstract automizer.
-/

public section
open Subgroup

namespace IsPPerfect

variable {A B : Type*} [Group A] [CommGroup B] [Finite B]

theorem twoCore_map_eq_bot_of_commutative (hA : IsPPerfect 2 A) (f : A →* B) :
    (pCore 2 A).map f = ⊥ := by
  have hc := coprime_card_of_isPPerfect_commGroup
    (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hP : IsPGroup 2 ((pCore 2 A).map f) := pCore_isPGroup.map f
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hd : Nat.card ((pCore 2 A).map f) ∣ Nat.card f.range :=
    card_dvd_of_le (map_le_range f (pCore 2 A))
  apply Subgroup.card_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes (hc.pow_left n) (hn ▸ dvd_rfl) hd

end IsPPerfect

namespace IsSupercriticalPSubgroup

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

theorem two_image_ne_bot (hX : IsSupercriticalPSubgroup p X)
    (hp : Odd p) (hP : IsPGroup p P)
    {A : Type*} [Group A] (a : A →* MulAut P)
    (B : Subgroup A) (hB : IsPGroup 2 B) (hm : B.map a ≠ ⊥) :
    letI : X.Characteristic := hX.characteristic
    B.map ((MulAut.characteristic X).comp a) ≠ ⊥ := by
  let : X.Characteristic := hX.characteristic
  intro hz
  have hle : B.map a ≤ (MulAut.characteristic X).ker :=
    (Subgroup.map_eq_bot_iff _).mp (by simpa only [map_map] using hz)
  have hd := (hB.map a).disjoint_of_coprime
    (hX.isPGroup_restriction_kernel hP hp) (Nat.coprime_two_left.mpr hp)
  exact hm (le_bot_iff.mp ((le_inf le_rfl hle).trans hd.le_bot))

theorem not_isCyclic_of_twoPerfect_movement (hX : IsSupercriticalPSubgroup p X)
    (hp : Odd p) (hP : IsPGroup p P)
    {A : Type*} [Group A] (hA : IsPPerfect 2 A)
    (a : A →* MulAut P) (hm : (pCore 2 A).map a ≠ ⊥) : ¬ IsCyclic X := by
  intro hc
  let : IsCyclic X := hc
  let : X.Characteristic := hX.characteristic
  let _ := (IsCyclic.mulAutMulEquiv X).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv X).injective
  exact hX.two_image_ne_bot hp hP a _ pCore_isPGroup hm
    (hA.twoCore_map_eq_bot_of_commutative ((MulAut.characteristic X).comp a))

end IsSupercriticalPSubgroup
