module

public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Omega and Frattini orders in abelian two-groups

For a finite abelian two-group, the first omega subgroup and the Frattini
quotient have the same order. Indeed the square homomorphism has first omega
as its kernel and the Frattini subgroup as its range. The first isomorphism
theorem then gives the equality of orders. In particular, a first omega
subgroup of order four gives a Klein four Frattini quotient.

This is the elementary input to the abelian Sylow reduction in
Janko–Thompson, Math. Z. 113 (1970), §6, p.394. It does not assert the
ambient simple-group theorem of Brauer cited there.
-/

open scoped IsMulCommutative

namespace IsPGroup

/-- The square kernel is first omega in an abelian group. -/
public theorem square_ker_eq_omega_one
    {A : Type*} [CommGroup A] :
    (powMonoidHom 2 : A →* A).ker = omega₁ A (p := 2) := by
  apply le_antisymm
  · intro x hx
    exact Subgroup.subset_closure (by simpa using hx)
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    simpa using hx

/-- Squares form the Frattini subgroup of a finite abelian two-group. -/
public theorem square_range_eq_frattini
    {A : Type*} [CommGroup A] [Finite A] (hA : IsPGroup 2 A) :
    (powMonoidHom 2 : A →* A).range = frattini A := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let R := (powMonoidHom 2 : A →* A).range
  have hR : IsElementaryAbelian 2 (A ⧸ R) := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective R q
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := R) _).mpr ⟨a, rfl⟩
  let : IsElementaryAbelian 2 (A ⧸ R) := hR
  let : Fact (IsPGroup 2 (A ⧸ R)) := ⟨hA.to_quotient R⟩
  have hphi : frattini (A ⧸ R) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := 2)
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    exact pth_power_mem_frattini_of_isPGroup (p := 2) a
  · have h := frattini_le_comap_frattini_of_surjective
      (φ := QuotientGroup.mk' R) (QuotientGroup.mk'_surjective R)
    simpa only [hphi, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using h

/-- First omega and the Frattini quotient of a finite abelian two-group
have equal orders. -/
public theorem card_frattini_quotient_eq_card_omega_one
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) :
    Nat.card (A ⧸ frattini A) = Nat.card (omega₁ A (p := 2)) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  rw [← hA.square_range_eq_frattini, ← Subgroup.index_eq_card,
    Subgroup.index_range, square_ker_eq_omega_one]

/-- Four involutions including the identity give a Klein four Frattini quotient. -/
public theorem isKleinFour_frattini_quotient_of_card_omega_one_eq_four
    {A : Type*} [Group A] [Finite A] [IsMulCommutative A]
    (hA : IsPGroup 2 A) (hfour : Nat.card (omega₁ A (p := 2)) = 4) :
    IsKleinFour (A ⧸ frattini A) := by
  have hcard : Nat.card (A ⧸ frattini A) = 4 :=
    hA.card_frattini_quotient_eq_card_omega_one.trans hfour
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  let : Nontrivial (A ⧸ frattini A) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩

end IsPGroup
