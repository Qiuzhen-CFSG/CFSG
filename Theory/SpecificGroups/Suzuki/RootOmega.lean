module

public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.GroupTheory.PGroup.OmegaAmbient
/-!
# Involutions in the standard Suzuki root group

The square of a root matrix u(a,b) is u(0,a·θ(a)), so it is an
involution or identity precisely when a = 0. The coordinate description
of the center then identifies the first omega subgroup with the center,
which is elementary abelian of order q. These facts concern the concrete
root group; the omega of a nontrivial central cover need not be central.

Source: Huppert–Blackburn, Finite Groups III, XI.3.1; used for the
covered paired Suzuki calculation in Aschbacher–Smith 13.6.6, p.927.
-/

public section
open BenderSuzuki PFAppendixIII Subgroup
namespace BenderSuzuki.MatrixGroups

private theorem rootClosure_square_iff_center (m : ℕ) (hm : 0 < m)
    (x : SuzukiRootClosure m) : x ^ 2 = 1 ↔ x ∈ center (SuzukiRootClosure m) := by
  let F := BinaryGaloisField (2 * m + 1)
  let pi : F ≃+* F := iterateFrobeniusEquiv F 2 (m + 1)
  have hpi : ∀ a : F, pi a = a ^ (2 ^ (m + 1)) :=
    iterateFrobeniusEquiv_def F 2 (m + 1)
  obtain ⟨_, _, _, _, _, _, _, _, hmul, hc, hz, _⟩ :=
    External.huppert_blackburn_XI_3_1 m hm pi
      (External.binaryGaloisField_tits_formula_sq m pi hpi)
  change commutator (SuzukiRootClosure m) = center (SuzukiRootClosure m) at hc
  change ∀ x : SuzukiRootClosure m, x ∈ commutator (SuzukiRootClosure m) ↔
    ∃ b : F, (x : GL (Fin 4) F) = SuzukiRootGL m 0 b at hz
  rw [hc] at hz
  rw [hz]
  constructor
  · intro hsq
    obtain ⟨a, b, hab⟩ := External.suzukiRootGL_mem_closure_iff m pi
      (External.binaryGaloisField_tits_formula_sq m pi hpi) hpi x.val |>.mp x.property
    have he : SuzukiRootGL m 0 (a * pi a) = 1 := by
      have hh := congrArg Subtype.val hsq
      change (x : GL (Fin 4) F) ^ 2 = 1 at hh
      simpa only [hab, pow_two, hmul, CharTwo.add_self_eq_zero, zero_add] using hh
    have ha : a * pi a = 0 := by
      have hh := congrArg (fun z : GL (Fin 4) F => (z : Matrix (Fin 4) (Fin 4) F) 0 2) he
      simpa [SuzukiRootGL, SuzukiRootMatrix] using hh
    have ha0 : a = 0 := (mul_eq_zero.mp ha).elim id (fun h => pi.injective (by simpa using h))
    exact ⟨b, ha0 ▸ hab⟩
  · rintro ⟨b, hb⟩
    apply Subtype.ext
    change (x : GL (Fin 4) F) ^ 2 = 1
    rw [hb, pow_two, hmul]
    simpa only [CharTwo.add_self_eq_zero, map_zero, zero_mul, add_zero] using
      External.suzukiRootGL_zero_zero m

/-- The square-one elements of the standard root group are exactly its center. -/
theorem suzukiRootSubgroup_square_iff_center (m : ℕ) (hm : 0 < m)
    (x : SuzukiRootSubgroup m) : x ^ 2 = 1 ↔ x ∈ center (SuzukiRootSubgroup m) := by
  let e : SuzukiRootSubgroup m ≃* SuzukiRootClosure m :=
    subgroupOfEquivOfLe (suzukiRootClosure_le m)
  have hsq : x ^ 2 = 1 ↔ (e x) ^ 2 = 1 := by
    rw [← map_pow, ← e.map_one, e.injective.eq_iff]
  rw [hsq, rootClosure_square_iff_center m hm]
  constructor
  · intro hx
    exact ((centerCongr e).symm ⟨e x, hx⟩).property
  · intro hx
    exact (centerCongr e ⟨x, hx⟩).property


/-- The first omega is the ambient image of the root-group center. -/
theorem suzukiRootSubgroup_omega_eq_center (m : ℕ) (hm : 0 < m) :
    omegaOneAmbient (SuzukiRootSubgroup m) =
      (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype := by
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hp
    exact ⟨⟨x, hx⟩, (suzukiRootSubgroup_square_iff_center m hm _).mp (Subtype.ext hp), rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl _ y.property
    exact congrArg Subtype.val ((suzukiRootSubgroup_square_iff_center m hm y).mpr hy)

/-- The standard root omega is elementary abelian. -/
theorem suzukiRootSubgroup_omega_elementary (m : ℕ) (hm : 0 < m) :
    IsElementaryAbelian 2 (omegaOneAmbient (SuzukiRootSubgroup m)) := by
  have hc : IsElementaryAbelian 2 (center (SuzukiRootSubgroup m)) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext ((suzukiRootSubgroup_square_iff_center m hm x.val).mpr x.property)) }
  rw [suzukiRootSubgroup_omega_eq_center m hm]
  exact IsElementaryAbelian.map _

/-- The standard root omega has order q. -/
theorem suzukiRootSubgroup_omega_card (m : ℕ) (hm : 0 < m) :
    Nat.card (omegaOneAmbient (SuzukiRootSubgroup m)) = 2 ^ (2 * m + 1) := by
  rw [suzukiRootSubgroup_omega_eq_center m hm, card_map_of_injective (SuzukiRootSubgroup m).subtype_injective]
  exact suzukiRootSubgroup_center_card m hm

end BenderSuzuki.MatrixGroups
