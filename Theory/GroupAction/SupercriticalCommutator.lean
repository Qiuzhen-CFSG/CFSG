module
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Coprime commutator actors on a supercritical subgroup

Let X = [X,J] act nontrivially on a normal odd p-group P, with |X| prime
to p. Restriction to a supercritical subgroup has p-group kernel, so the
X-image remains nontrivial. The supercritical subgroup cannot be cyclic:
its automorphism group would be abelian and the same commutator identity
would kill the X-image. Both actor images use the literal conjugation map.

Source: Aschbacher–Smith, the supercritical selection in 14.5.11,
printed pp.1015–1016, using A.1.21. The later rank and representation
exclusions are separate from this coprime detection argument.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {D : Type*} [Group D] [Finite D]

/-- Coprime detection preserves the original commutator actor and excludes
the cyclic supercritical model. -/
theorem supercritical_commutator_movement
    (X J P : Subgroup D) [P.Normal] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card X))
    (hcomm : ⁅X,J⁆ = X) (hm : ¬ X ≤ centralizer (P : Set D)) :
    ∃ (R : Subgroup P) (hR : IsSupercriticalPSubgroup p R),
      letI : R.Characteristic := hR.characteristic
      let a := (MulAut.characteristic R).comp
        (MulAut.conjNormal : D →* MulAut P)
      ¬ IsCyclic R ∧ X.map a ≠ ⊥ ∧ ⁅X.map a,J.map a⁆ = X.map a := by
  obtain ⟨R,hR⟩ := hP.exists_supercriticalPSubgroup (by rintro rfl; obtain ⟨k,hk⟩ := hp; omega)
  let : R.Characteristic := hR.characteristic
  let a : D →* MulAut P := MulAut.conjNormal
  let b := (MulAut.characteristic R).comp a
  have hmove : X.map b ≠ ⊥ := by
    intro hz
    have hle : X.map a ≤ (MulAut.characteristic R).ker :=
      (Subgroup.map_eq_bot_iff _).mp (by simpa only [map_map] using hz)
    have hpX : IsPGroup p (X.map a) :=
      (hR.isPGroup_restriction_kernel hP hp).to_le hle
    obtain ⟨n,hn⟩ := hpX.exists_card_eq
    have hcX : Nat.card (X.map a) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hcop.pow_left n)
        (hn ▸ dvd_rfl) (card_dvd_of_surjective (a.subgroupMap X) (a.subgroupMap_surjective X))
    have hzX := (Subgroup.card_eq_one.mp hcX : X.map a = ⊥)
    apply hm
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact (Subgroup.map_eq_bot_iff _).mp hzX
  have he : ⁅X.map b,J.map b⁆ = X.map b := by
    rw [←map_commutator,hcomm]
  refine ⟨R,hR,?_,hmove,he⟩
  intro hcyc
  let : IsCyclic R := hcyc
  let _ := (IsCyclic.mulAutMulEquiv R).toMonoidHom.commGroupOfInjective
    (IsCyclic.mulAutMulEquiv R).injective
  apply hmove
  rw [←he]
  apply le_bot_iff.mp
  apply commutator_le.mpr
  intro x hx y hy
  exact mem_bot.mpr (commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm x y))


end Theory.GroupTheory
