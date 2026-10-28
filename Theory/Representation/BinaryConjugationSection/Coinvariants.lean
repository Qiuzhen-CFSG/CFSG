module

public import Theory.Representation.BinaryConjugationSection
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Group generation on a literal binary section

For a supplied binary conjugation section P/U, the original equality
[K,P]U=P implies generation of the module by the corresponding linear
displacements. The actor map retains the chosen marking. Pulling the
commutator space back through the coordinate homomorphism proves the
claim without constructing new section coordinates.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 14.7.73(3), printed pp.1076–1077.
-/

public section

open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection

variable {G D W : Type*} [Group G] [Group D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H P U : Subgroup G} {τ : Representation (ZMod 2) H W}

/-- The original group commutators generate the corresponding binary module. -/
theorem coinvariants_eq_top_of_group_generation
    (d : BinaryConjugationSection H P U τ)
    (K : Subgroup G) (hKH : K ≤ H)
    (ρ : Representation (ZMod 2) D W) (r : K →* D)
    (hact : ∀ k : K, ∀ w, τ ⟨k, hKH k.property⟩ w = ρ (r k) w)
    (hgen : ⁅K, P⁆ ⊔ U = P) : Coinvariants.ker ρ = ⊤ := by
  let C := Coinvariants.ker ρ
  let N : Subgroup G := (C.toAddSubgroup.toSubgroup.comap d.coordinates).map P.subtype
  have hmem (x : P) : (x : G) ∈ N ↔ (d.coordinates x).toAdd ∈ C := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hyx : y = x := Subtype.ext he
      exact hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hUN : U ≤ N := by
    intro u hu
    apply (hmem ⟨u, d.kernel_le hu⟩).mpr
    rw [(d.coordinates_eq_one_iff _).mpr hu]
    exact C.zero_mem
  have hKN : ⁅K, P⁆ ≤ N := by
    apply commutator_le.mpr
    intro k hk x hx
    let kH : H := ⟨k, hKH hk⟩
    let xP : P := ⟨x, hx⟩
    let c : P := (⟨k * x * k⁻¹,
      (mem_normalizer_iff.mp (d.normalized kH.property) x).mp hx⟩ : P) * xP⁻¹
    apply (hmem c).mpr
    rw [map_mul, map_inv]
    change (d.coordinates ⟨k * x * k⁻¹, _⟩).toAdd + -(d.coordinates xP).toAdd ∈ C
    rw [← sub_eq_add_neg, d.equivariant kH xP, hact ⟨k, hk⟩]
    exact Coinvariants.sub_mem_ker _ _
  have hPN : P ≤ N := hgen.ge.trans (sup_le hKN hUN)
  apply top_unique
  intro w _
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd w)
  have hw := (hmem x).mp (hPN x.property)
  rw [hx] at hw
  exact hw

end Representation.BinaryConjugationSection
