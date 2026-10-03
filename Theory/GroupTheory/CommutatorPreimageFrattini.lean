module

public import Theory.GroupTheory.CommutatorPreimage
public import Theory.Frattini.PGroupMap

/-!
# Frattini criterion for a commutator-preimage quotient

A quotient of a finite p-group is elementary abelian exactly when its
kernel contains the Frattini subgroup. For a commutator-preimage kernel,
this is equivalent to the actor centralizing the Frattini subgroup modulo
the specified layer. The criterion concerns the actual quotient, without
assuming a chief series or a quotient cardinality.
-/

namespace Subgroup

public theorem elementary_quotient_of_frattini_le
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (hgroup : IsPGroup prime G) (kernel : Subgroup G) [kernel.Normal]
    (hfrattini : frattini G ≤ kernel) : IsElementaryAbelian prime (G ⧸ kernel) := by
  let _ : Fact (IsPGroup prime G) := ⟨hgroup⟩
  refine {
    toIsMulCommutative :=
      (Normal.quotient_commutative_iff_commutator_le (N := kernel)).mpr
        ((commutator_le_frattini_of_isPGroup (p := prime)).trans hfrattini)
    exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro element
  refine QuotientGroup.induction_on element ?_
  intro representative
  exact (QuotientGroup.eq_one_iff (N := kernel) (x := representative ^ prime)).mpr
    (hfrattini (pth_power_mem_frattini_of_isPGroup (p := prime) representative))

public theorem frattini_le_of_elementary_quotient
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (hgroup : IsPGroup prime G) (kernel : Subgroup G) [kernel.Normal]
    (helementary : IsElementaryAbelian prime (G ⧸ kernel)) : frattini G ≤ kernel := by
  let _ : Fact (IsPGroup prime G) := ⟨hgroup⟩
  let _ := helementary
  let _ : Fact (IsPGroup prime (G ⧸ kernel)) :=
    ⟨IsElementaryAbelian.isPGroup prime (G ⧸ kernel)⟩
  have hmap := frattini_map_le_of_isPGroup (p := prime) (QuotientGroup.mk' kernel)
  rw [frattini_eq_bot_of_isElementaryAbelian (R := G ⧸ kernel) (p := prime)] at hmap
  have hkernel := (map_eq_bot_iff (frattini G)).mp (bot_unique hmap)
  simpa only [QuotientGroup.ker_mk'] using hkernel

public theorem commutatorPreimage_quotient_elementary_iff
    {G : Type*} [Group G] [Finite G] {prime : ℕ} [Fact prime.Prime]
    (core actor layer : Subgroup G) (hcore : IsPGroup prime core)
    (hnormalizes : core ≤ normalizer layer)
    [(commutatorPreimage core actor layer).subgroupOf core |>.Normal] :
    IsElementaryAbelian prime
      (core ⧸ (commutatorPreimage core actor layer).subgroupOf core) ↔
      ⁅(frattini core).map core.subtype, actor⁆ ≤ layer := by
  constructor
  · intro helementary
    have hfrattini := frattini_le_of_elementary_quotient hcore
      ((commutatorPreimage core actor layer).subgroupOf core) helementary
    have hmap : (frattini core).map core.subtype ≤ commutatorPreimage core actor layer := by
      rintro element ⟨representative, hrepresentative, rfl⟩
      exact hfrattini hrepresentative
    exact (commutator_mono hmap le_rfl).trans
      (commutator_commutatorPreimage_le core actor layer hnormalizes)
  · intro hcommutator
    have hmap := le_commutatorPreimage (map_subtype_le (frattini core)) hcommutator
    apply elementary_quotient_of_frattini_le hcore
    intro element helement
    exact hmap (mem_map_of_mem core.subtype helement)

end Subgroup
