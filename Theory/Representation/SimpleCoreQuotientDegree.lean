module
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer

/-!
# Binary degree bounds from a simple two-core quotient

A noncentral binary chief factor of a perfect group descends through its
two-core. Simplicity of that quotient makes the descended action faithful.
Every odd prime divisor p of the quotient therefore forces dimension at
least the multiplicative order of 2 modulo p. A nonzero fully moved normal
elementary subgroup has such a chief factor, giving the same lower bound
without irreducibility or splitting assumptions on the whole subgroup.

This supplies a degree comparison for the Suzuki and prime PSL₂ quotients
in the original point configuration of Aschbacher--Smith 10.2.9,
printed pp.750--751.
The degree argument itself is the finite general-linear order formula.
-/

public section
open Subgroup NoncentralChiefRefinement
open scoped IsMulCommutative
namespace Representation.SimpleCoreQuotient
variable {H V : Type*} [Group H] [Finite H]
    [IsSimpleGroup (H ⧸ pCore 2 H)]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A nontrivial irreducible action retains every odd quotient prime. -/
theorem irreducible_prime_degree
    (ρ : Representation (ZMod 2) H V) [ρ.IsIrreducible]
    (hn : ∃ h, ρ h ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card (H ⧸ pCore 2 H)) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  have hk : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let τ := quotientOfLEKer ρ (pCore 2 H) hk
  have hf : Function.Injective τ := by
    apply τ.ker_eq_bot_iff.mp
    rcases (MonoidHom.normal_ker τ).eq_bot_or_eq_top with hb | ht
    · exact hb
    · obtain ⟨h,hh⟩ := hn
      have hz : τ (QuotientGroup.mk' (pCore 2 H) h) = 1 :=
        show _ ∈ τ.ker from ht ▸ mem_top _
      exact (hh hz).elim
  exact BinaryPrimeDegree.orderOf_le_finrank τ hf hp hp2 hd

variable [Group.IsPerfect H]

/-- A noncentral chief factor bounds the dimension of the entire moved subgroup. -/
theorem moved_elementary_prime_finrank
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hmoved : ⁅U,(⊤ : Subgroup H)⁆ = U)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card (H ⧸ pCore 2 H)) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (Additive U) := by
  have hperfect : pResidual 2 H = ⊤ := by
    apply (pResidual_eq_top_iff 2 H).mpr
    intro N hN hn
    let := hN
    by_contra hnt
    let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hnt
    let : Group.IsPerfect (H ⧸ N) := Group.IsPerfect.ofSurjective
      (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (H ⧸ N) := hn.isNilpotent
    exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hex : ∃ i, ¬ s.Central i := by
    by_contra! hall
    have hu := IsElementaryAbelian.isPGroup 2 U
    have hpLast : IsPGroup 2 s.series.last.val := hu.of_equiv
      (MulEquiv.subgroupCongr (congrArg Subtype.val s.last_eq)).symm
    have hc := s.series.residual_commutator_le_head_of_central_steps hpLast hall
    rw [s.head_eq,s.last_eq] at hc
    change ⁅U,pResidual 2 H⁆ ≤ ⊥ at hc
    rw [hperfect,hmoved] at hc
    exact hne (le_bot_iff.mp hc)
  obtain ⟨i,hi⟩ := hex
  let := s.factorRepresentation_irreducible i
  have hn : ∃ h, s.factorRepresentation i h ≠ 1 := by
    by_contra! hn
    apply hi
    rw [s.central_iff_action]
    intro h x
    exact congrArg Additive.toMul (congrArg (fun f => f (Additive.ofMul x)) (hn h))
  have hl := irreducible_prime_degree (s.factorRepresentation i) hn hp hp2 hd
  have hle := LinearMap.finrank_le_finrank_of_surjective (s.factorProjection_surjective i)
  exact hl.trans (hle.trans (Submodule.finrank_le (s.linearTerm i.succ).toSubmodule))

/-- Cardinality form, retaining fixed layers and nonsplit extensions. -/
theorem moved_elementary_prime_card
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hmoved : ⁅U,(⊤ : Subgroup H)⁆ = U)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ Nat.card (H ⧸ pCore 2 H)) :
    2 ^ orderOf (2 : ZMod p) ≤ Nat.card U := by
  have hc : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    change Nat.card (Additive U) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide)
    (moved_elementary_prime_finrank U hne hmoved hp hp2 hd)
end Representation.SimpleCoreQuotient
