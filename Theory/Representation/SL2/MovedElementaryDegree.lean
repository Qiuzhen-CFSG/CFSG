module
public import Theory.Representation.SL2.CoreQuotientDegree
public import Theory.GroupTheory.NoncentralChiefRefinement.UniqueResidualLayer

/-!
# Size of a fully moved binary subgroup above an SL₂ quotient

A nonzero normal elementary two-subgroup of a perfect group, equal to its
commutator with that group, has a noncentral chief factor. Otherwise the
central chief series is centralized by the two-residual, which is the whole
group. The actual chief factor descends through the two-core and has binary
dimension at least twice the defining field exponent. This gives a bound
on the whole subgroup without assuming that it is irreducible or split.

The ambient-subgroup form retains the original inclusion and action. It is
used by the binary triality and Higman–Sims point-component comparisons in
Aschbacher–Smith 10.2.9, pp.750–751; the degree bound is E.2.13(4), p.225.
-/

public section
open Subgroup NoncentralChiefRefinement
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {H F : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2]

/-- The dimension bound on the actual fully moved normal subgroup. -/
theorem moved_elementary_finrank_bound
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hmoved : ⁅U,(⊤ : Subgroup H)⁆ = U)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2 ^ n) :
    2 * n ≤ Module.finrank (ZMod 2) (Additive U) := by
  have hperfect : pResidual 2 H = ⊤ := by
    apply (pResidual_eq_top_iff 2 H).mpr
    intro N hN hp
    let := hN
    by_contra hnt
    let : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.mpr hnt
    let : Group.IsPerfect (H ⧸ N) := Group.IsPerfect.ofSurjective
      (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (H ⧸ N) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hex : ∃ i, ¬ s.Central i := by
    by_contra! hall
    have hp := IsElementaryAbelian.isPGroup 2 U
    have hpLast : IsPGroup 2 s.series.last.val := hp.of_equiv
      (MulEquiv.subgroupCongr (congrArg Subtype.val s.last_eq)).symm
    have hc := s.series.residual_commutator_le_head_of_central_steps hpLast hall
    rw [s.head_eq,s.last_eq] at hc
    change ⁅U,pResidual 2 H⁆ ≤ ⊥ at hc
    rw [hperfect,hmoved] at hc
    exact hne (le_bot_iff.mp hc)
  obtain ⟨i,hi⟩ := hex
  have hd := s.noncentral_factor_finrank_ge_sl2 e i hi n hn hF
  have hle := LinearMap.finrank_le_finrank_of_surjective (s.factorProjection_surjective i)
  exact hd.trans (hle.trans (Submodule.finrank_le (s.linearTerm i.succ).toSubmodule))

/-- The corresponding cardinality bound, including modules with fixed vectors. -/
theorem moved_elementary_card_bound
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hmoved : ⁅U,(⊤ : Subgroup H)⁆ = U)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2 ^ n) : 2 ^ (2 * n) ≤ Nat.card U := by
  have hd := moved_elementary_finrank_bound U hne hmoved e hn hF
  have hc : Nat.card U = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    change Nat.card (Additive U) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive U))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd
end Representation.SL2

namespace Representation.SL2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
/-- The cardinality bound for an actual subgroup of a containing perfect actor. -/
theorem moved_subgroup_card_bound
    (B E : Subgroup G) [Group.IsPerfect B] [IsElementaryAbelian 2 E]
    (hEB : E ≤ B) (hne : E ≠ ⊥) (hm : ⁅E,B⁆ = E)
    (e : (B ⧸ pCore 2 B) ≃* SL(2,F))
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2 ^ n) : 2 ^ (2 * n) ≤ Nat.card E := by
  let U := E.subgroupOf B
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hm.le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hEB
  have hu : U ≠ ⊥ := by
    intro hz
    have hh := congrArg (map B.subtype) hz
    rw [map_subgroupOf_eq_of_le hEB,Subgroup.map_bot] at hh
    exact hne hh
  have hmU : ⁅U,(⊤ : Subgroup B)⁆ = U := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,← MonoidHom.range_eq_map,range_subtype]
    exact hm
  have h := moved_elementary_card_bound U hu hmU e hn hF
  rwa [Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv] at h
end Representation.SL2

namespace Representation.SL2
variable {H F : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2]
/-- The moved subgroup contributes its full two-part in addition to the
original two-core quotient, rather than only a subgroup-order bound. -/
theorem moved_elementary_order_dvd
    (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) (hmoved : ⁅U,(⊤ : Subgroup H)⁆ = U)
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2 ^ n) :
    2 ^ (2 * n) * Nat.card (H ⧸ pCore 2 H) ∣ Nat.card H := by
  have hc := moved_elementary_card_bound U hne hmoved e hn hF
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
  have hnk : 2 * n ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hk ▸ hc)
  have hd : 2 ^ (2 * n) ∣ Nat.card U := hk ▸ pow_dvd_pow 2 hnk
  have hU : U ≤ pCore 2 H := le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩
  have hdcore := hd.trans (card_dvd_of_le hU)
  have hcount : Nat.card H = Nat.card (pCore 2 H) * Nat.card (H ⧸ pCore 2 H) :=
    (pCore 2 H).card_mul_index.symm
  rw [hcount]
  exact Nat.mul_dvd_mul hdcore dvd_rfl
end Representation.SL2
