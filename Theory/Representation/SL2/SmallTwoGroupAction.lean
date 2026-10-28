module
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.Representation.FrattiniAction
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Frattini.OmegaProducts
public import Theory.ElementaryAbelian.Injective
public import Theory.Quasithin.Rank

/-!
# Small two-groups under perfect rank-one actions

A nontrivial action of a perfect group on a two-group survives on its
Frattini quotient. When the actor has two-core quotient SL₂(2ⁿ), this
binary module has dimension at least 2n. Thus a smaller Frattini quotient
is centralized. An embedding into a group of sectional two-rank below
2n applies this directly to the actor's entire two-core.

Source: Aschbacher--Smith E.2.13(4), printed p.225; used in the proper
two-local inspection of 4.3.16, printed p.618.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace Representation.SL2
variable {H F P : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2] [Group P] [Finite P]

/-- A small Frattini quotient forces the entire perfect action to be trivial. -/
theorem action_eq_one_of_small_frattini
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2^n)
    (hp : IsPGroup 2 P) (hb : primeRank 2 (P ⧸ frattini P) < 2*n)
    (a : H →* MulAut P) : a = 1 := by
  by_contra ha
  let : Fact (IsPGroup 2 P) := ⟨hp⟩
  let W := P ⧸ frattini P
  let : IsElementaryAbelian 2 W := isElementaryAbelian_quotient_frattini
  let b := (quotientAut (frattini P)).comp a
  have hbne : b ≠ 1 := a.frattini_comp_ne_one_of_isPerfect hp ha
  obtain ⟨x,hx⟩ : ∃ x, b x ≠ 1 := by
    by_contra! hh
    exact hbne (MonoidHom.ext hh)
  let ρ := Representation.FrattiniAction.ofAutomorphismHom b
  have hr : ∃ x, ρ x ≠ 1 := by
    by_contra! hh
    exact Representation.FrattiniAction.ofAutomorphismHom_ne_one b x hx (MonoidHom.ext hh)
  have hl := perfect_core_quotient_finrank_bound (V := Additive W) e ρ hr hn hF
  have hc := (primeRank_le_iff_elementary_card_le (p := 2) (n := primeRank 2 W) W).mp le_rfl
    (⊤ : Subgroup W)
      (IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype
        (⊤ : Subgroup W).subtype_injective)
  rw [Nat.card_congr (topEquiv (G := W)).toEquiv] at hc
  have hw : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    change Nat.card (Additive W) = _
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  rw [hw] at hc
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hc
  change primeRank 2 W < 2*n at hb
  omega

end Representation.SL2

namespace Representation.SL2
variable {H F A : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Field F] [Finite F] [CharP F 2] [Group A] [Finite A]

/-- Small sectional rank forces the full two-core of the embedded actor to be central. -/
theorem core_le_center_of_section_rank_bound
    (e : (H ⧸ pCore 2 H) ≃* SL(2,F))
    {n r : ℕ} (hn : n ≠ 0) (hF : Nat.card F = 2^n)
    (f : H →* A) (hf : Function.Injective f)
    (hb : ∀ (B : Subgroup A) (N : Subgroup B) [N.Normal], primeRank 2 (B ⧸ N) ≤ r)
    (hr : r < 2*n) : pCore 2 H ≤ center H := by
  let P := pCore 2 H
  let g := f.comp P.subtype
  have hg : Function.Injective g := hf.comp P.subtype_injective
  let a := MonoidHom.ofInjective hg
  let b := QuotientGroup.congr (frattini P) (frattini g.range) a (frattini_map_equiv a)
  have hsmall : primeRank 2 (P ⧸ frattini P) < 2*n := by
    rw [primeRank_congr 2 b]
    exact (hb g.range (frattini g.range)).trans_lt hr
  have hzero := action_eq_one_of_small_frattini e hn hF pCore_isPGroup hsmall
    (MulAut.conjNormal : H →* MulAut P)
  intro x hx
  apply mem_center_iff.mpr
  intro y
  have he := congrArg (fun a : H →* MulAut P => (a y ⟨x,hx⟩ : H)) hzero
  change y*x*y⁻¹=x at he
  exact mul_inv_eq_iff_eq_mul.mp he
end Representation.SL2

