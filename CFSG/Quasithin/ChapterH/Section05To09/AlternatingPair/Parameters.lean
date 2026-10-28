module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupAction.PrimeOrder

/-!
# Source parameters and the reductions used in H.8

The definitions use the actual pointwise centralizer of a subspace. In `β`,
`O²` is its two-residual. In `α`, the dimension is at least two and the
centralizer has two-rank at least that dimension minus one. Both minima
are in the extended naturals, with an empty family giving infinity.

A maximal elementary subgroup of the centralizer converts absence of
`(F - 1)` offenders to `α = ∞`. Conversely, a subspace of small codimension
whose centralizer has nontrivial two-residual supplies an odd-prime-order
actor of small displacement. The latter implication proves the `β` bound
from element calculations, with the prime-order criterion for two-groups.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Chapter H introduction, printed p.377, and H.8, printed p.389/PDF p.400.
The `m` parameter and fixed-space families are reused from E.3.1 and E.3.8–9.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterH.AlternatingPair

open Representation.BinaryOffender

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The pointwise centralizer of a subspace for the actual action. -/
abbrev centralizer (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V) :
    Subgroup G := subspaceKernel ρ U ⊤

/-- The source `(F - 1)` condition on a nontrivial elementary actor. -/
def IsFMinusOneOffender (ρ : Representation (ZMod 2) G V) (A : Subgroup G) : Prop :=
  IsElementaryTwo A ∧ fixedCodim ρ A ≤ rank A + 1

/-- The source family inside a chosen Sylow subgroup, retained as actual
 subgroups of the original acting group. -/
def sylowFixedSpaceFamily (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (k : ℕ) :
    Set (Subgroup G) :=
  {A | A ≤ (T : Subgroup G) ∧ A ∈ ChapterE.fixedSpaceFamily ρ k}

/-- The minimum in the introduction to Chapter H; an empty family gives infinity. -/
noncomputable def moduleAlpha (ρ : Representation (ZMod 2) G V) : ℕ∞ :=
  ⨅ (U : Submodule (ZMod 2) V)
    (_ : 2 ≤ Module.finrank (ZMod 2) (V ⧸ U) ∧
      Module.finrank (ZMod 2) (V ⧸ U) - 1 ≤ primeRank 2 (centralizer ρ U)),
    (Module.finrank (ZMod 2) (V ⧸ U) : ℕ∞)

/-- Here `O²` is the two-residual of the pointwise centralizer, not its two-core. -/
noncomputable def moduleBeta (ρ : Representation (ZMod 2) G V) : ℕ∞ :=
  ⨅ (U : Submodule (ZMod 2) V) (_ : U < ⊤)
    (_ : pResidual 2 (centralizer ρ U) ≠ ⊥),
    (Module.finrank (ZMod 2) (V ⧸ U) : ℕ∞)

variable [FiniteDimensional (ZMod 2) V]

/-- An involution attaining a common displacement gives the minimum `m`. -/
theorem moduleM_eq_of_constant_involution_codim
    (ρ : Representation (ZMod 2) G V) {d : ℕ}
    (hex : ∃ t : G, orderOf t = 2)
    (hinv : ∀ t : G, orderOf t = 2 → fixedCodim ρ (Subgroup.zpowers t) = d) :
    ChapterE.moduleM ρ = d := by
  obtain ⟨t, ht, hmin⟩ := ChapterE.moduleM_attained ρ hex
  exact hmin.symm.trans (hinv t ht)

private theorem codim_le_quotient_of_fixed
    (ρ : Representation (ZMod 2) G V) (U : Submodule (ZMod 2) V)
    (A : Subgroup G) (h : U ≤ fixedSpace ρ A) :
    fixedCodim ρ A ≤ Module.finrank (ZMod 2) (V ⧸ U) := by
  have := Submodule.finrank_mono h
  have := U.finrank_quotient_add_finrank
  have := fixedCodim_add_finrank ρ A
  omega

variable [Finite G]

/-- The pointwise-centralizer formulation of `α` follows from the absence of
 offenders, by lifting a maximal elementary subgroup of that centralizer. -/
theorem moduleAlpha_eq_top_of_no_offender (ρ : Representation (ZMod 2) G V)
    (hno : ∀ A : Subgroup G, ¬ IsFMinusOneOffender ρ A) : moduleAlpha ρ = ⊤ := by
  apply top_unique
  apply le_iInf
  intro U
  apply le_iInf
  rintro ⟨hdim, hr⟩
  let C := centralizer ρ U
  change Module.finrank (ZMod 2) (V ⧸ U) - 1 ≤ primeRank 2 C at hr
  obtain ⟨E, hE, hc⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 2)
  let _ : IsElementaryAbelian 2 E := hE
  let A := E.map C.subtype
  have hAc : Nat.card A = 2 ^ primeRank 2 C := by
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hc
  have hAr : rank A = primeRank 2 C := by
    rw [rank, hAc, Nat.log_pow (by decide : 1 < 2)]
  have hA0 : A ≠ ⊥ := by
    intro he
    have hz : rank A = 0 := by rw [he, Representation.BinaryOffender.rank_bot]
    change Module.finrank (ZMod 2) (V ⧸ U) - 1 ≤ primeRank 2 C at hr
    omega
  have hAe : IsElementaryTwo A := ⟨hA0, IsElementaryAbelian.map_subtype⟩
  have hU : U ≤ fixedSpace ρ A := by
    intro u hu a
    obtain ⟨e, he, hea⟩ := a.property
    have hf := e.property.2 u hu
    change ρ (a : G) u = u
    change (e : G) = (a : G) at hea
    exact hea ▸ hf
  have hcodim := codim_le_quotient_of_fixed ρ U A hU
  exact (hno A ⟨hAe, by rw [hAr]; omega⟩).elim

/-- Odd-prime displacement bounds give the residual-centralizer bound `β`.
 Cauchy's theorem is used through the prime-order criterion for two-groups. -/
theorem le_moduleBeta_of_odd_prime_codim (ρ : Representation (ZMod 2) G V)
    {d : ℕ}
    (hodd : ∀ x : G, (orderOf x).Prime → orderOf x ≠ 2 →
      d ≤ fixedCodim ρ (Subgroup.zpowers x)) :
    (d : ℕ∞) ≤ moduleBeta ρ := by
  apply le_iInf
  intro U
  apply le_iInf
  intro _
  apply le_iInf
  intro hres
  apply ENat.natCast_le_natCast.mpr
  by_contra hn
  have hsmall : Module.finrank (ZMod 2) (V ⧸ U) < d := Nat.lt_of_not_ge hn
  let C := centralizer ρ U
  have hp : IsPGroup 2 C := by
    apply isPGroup_of_prime_order_eq_p 2 C
    intro x hx
    by_contra hx2
    have horder : orderOf (x : G) = orderOf x := C.orderOf_coe x
    have hlower := hodd (x : G) (horder ▸ hx) (horder ▸ hx2)
    have hu : U ≤ fixedSpace ρ (Subgroup.zpowers (x : G)) := by
      intro u hu
      exact (mem_fixedSpace_zpowers_iff ρ (x : G) u).mpr (x.property.2 u hu)
    have hupper := codim_le_quotient_of_fixed ρ U _ hu
    omega
  have hz : pResidual 2 C = ⊥ := by
    apply le_antisymm _ bot_le
    apply sInf_le
    exact ⟨inferInstance, hp.to_quotient ⊥⟩
  exact hres hz

end CFSG.Quasithin.ChapterH.AlternatingPair
