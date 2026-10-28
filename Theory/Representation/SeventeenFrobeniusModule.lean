module

public import Theory.Representation.SeventeenFrobeniusModule.Orbit
public import Theory.Representation.SeventeenFrobeniusModule.CyclicFixed
public import Theory.Representation.ScalarDescent
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.NilpotentIndecomposable
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Binary modules for a literal 17:8 pair

Let `ρ` be faithful of binary degree eight, and suppose `x` and `r` have orders
seventeen and eight with `r*x*r⁻¹=x²`. Over an algebraic closure, the eight
translates of a nontrivial root eigenvector form a cyclic permutation basis.
The first, second and fourth powers of the complement therefore have fixed
dimensions one, two and four. Flat scalar extension preserves the kernels of
the displacement maps, so these dimensions descend to the original module.
Rank-nullity gives codimensions seven, six and four. In characteristic two the
complement is unipotent, and its fixed line implies indecomposability, expressing
the source's single-block assertion on the actual polynomial module.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript p.9, used in Aschbacher--Smith K.2, printed p.453.
-/

open Module
namespace Representation.SeventeenFrobeniusModule
open BinaryOffender
open scoped _root_.TensorProduct
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
private theorem ker_sub_one_eq_fixedSpace (ρ : Representation (ZMod 2) G V) (s : G) :
    (ρ s - 1).ker = fixedSpace ρ (Subgroup.zpowers s) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff]
  exact sub_eq_zero

/-- A literal `17:8` pair on a faithful binary module of degree eight has
fixed dimensions `1`, `2` and `4` for the indicated complement powers. -/
public theorem finrank_fixedSpace_pow (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2)
    (k : ℕ) (hk : k = 1 ∨ k = 2 ∨ k = 4) :
    finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers (r ^ k))) = k := by
  let E := AlgebraicClosure (ZMod 2)
  let τ := extendScalars E ρ
  have hfτ : Function.Injective τ := (extendScalars_faithful_iff E ρ).mp hf
  have hdτ : finrank E (E ⊗[ZMod 2] V) = 8 := by
    simpa only [Module.finrank_baseChange] using hd
  have h17 : (17 : E) ≠ 0 := by
    intro hz
    have hbase : (17 : ZMod 2) = 0 := by
      apply (algebraMap (ZMod 2) E).injective
      rw [map_ofNat, map_zero]
      exact hz
    exact (by decide : (17 : ZMod 2) ≠ 0) hbase
  obtain ⟨b, hb⟩ := exists_cyclic_basis τ hfτ hdτ x r hx hr hrel h17
  have hcalc := finrank_ker_of_cycle_basis τ r b hb k hk
  have he : (ρ (r⁻¹ ^ k) - 1).baseChange E = τ (r⁻¹ ^ k) - 1 := by
    rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]
    rfl
  have hdim := (LinearMap.kerBaseChangeEquiv (E := E) (ρ (r⁻¹ ^ k) - 1)).finrank_eq
  rw [Module.finrank_baseChange, he, hcalc, ker_sub_one_eq_fixedSpace,
    inv_pow, Subgroup.zpowers_inv] at hdim
  exact hdim

/-- The three fixed-space dimensions for the generator, its square and its
fourth power. Neither absolute irreducibility nor a chosen model is assumed. -/
public theorem fixed_dimensions (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers r)) = 1 ∧
    finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers (r ^ 2))) = 2 ∧
    finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers (r ^ 4))) = 4 := by
  refine ⟨?_, finrank_fixedSpace_pow ρ hf hd x r hx hr hrel 2 (by simp),
    finrank_fixedSpace_pow ρ hf hd x r hx hr hrel 4 (by simp)⟩
  have hh := finrank_fixedSpace_pow ρ hf hd x r hx hr hrel 1 (by simp)
  rw [_root_.pow_one] at hh
  exact hh

/-- The corresponding fixed codimensions are seven, six and four. -/
public theorem fixed_codimensions (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    fixedCodim ρ (Subgroup.zpowers r) = 7 ∧
    fixedCodim ρ (Subgroup.zpowers (r ^ 2)) = 6 ∧
    fixedCodim ρ (Subgroup.zpowers (r ^ 4)) = 4 := by
  obtain ⟨h1, h2, h4⟩ := fixed_dimensions ρ hf hd x r hx hr hrel
  have hc1 := fixedCodim_add_finrank ρ (Subgroup.zpowers r)
  have hc2 := fixedCodim_add_finrank ρ (Subgroup.zpowers (r ^ 2))
  have hc4 := fixedCodim_add_finrank ρ (Subgroup.zpowers (r ^ 4))
  omega

/-- The complement acts as a single size-eight unipotent block: its
nilpotent displacement has eighth power zero, and the polynomial module with
variable acting by the complement is indecomposable. -/
public theorem single_block (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 8)
    (x r : G) (hx : orderOf x = 17) (hr : orderOf r = 8)
    (hrel : r * x * r⁻¹ = x ^ 2) :
    (ρ r - 1) ^ 8 = 0 ∧
      IsIndecomposable (Polynomial (ZMod 2)) (Module.AEval' (ρ r)) := by
  have hfix := (fixed_dimensions ρ hf hd x r hx hr hrel).1
  have hnontriv : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank (ZMod 2) V)
  let : CharP (Module.End (ZMod 2) V) 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have hnil : (ρ r - 1) ^ 8 = 0 := by
    have hpow : r ^ (2 ^ 3) = 1 := by simpa [hr] using pow_orderOf_eq_one r
    change (ρ r - 1) ^ (2 ^ 3) = 0
    rw [sub_pow_char_pow_of_commute 2 3 (Commute.one_right (ρ r)), one_pow,
      ← map_pow, hpow, map_one, sub_self]
  refine ⟨hnil, ?_⟩
  have hne : fixedSpace ρ (Subgroup.zpowers r) ≠ ⊥ := by
    intro hzero
    rw [hzero, finrank_bot] at hfix
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  apply isIndecomposable_aeval_of_nilpotent_sub_one_ker_line (ρ r) ⟨8, hnil⟩ v hv0
    ((mem_fixedSpace_zpowers_iff ρ r v).mp hv)
  intro w hw
  have hwmem : w ∈ fixedSpace ρ (Subgroup.zpowers r) := (mem_fixedSpace_zpowers_iff ρ r w).mpr hw
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hfix hv hv0] at hwmem
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hwmem
  exact ⟨a, ha.symm⟩
end Representation.SeventeenFrobeniusModule
