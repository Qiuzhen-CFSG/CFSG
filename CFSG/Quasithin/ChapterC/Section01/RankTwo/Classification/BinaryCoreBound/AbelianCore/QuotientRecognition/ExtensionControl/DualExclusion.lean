module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Dimension
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.FaithfulRankOne
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.PSL3Two.SmallModuleProperties
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Opposite natural orientations cannot form a binary FF-extension

The displacement of a faithful actor embeds it, as a set, into the linear maps
from the fixed-space quotient to the commutator space. Counting these maps and
using duality gives `rank A ≤ fixedCodim W A * fixedCodim W.dual A`. If an
elementary subgroup of SL₃(2) could offend on an extension of these two factors,
the additive codimension inequality and rank at most two would force both
codimensions to be one and the actor rank to be two. The product bound then
gives rank at most one, a contradiction. Splitting is not assumed.

This establishes the binary orientation exclusion in Aschbacher–Smith
B.4.9(2)(ii), printed pp.92,94, with the quotient/submodule inequality used
in B.5.1, pp.100–101, combined manuscript of 1 March 2004.
-/

public section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl

private theorem rank_le_fixedCodim_mul_dual
    {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) G W)
    (hσ : Function.Injective σ) (A : Subgroup G) :
    rank A ≤ fixedCodim σ A * fixedCodim σ.dual A := by
  let τ := σ.comp A.subtype
  let U := fixedSpace σ A
  let C := Coinvariants.ker τ
  let d (a : A) : W →ₗ[ZMod 2] C :=
    (σ a - LinearMap.id).codRestrict C (fun v => Coinvariants.sub_mem_ker (ρ := τ) a v)
  let D (a : A) : (W ⧸ U) →ₗ[ZMod 2] C := U.liftQ (d a) (by
    intro v hv
    apply Subtype.ext
    exact sub_eq_zero.mpr (hv a))
  have hinj : Function.Injective D := by
    intro a b h
    apply Subtype.ext
    apply hσ
    apply LinearMap.ext
    intro v
    have he := congrArg (fun f : (W ⧸ U) →ₗ[ZMod 2] C => (f (U.mkQ v) : W)) h
    change σ a v - v = σ b v - v at he
    exact sub_left_injective he
  let : Finite ((W ⧸ U) →ₗ[ZMod 2] C) := Module.finite_of_finite (ZMod 2)
  have hc := Nat.card_le_card_of_injective D hinj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (W ⧸ U) →ₗ[ZMod 2] C), Nat.card_zmod,
    Module.finrank_linearMap] at hc
  have hd : fixedCodim σ.dual A = Module.finrank (ZMod 2) C :=
    finrank_dual_quotient_invariants τ
  have hl := Nat.log_monotone (b := 2) hc
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  rw [hd]
  exact hl


/-- The natural module and its dual cannot share the budget of an offender. -/
theorem rank_lt_natural_add_dual_fixedCodim (A : Subgroup SL) (hA : IsElementaryTwo A) :
    rank A < fixedCodim BinaryLinearThree.W A + fixedCodim BinaryLinearThree.W.dual A := by
  have hr := elementary_rank_le_two A hA.2
  have hn := fixedCodim_pos_of_faithful BinaryLinearThree.W BinaryLinearThree.natural_injective hA.1
  have hd := fixedCodim_pos_of_faithful BinaryLinearThree.W.dual BinaryLinearThree.dual_injective hA.1
  have hp := rank_le_fixedCodim_mul_dual BinaryLinearThree.W BinaryLinearThree.natural_injective A
  by_contra! h
  have he1 : fixedCodim BinaryLinearThree.W A = 1 := by omega
  have he2 : fixedCodim BinaryLinearThree.W.dual A = 1 := by omega
  rw [he1, he2] at hp
  omega

private theorem fixedCodim_equiv {G W X : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) G W} {τ : Representation (ZMod 2) G X}
    (e : σ.Equiv τ) (A : Subgroup G) : fixedCodim σ A = fixedCodim τ A := by
  simpa only [Subgroup.map_id] using fixedCodim_map_equivariant σ τ (MonoidHom.id G)
    e.toLinearEquiv (fun g v => LinearMap.congr_fun (e.isIntertwining' g) v) A

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) SL V)

/-- An extension with one natural factor and one dual factor is never FF,
whether or not the extension splits. -/
theorem not_ff_of_opposite_natural_layers (N : Subrepresentation ρ)
    (h : (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W) ∧
          Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W.dual)) ∨
         (Nonempty (N.toRepresentation.Equiv BinaryLinearThree.W.dual) ∧
          Nonempty (N.quotientRepresentation.Equiv BinaryLinearThree.W))) :
    ¬ IsFFModule ρ := by
  rintro ⟨A,hA⟩
  have hcost := fixedCodim_quotient_add_subrepresentation_le ρ N A
  have hlt := rank_lt_natural_add_dual_fixedCodim A hA.1
  rcases h with ⟨hN,hQ⟩ | ⟨hN,hQ⟩
  · obtain ⟨eN⟩ := hN
    obtain ⟨eQ⟩ := hQ
    rw [fixedCodim_equiv eN, fixedCodim_equiv eQ] at hcost
    have := hA.2
    omega
  · obtain ⟨eN⟩ := hN
    obtain ⟨eQ⟩ := hQ
    rw [fixedCodim_equiv eN, fixedCodim_equiv eQ] at hcost
    have := hA.2
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.AbelianCore.QuotientRecognition.ExtensionControl
