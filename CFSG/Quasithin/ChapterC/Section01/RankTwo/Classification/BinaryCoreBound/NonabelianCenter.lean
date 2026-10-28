module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.NonabelianCenter.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.NonabelianCenter.SmallCore

/-!
# Nonabelian binary MS cores: reductions and conditional center assembly

The small-core obstruction excludes all nonabelian cores of order at most
32, including the order-16 central extension in source C.1.34(5).

The remaining center model is assembled below from two explicit inputs:
every element of Z(D) squares to one, and its intrinsic omega subgroup has
order 8 or 32. Choosing a basis of the resulting binary vector space gives
the actual group isomorphism. Neither input is proved by this module;
MS3-driven exponent control and omega-center rigidity remain necessary
before the unconditional `Input.nonabelianCoreCenter_model` can be exported.
The final conditional theorem instead takes order eight for the commutator
of the ambient omega-center with L, and relative index one or four for
that commutator. Its cardinal calculation uses the actual subtype comparison.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.34(3),(4),
printed pp.136–137. In particular the elementary module Ω₁Z(O₂(J)) cannot
be substituted for the intrinsic center Z([O₂(J), L]).
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J] [Finite J]

/-- Conditional model construction from separate exponent and intrinsic
omega-center order inputs. This is not the MS local rigidity theorem. -/
theorem coreCenter_model_of_squares_and_omega_card (L : Subgroup J)
    (hsquare : ∀ z : center (commutatorCore L), z ^ 2 = 1)
    (hcard : Nat.card (coreCenterOmega L) = 8 ∨
      Nat.card (coreCenterOmega L) = 32) :
    ∃ d : ℕ, (d = 3 ∨ d = 5) ∧
      Nonempty (center (commutatorCore L) ≃* Multiplicative (Fin d → ZMod 2)) := by
  classical
  let Z := center (commutatorCore L)
  let : IsElementaryAbelian 2 Z :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare⟩
  have ht : coreCenterOmega L = ⊤ := coreCenterOmega_eq_top_of_squares L hsquare
  have he : Nat.card (coreCenterOmega L) = Nat.card Z :=
    Nat.card_congr ((MulEquiv.subgroupCongr ht).trans topEquiv).toEquiv
  have hc : Nat.card Z = 8 ∨ Nat.card Z = 32 := by rwa [he] at hcard
  have hd : ∃ d : ℕ, (d = 3 ∨ d = 5) ∧ Nat.card Z = 2 ^ d := by
    rcases hc with hc | hc
    · exact ⟨3, Or.inl rfl, hc⟩
    · exact ⟨5, Or.inr rfl, hc⟩
  obtain ⟨d, hd, hsize⟩ := hd
  refine ⟨d, hd, ?_⟩
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive Z) = 2 ^ d := by
    have hz := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Z)
    change Nat.card Z = _ at hz
    simpa only [Nat.card_zmod, hsize] using hz.symm
  have hdim : Module.finrank (ZMod 2) (Additive Z) = d :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive Z) hdim
  exact ⟨b.equivFun.toAddEquiv.toMultiplicativeRight⟩

open Stellmacher
variable {κ : GroupClass.{u}} {L R : Subgroup J}

/-- Conditional assembly from exponent control and the moving omega-center
layer. The two MS rigidity results supplying these premises remain separate
proof obligations; no identification with the ambient two-core center is used. -/
theorem Input.coreCenter_model_of_squares_and_omega_commutator (h : Input κ L R)
    (hsquare : ∀ z : center (commutatorCore L), z ^ 2 = 1)
    (hmoving : Nat.card (⁅omegaOneCenterAmbient (commutatorCore L), L⁆ : Subgroup J) = 8)
    (hindex : ⁅omegaOneCenterAmbient (commutatorCore L), L⁆.relIndex
        (omegaOneCenterAmbient (commutatorCore L)) = 1 ∨
      ⁅omegaOneCenterAmbient (commutatorCore L), L⁆.relIndex
        (omegaOneCenterAmbient (commutatorCore L)) = 4) :
    ∃ d : ℕ, (d = 3 ∨ d = 5) ∧
      Nonempty (center (commutatorCore L) ≃* Multiplicative (Fin d → ZMod 2)) := by
  let W := omegaOneCenterAmbient (commutatorCore L)
  change Nat.card (⁅W, L⁆ : Subgroup J) = 8 at hmoving
  let : W.Normal := h.coreCenterOmega_ambient_normal
  have hle : ⁅W, L⁆ ≤ W := commutator_le_left _ _
  have hc := relIndex_mul_relIndex (⊥ : Subgroup J) ⁅W, L⁆ W bot_le hle
  simp only [relIndex_bot_left, hmoving] at hc
  have hw : Nat.card W = 8 ∨ Nat.card W = 32 := by
    rcases hindex with hi | hi
    · exact Or.inl (by rw [hi, mul_one] at hc; exact hc.symm)
    · exact Or.inr (by rw [hi] at hc; exact hc.symm)
  apply coreCenter_model_of_squares_and_omega_card L hsquare
  have he := Nat.card_congr (coreCenterOmegaEquivAmbient L).toEquiv
  exact hw.imp (fun hh => he.trans hh) (fun hh => he.trans hh)

end CFSG.Quasithin.ChapterC.BinaryMS
