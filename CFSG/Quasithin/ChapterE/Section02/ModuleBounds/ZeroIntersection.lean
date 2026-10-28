module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ClassicalCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearCubic
import all CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Strict

/-!
# The zero-intersection FF conclusion of E.2.13

If Z=V∩Vᵍ is trivial, the elementary factors A and B commute, so their
join P is elementary. Consequently B is fixed by A, and the original
star-quotient bound alone bounds the fixed codimension. Comparing it
with the actual actor rank produces an offender and quadratic ratio
at most one. The final four theorems discharge both bounds in the
original dihedral, SL₂, Suzuki, and symplectic families.

The internal import reuses the fixed-subgroup cardinal argument in the
strict-dihedral proof. No private declaration occurs in a public type.
Source: Aschbacher–Smith E.2.13(5) and the preliminary reduction in
E.2.15, printed pp.224–228.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem actor_rank_pos (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) :
    0 < Nat.log 2 ((Z V g).relIndex (A V M g)) := by
  let := h.Z_normal
  let f := QuotientGroup.mk' ((Z V g).subgroupOf (A V M g))
  have he := h.actor_elementary hproper hfit f (QuotientGroup.ker_mk' _)
  have hr := he.rank_pos
  change 0 < Nat.log 2 (Nat.card f.range) at hr
  rw [← index_ker, QuotientGroup.ker_mk'] at hr
  exact hr

theorem P_elementary_of_Z_eq_bot (h : Hypotheses T V M g) (hz : Z V g = ⊥) :
    IsElementaryAbelian 2 (P V M g) := by
  let := h.A_elementary
  let := h.B_elementary
  apply IsElementaryAbelian.sup_of_le_centralizer
  exact commutator_eq_bot_iff_le_centralizer.mp (bot_unique
    (h.commutator_A_B_le_Z.trans_eq hz))

variable {D Q : Type*} [Group D] [Finite D] [Group Q] [Finite Q]
  [IsElementaryAbelian 2 Q]

omit [Finite X] [Finite D] in
theorem actor_fixed_bound_of_P_elementary (h : Hypotheses T V M g)
    (hP : IsElementaryAbelian 2 (P V M g))
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2^d) :
    fixedCodim ρ f.range ≤ d := by
  let := hP
  apply actor_fixed_bound_of_fixed_subgroup e ρ f ha (B V M) inf_le_right
  · intro b hb a ha
    exact (P V M g).le_centralizer (show b ∈ P V M g from
      (show B V M ≤ P V M g from le_sup_left) hb) a
      ((show A V M g ≤ P V M g from le_sup_right) ha)
  · rw [h.card_V_eq_card_A_mul_star, A,
      card_map_of_injective (MulAut.conj g).injective, mul_comm (2^d)]
    exact Nat.mul_le_mul_left _ hstar

theorem offender_of_P_elementary_and_star_dimension
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hP : IsElementaryAbelian 2 (P V M g))
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2^d)
    (hd : d ≤ Nat.log 2 ((Z V g).relIndex (A V M g))) :
    IsOffender ρ f.range ∧ quadraticRatio ρ ≤ 1 := by
  have hk := h.actor_kernel e ρ hρ f ha
  have he := h.actor_elementary hproper hfit f hk
  have hr : rank f.range = Nat.log 2 ((Z V g).relIndex (A V M g)) := by
    change Nat.log 2 (Nat.card f.range) = _
    rw [← index_ker, hk]
    rfl
  have hb := h.actor_fixed_bound_of_P_elementary hP e ρ f ha d hstar
  have hoff : IsOffender ρ f.range := ⟨he, by rw [hr]; exact hb.trans hd⟩
  exact ⟨hoff,(isFFModule_iff_quadraticRatio_le_one ρ).mp ⟨f.range,hoff⟩⟩
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {X : Type*} [Group X] [Finite X]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

private theorem canonical_quadraticRatio_le_one_of_P_elementary
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hP : IsElementaryAbelian 2 (P V M g))
    (d : ℕ) (hstar : Nat.card (V.map (QuotientGroup.mk' (J M))) ≤ 2^d)
    (hd : d ≤ Nat.log 2 ((Z V g).relIndex (A V M g))) :
    letI := h.elementary
    quadraticRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 1 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  have hr := h.offender_of_P_elementary_and_star_dimension hproper hfit hP
    (MulEquiv.refl V) (canonicalAction (normalizer (V : Set X)) V le_rfl)
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
    (fun a v => representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) _ _) d hstar hd
  exact hr.2

theorem canonical_quadraticRatio_le_one_dihedral_of_Z_eq_bot
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) (hz : Z V g = ⊥)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.elementary
    quadraticRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 1 := by
  apply canonical_quadraticRatio_le_one_of_P_elementary h hproper hfit
    (h.P_elementary_of_Z_eq_bot hz) 1 (by rw [hcard]; norm_num)
  exact h.actor_rank_pos hproper hfit

theorem canonical_quadraticRatio_le_one_linear_two_of_Z_eq_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) (hz : Z V g = ⊥)
    (m : ℕ) (hm : 2 ≤ m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* SL(2,F)) :
    letI := h.elementary
    quadraticRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 1 :=
  canonical_quadraticRatio_le_one_of_P_elementary h hproper hfit
    (h.P_elementary_of_Z_eq_bot hz) m (h.star_card_le_linear_two m hcard ξ)
    (h.actor_rank_ge_linear_two_star hproper hfit m hm hcard ξ)

theorem canonical_quadraticRatio_le_one_suzuki_of_Z_eq_bot
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) (hz : Z V g = ⊥)
    (m : ℕ) (hm : 1 ≤ m)
    (ξ : (X ⧸ J M) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :
    letI := h.elementary
    quadraticRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 1 := by
  apply canonical_quadraticRatio_le_one_of_P_elementary h hproper hfit
    (h.P_elementary_of_Z_eq_bot hz) (2*m+1) (h.star_card_le_suzuki m (by omega) ξ)
  have hd := h.actor_rank_ge_suzuki hfit m hm ξ
  omega

theorem canonical_quadraticRatio_le_one_symplectic_four_of_Z_eq_bot
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X) (hz : Z V g = ⊥)
    (m : ℕ) (hm : 0 < m) (hcard : Nat.card F = 2^m)
    (ξ : (X ⧸ J M) ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hVS : V.map (ξ.toMonoidHom.comp (QuotientGroup.mk' (J M))) ≤
      (center S).map (S : Subgroup _).subtype) :
    letI := h.elementary
    quadraticRatio (canonicalAction (normalizer (V : Set X)) V le_rfl) ≤ 1 :=
  canonical_quadraticRatio_le_one_of_P_elementary h hproper hfit
    (h.P_elementary_of_Z_eq_bot hz) (2*m)
    (Hypotheses.star_card_le_symplectic_center m hm hcard ξ S hVS)
    (h.actor_rank_ge_symplectic_four hfit m hm hcard ξ)
end CFSG.Quasithin.ChapterE.DihedralCubic
