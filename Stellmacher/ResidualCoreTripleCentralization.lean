module
public import Stellmacher.ResidualCoreCommutator
public import Theory.ThreeSubgroups

/-!
# Residual-core centralization from two triple commutators

For a finite subgroup R equal to its two-residual and with odd core
quotient, its two-core equals its commutator with R. Thus an ambient
subgroup D centralizes that core if both [[D,R],O₂(R)] and
[[D,O₂(R)],R] are trivial. No normality of D is required.

Map the native core commutator identity into the ambient group. The
three-subgroups lemma kills [[O₂(R),R],D], and substitution gives the
claimed centralization. This is the final algebraic deduction in source
(7) of Stellmacher (8.4), printed p.39; its consumer supplies the two
triple commutators from the geometric subgroup configuration.
-/

namespace Stellmacher
open BenderSuzuki.External
public theorem residual_core_centralizes_of_triple_commutators
    {G : Type*} [Group G] [Finite G] (D R : Subgroup G)
    (hres : hktPResidual 2 R = ⊤)
    (hodd : Odd (Nat.card (R ⧸ pCore 2 R)))
    (hDRQ : ⁅⁅D, R⁆, (pCore 2 R).map R.subtype⁆ = ⊥)
    (hDQR : ⁅⁅D, (pCore 2 R).map R.subtype⁆, R⁆ = ⊥) :
    ⁅D, (pCore 2 R).map R.subtype⁆ = ⊥ := by
  let Q := (pCore 2 R).map R.subtype
  have hQR : Q = ⁅Q,R⁆ := by
    have hh := congrArg (Subgroup.map R.subtype)
      (twoCore_eq_commutator_of_residual_perfect hres hodd)
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
    exact hh
  have hrot : ⁅⁅Q,R⁆,D⁆ ≤ (⊥ : Subgroup G) := by
    apply Subgroup.commutator_commutator_le_of_rotate
    · simpa only [Subgroup.commutator_comm] using hDRQ.le
    · exact hDQR.le
  rw [Subgroup.commutator_comm]
  exact le_bot_iff.mp ((congrArg (fun T : Subgroup G => ⁅T,D⁆) hQR).le.trans hrot)
end Stellmacher
