module

public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Perfectness of the actual point parabolic in GL₄(2)

A point-stabilizer kernel element is a commutator of two transvections fixing
that point. The quotient action is onto GL₃(2), which is perfect. Consequently
the full point parabolic, including its radical, is perfect. This removes the
possible binary lifting obstruction when excluding A₁ from I.

The proof specializes the dimension-independent point-stabilizer construction
and adapts the existing five-space proof in
`Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals.Endpoints`.
Source: Aschbacher–Smith 13.8.25, printed p.961 (PDF p.978).
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Point
open BinaryLinear BinaryLinear.OuterCyclic
open Theory.LinearAlgebra

private theorem transvection_cross (w y : Space 4)
    (α β : Space 4 →ₗ[ZMod 2] ZMod 2)
    (hαw : α w = 0) (hβw : β w = 0) (hβy : β y = 0) (hαy : α y = 1) :
    ⁅transvection w α hαw, transvection y β hβy⁆ = transvection w β hβw := by
  apply LinearEquiv.ext
  intro v
  change (v + β v • y + α (v + β v • y) • w +
    β (v + β v • y + α (v + β v • y) • w) • y +
    α (v + β v • y + α (v + β v • y) • w +
      β (v + β v • y + α (v + β v • y) • w) • y) • w) = v + β v • w
  simp only [map_add, map_smul, hαw, hβw, hβy, hαy, smul_eq_mul, mul_zero,
    mul_one, add_zero]
  match_scalars <;> ring_nf <;>
    simp only [show (2 : ZMod 2) = 0 by decide, show (3 : ZMod 2) = 1 by decide,
      mul_zero, mul_one, zero_add]

/-- Every displacement-kernel element is a commutator inside the point stabilizer. -/
private theorem point_kernel_le_commutator {v : Space 4} (hv : v ≠ 0) :
    BinaryFivePointStabilizer.kernel v ≤ commutator (BinaryFivePointStabilizer.stabilizer v) := by
  intro g hg
  by_cases hg1 : g = 1
  · exact hg1 ▸ one_mem _
  have hr : g.val ∈ radical (BinaryFivePointStabilizer.line v) :=
    ⟨BinaryFivePointStabilizer.fixes_line v g, (BinaryFivePointStabilizer.mem_kernel_iff v g).mp hg⟩
  obtain ⟨β, _, hβv, he⟩ := exists_transvection_of_mem_line_radical hv hr
    (fun h => hg1 (Subtype.ext h))
  have hline : BinaryFivePointStabilizer.line v ≤ β.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    exact hβv
  have hlt : BinaryFivePointStabilizer.line v < β.ker := by
    apply lt_of_le_of_ne hline
    intro heq
    have hd := β.finrank_range_add_finrank_ker
    have hb := Submodule.finrank_le β.range
    rw [← heq, finrank_span_singleton hv] at hd
    norm_num [Space] at hd hb
    omega
  obtain ⟨y, hβy, hyv⟩ := SetLike.exists_of_lt hlt
  obtain ⟨α, hαy, hαv⟩ := (BinaryFivePointStabilizer.line v).exists_le_ker_of_notMem hyv
  have hαv0 : α v = 0 := hαv (Submodule.mem_span_singleton_self v)
  have hαy1 : α y = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hαy
  let a : BinaryFivePointStabilizer.stabilizer v := ⟨transvection v α hαv0, by
    change v + α v • v = v
    simp [hαv0]⟩
  let c : BinaryFivePointStabilizer.stabilizer v := ⟨transvection y β hβy, by
    change v + β v • y = v
    simp [hβv]⟩
  have hcomm : ⁅a, c⁆ = g := by
    apply Subtype.ext
    change ⁅transvection v α hαv0, transvection y β hβy⁆ = g.val
    rw [transvection_cross v y α β hαv0 hβv hβy hαy1]
    apply LinearEquiv.ext
    intro x
    exact (he x).symm
  rw [← hcomm]
  exact commutator_mem_commutator (mem_top _) (mem_top _)

/-- The point stabilizer is perfect, including its elementary abelian kernel. -/
private theorem pointStabilizer_isPerfect {v : Space 4} (hv : v ≠ 0) :
    Group.IsPerfect (BinaryFivePointStabilizer.stabilizer v) := by
  let b : BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    LinearEquiv.ofFinrankEq _ _ (by
      have hd := Submodule.finrank_quotient_add_finrank (BinaryFivePointStabilizer.line v)
      have hl : Module.finrank (ZMod 2) (BinaryFivePointStabilizer.line v) = 1 :=
        finrank_span_singleton hv
      have he : Module.finrank (ZMod 2) (Space 4) = 4 := by simp [Space]
      change Module.finrank (ZMod 2) (BinaryFivePointStabilizer.QuotientSpace v) +
        Module.finrank (ZMod 2) (BinaryFivePointStabilizer.line v) =
        Module.finrank (ZMod 2) (Space 4) at hd
      rw [hl, he] at hd
      simp only [Module.finrank_pi, Fintype.card_fin]
      omega)
  let e : (BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2] BinaryFivePointStabilizer.QuotientSpace v) ≃* LinearGroup 3 :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (BinaryFivePointStabilizer.QuotientSpace v)).symm.trans
      ((LinearMap.GeneralLinearGroup.congrLinearEquiv b).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Space 3)))
  let : Group.IsPerfect (LinearGroup 3) := linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect (BinaryFivePointStabilizer.QuotientSpace v ≃ₗ[ZMod 2] BinaryFivePointStabilizer.QuotientSpace v) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (BinaryFivePointStabilizer.quotientAction v) (BinaryFivePointStabilizer.quotientAction_surjective v)
  rwa [sup_eq_right.mpr (point_kernel_le_commutator hv)] at hh

/-- Over the binary field, stabilizing a nonzero vector's line fixes that vector. -/
private theorem pointParabolic_eq_stabilizer {v : Space 4} (hv : v ≠ 0) :
    parabolic (Submodule.span (ZMod 2) {v}) = BinaryFivePointStabilizer.stabilizer v := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
      ((hg v).mpr (Submodule.mem_span_singleton_self v))
    have ha0 : a ≠ 0 := by
      intro hz
      exact hv (g.map_eq_zero_iff.mp (by simpa [hz] using ha.symm))
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    simpa [ha1, BinaryFivePointStabilizer.mem_stabilizer] using ha.symm
  · intro hg x
    have hfix : g v = v := hg
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
      exact Submodule.mem_span_singleton.mpr ⟨a, g.injective (by simpa [hfix] using ha)⟩
    · intro hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simpa [map_smul, hfix] using Submodule.smul_mem
        (Submodule.span (ZMod 2) {v}) a (Submodule.mem_span_singleton_self v)

/-- The actual geometric point parabolic is perfect. -/
private theorem pointParabolic_isPerfect {v : Space 4} (hv : v ≠ 0) :
    Group.IsPerfect (parabolic (Submodule.span (ZMod 2) {v})) := by
  rw [pointParabolic_eq_stabilizer hv]
  exact pointStabilizer_isPerfect hv


/-- The binary four-space point parabolic equals its derived subgroup. -/
theorem parabolic_isPerfect (L : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hL : Module.finrank (ZMod 2) L = 1) : Group.IsPerfect (parabolic L) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (by
    intro hz
    rw [hz, finrank_bot] at hL
    omega : L ≠ ⊥)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hL hv hv0]
  exact pointParabolic_isPerfect hv0

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.Point
