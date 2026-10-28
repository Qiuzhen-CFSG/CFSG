module
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.Tactic.Module
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.KernelCard
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Perfectness and order of a binary point stabilizer

In dimension at least four, the stabilizer of a nonzero vector is perfect.
Its displacement kernel consists of transvections, each a commutator of
transvections fixing the point. Its quotient is the perfect general linear
group on the quotient space. The displacement description also identifies
its order as 2^(d-1) times the order of GL_(d-1)(2).

This extends the five-dimensional calculation in FiveFlagGeometry/Residuals/
Endpoints to the dimensions used by the original natural point action.
The source application uses the full parabolic, including its two-core,
when comparing it with the literal component quotient in 12.9.6.

Source: Aschbacher--Smith, 12.8.3(1) and 12.9.6, printed pp.850 and861--862.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace BinaryLinear.PointStabilizerPerfect
open OuterCyclic Theory.LinearAlgebra
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [FiniteDimensional (ZMod 2) E] in
private theorem transvection_cross (w y : E)
    (α β : E →ₗ[ZMod 2] ZMod 2)
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
theorem point_kernel_le_commutator (hd : 3 ≤ Module.finrank (ZMod 2) E) {v : E} (hv : v ≠ 0) :
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
    have hedim := β.finrank_range_add_finrank_ker
    have hb := Submodule.finrank_le β.range
    rw [← heq, finrank_span_singleton hv] at hedim
    have hb1 : Module.finrank (ZMod 2) (LinearMap.range β) ≤ 1 := by simpa using hb
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


/-- A nonzero point stabilizer in binary dimension at least four is perfect. -/
theorem isPerfect (hd : 4 ≤ Module.finrank (ZMod 2) E) {v : E} (hv : v ≠ 0) :
    Group.IsPerfect (BinaryFivePointStabilizer.stabilizer v) := by
  let Q := BinaryFivePointStabilizer.QuotientSpace v
  let d := Module.finrank (ZMod 2) Q
  have hdim : d + 1 = Module.finrank (ZMod 2) E := by
    have he := (BinaryFivePointStabilizer.line v).finrank_quotient_add_finrank
    rw [finrank_span_singleton hv] at he
    exact he
  let b := (Module.finBasis (ZMod 2) Q).equivFun
  let e := SmallParabolicLevi.linearGroupCongr b
  let : Group.IsPerfect (LinearGroup d) := linearGroup_isPerfect d (by omega)
  let : Group.IsPerfect (Q ≃ₗ[ZMod 2] Q) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (BinaryFivePointStabilizer.quotientAction v) (BinaryFivePointStabilizer.quotientAction_surjective v)
  rwa [sup_eq_right.mpr (point_kernel_le_commutator (by omega) hv)] at hh

/-- The order of the literal point stabilizer, including its displacement kernel. -/
theorem card (v : E) (hv : v ≠ 0) :
    Nat.card (BinaryFivePointStabilizer.stabilizer v) =
      2 ^ (Module.finrank (ZMod 2) E - 1) *
        Nat.card (LinearGroup (Module.finrank (ZMod 2) E - 1)) := by
  let := Module.finite_of_finite (ZMod 2) (M := E)
  have hdim : Module.finrank (ZMod 2) (BinaryFivePointStabilizer.QuotientSpace v) =
      Module.finrank (ZMod 2) E - 1 := by
    have he := (BinaryFivePointStabilizer.line v).finrank_quotient_add_finrank
    rw [finrank_span_singleton hv] at he
    exact Nat.eq_sub_of_add_eq he
  have hk : Nat.card (BinaryFivePointStabilizer.kernel v) =
      2 ^ (Module.finrank (ZMod 2) E - 1) := by
    rw [Nat.card_congr (BinaryFivePointStabilizer.kernelDisplacementEquiv v).toEquiv]
    change Nat.card (BinaryFivePointStabilizer.QuotientSpace v →ₗ[ZMod 2]
      BinaryFivePointStabilizer.line v) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap,
      hdim, finrank_span_singleton hv, Nat.card_zmod, mul_one]
  let b := (Module.finBasisOfFinrankEq (ZMod 2) _ hdim).equivFun
  let e := (BinaryFivePointStabilizer.quotientEquiv v).trans
    (SmallParabolicLevi.linearGroupCongr b)
  rw [← (BinaryFivePointStabilizer.kernel v).card_mul_index, hk]
  change _ * Nat.card (_ ⧸ _) = _
  rw [Nat.card_congr e.toEquiv]

omit [FiniteDimensional (ZMod 2) E] in
private theorem exists_generator (W : Submodule (ZMod 2) E)
    (hW : Module.finrank (ZMod 2) W = 1) :
    ∃ v : E, v ≠ 0 ∧ W = Submodule.span (ZMod 2) {v} := by
  have hn : W ≠ ⊥ := by intro he; rw [he] at hW; simp at hW
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  exact ⟨v,hv0,eq_span_singleton_of_mem_of_finrank_eq_one hW hv hv0⟩

omit [FiniteDimensional (ZMod 2) E] in
private theorem line_parabolic {v : E} (hv : v ≠ 0) :
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

/-- The actual stabilizer of a one-space is perfect in binary dimension at least four. -/
theorem parabolic_isPerfect (hd : 4 ≤ Module.finrank (ZMod 2) E)
    (W : Submodule (ZMod 2) E) (hW : Module.finrank (ZMod 2) W = 1) :
    Group.IsPerfect (parabolic W) := by
  obtain ⟨v,hv,rfl⟩ := exists_generator W hW
  rw [line_parabolic hv]
  exact isPerfect hd hv

/-- Order of the original one-space parabolic. -/
theorem parabolic_card (W : Submodule (ZMod 2) E)
    (hW : Module.finrank (ZMod 2) W = 1) :
    Nat.card (parabolic W) = 2 ^ (Module.finrank (ZMod 2) E - 1) *
      Nat.card (LinearGroup (Module.finrank (ZMod 2) E - 1)) := by
  obtain ⟨v,hv,rfl⟩ := exists_generator W hW
  rw [line_parabolic hv]
  exact card v hv

end BinaryLinear.PointStabilizerPerfect
