module

public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Pure.Basic
public import Theory.SpecificGroups.BinaryLinear.SylowTransvections
public import Theory.GroupTheory.Commutator.PerfectQuotient
public import Mathlib.Tactic.Module

/-!
# The two-residual of a pure-vector stabilizer

Every element of the point radical is a commutator of transvections fixing
the marked vector. The quotient is the perfect group GL_(n−1)(2), so the
whole point stabilizer is perfect for n ≥ 4. Transport through the actual
inner embedding proves the source equality with its embedded two-residual.

The transvection proof extends the dimension-five argument in
`BinaryLinear.FiveFlagGeometry.Residuals.Endpoints` to every dimension at
least three. Source: Aschbacher–Smith, H.9.1(3), printed pp.389–390.
-/

@[expose] public section

namespace BinaryNaturalDual.VectorStabilizers.Pure
open BinaryLinear
open BinaryLinear.OuterCyclic
open Theory.LinearAlgebra
open Subgroup
open scoped commutatorElement
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem transvection_cross (w y : V)
    (α β : V →ₗ[ZMod 2] ZMod 2)
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
theorem point_kernel_le_commutator [FiniteDimensional (ZMod 2) V]
    (hV : 3 ≤ Module.finrank (ZMod 2) V) {v : V} (hv : v ≠ 0) :
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
    have hb1 : Module.finrank (ZMod 2) β.range ≤ 1 := by simpa using hb
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

/-- Coordinates on the quotient by the marked nonzero vector. -/
noncomputable def quotientCoordinates {n : ℕ} {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    pointQuotient x ≃ₗ[ZMod 2] OuterCyclic.Space (n - 1) :=
  LinearEquiv.ofFinrankEq _ _ (by
    have hd := (BinaryFivePointStabilizer.line x).finrank_quotient_add_finrank
    rw [finrank_span_singleton hx] at hd
    simp only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] at hd
    change Module.finrank (ZMod 2) (pointQuotient x) + 1 = n at hd
    simp only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin]
    omega)

/-- The genuine full linear group on the marked quotient, in coordinates. -/
noncomputable def quotientGroupCoordinates {n : ℕ} {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    BinaryLinear.GL (pointQuotient x) ≃* LinearGroup (n - 1) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (pointQuotient x)).symm.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (quotientCoordinates hx)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (OuterCyclic.Space (n - 1))))

/-- The elementary radical is included in the derived subgroup; the quotient is perfect. -/
theorem point_isPerfect {n : ℕ} (hn : 4 ≤ n) {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Group.IsPerfect (pointStabilizer x) := by
  let e := quotientGroupCoordinates hx
  let : Group.IsPerfect (LinearGroup (n - 1)) := linearGroup_isPerfect (n - 1) (by omega)
  let : Group.IsPerfect (BinaryLinear.GL (pointQuotient x)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  constructor
  have hh := CentralExtension.ker_sup_commutator_eq_top_of_surjective
    (pointQuotientAction x) (BinaryFivePointStabilizer.quotientAction_surjective x)
  rwa [sup_eq_right.mpr (point_kernel_le_commutator (by
    simpa only [OuterCyclic.Space, Module.finrank_pi, Fintype.card_fin] using (show 3 ≤ n by omega)) hx)] at hh

/-- Perfectness of the actual inner pure-vector stabilizer. -/
theorem inner_isPerfect {n : ℕ} (hn : 4 ≤ n) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    Group.IsPerfect (innerStabilizer d (x,0)) := by
  let := point_isPerfect hn hx
  exact Group.IsPerfect.ofSurjective (f := (innerEquivPoint d x).symm.toMonoidHom)
    (innerEquivPoint d x).symm.surjective

/-- The intrinsic two-residual is the whole pure-vector stabilizer. -/
theorem inner_twoResidual {n : ℕ} (hn : 4 ≤ n) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    pResidual 2 (innerStabilizer d (x,0)) = ⊤ := by
  let : Finite (LinearGroup n) := Finite.of_injective
    (fun g : LinearGroup n => (g : OuterCyclic.Space n → OuterCyclic.Space n)) DFunLike.coe_injective
  let : Finite (innerStabilizer d (x,0)) :=
    Finite.of_injective (innerEquivPoint d x) (innerEquivPoint d x).injective
  let := inner_isPerfect hn d hx
  apply (pResidual_eq_top_iff 2 _).mpr
  intro N hN hp
  let := hN
  have hs : Subsingleton (innerStabilizer d (x,0) ⧸ N) := by
    by_contra! hh
    exact Group.IsPerfect.not_isNilpotent _ hp.isNilpotent
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

/-- The embedded two-residual agrees with the actual inner stabilizer. -/
theorem innerResidual_eq {n : ℕ} (hn : 4 ≤ n) (d : CoordinateAction n)
    {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    innerResidual d (x,0) = innerStabilizer d (x,0) := by
  rw [innerResidual, inner_twoResidual hn d hx, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

/-- The source equality C_M(x) = O²(C_L(x)). -/
theorem fullStabilizer_eq_innerResidual {n : ℕ} (hn : n = 4 ∨ n = 5)
    (d : CoordinateAction n) {x : OuterCyclic.Space n} (hx : x ≠ 0) :
    fullStabilizer d (x,0) = innerResidual d (x,0) := by
  rw [innerResidual_eq (by omega) d hx, pure_fullStabilizer_eq_innerStabilizer hn d hx]

end BinaryNaturalDual.VectorStabilizers.Pure
