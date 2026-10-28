module

public import Theory.SpecificGroups.ProjectiveDimensionThree.NondefiningThreeRank.Lifts
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Noncommuting lifts in projective dimension three

An abelian projective image makes each matrix commutator scalar. Taking
determinants shows that its scalar is a cube root of unity. Choose a
noncommuting pair, so this root has order three. Over an algebraic closure,
an eigenspace of any common centralizer element is invariant under the pair.
The determinant of the restricted commutation relation forces its dimension
to be divisible by three. Thus the eigenspace is the whole natural module,
and the common centralizer consists of scalars.

The two scalar commutation factors with this pair distinguish projective
classes, embedding the projective image into two groups of cube roots of
unity. Faithful extension of both matrices and the literal projective
quotient descends the bound to the original field. The full-preimage
consumer uses the actual map-comap equality for GL₃ modulo its scalar center.
This includes the extraspecial three-group lifts and discharges the
noncommuting premise in the dimension-three nondefining rank assembly.
The finite-field API retains the nondefining characteristic hypothesis;
the noncommuting argument itself works in every characteristic.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.2.17 and Remark A.2.14, printed pp.37–39.
-/

public section

open Matrix
open scoped MatrixGroups IsMulCommutative
namespace Matrix.ProjectiveDimensionThree
variable {F : Type*} [Field F]

/-- An invariant eigenspace has dimension divisible by the scalar commutator order. -/
private theorem scalar_of_twisted_pair [IsAlgClosed F]
    (X Y Z : Module.End F (Fin 3 → F))
    (hX : Function.Injective X) (hY : Function.Injective Y)
    (zeta : F) (hzeta : orderOf zeta = 3)
    (hXY : X * Y = zeta • (Y * X))
    (hZX : Commute Z X) (hZY : Commute Z Y) :
    ∃ c : F, Z = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := Z.exists_eigenvalue
  let W := Z.eigenspace c
  have stable (T : Module.End F (Fin 3 → F)) (hZT : Commute Z T) :
      ∀ v ∈ W, T v ∈ W := by
    intro v hv
    apply Module.End.mem_eigenspace_iff.mpr
    have hv := Module.End.mem_eigenspace_iff.mp hv
    calc
      Z (T v) = T (Z v) := LinearMap.congr_fun hZT.eq v
      _ = c • T v := by rw [hv, map_smul]
  let X' : Module.End F W := X.restrict (stable X hZX)
  let Y' : Module.End F W := Y.restrict (stable Y hZY)
  have hX' : Function.Injective X' := by
    intro v w hvw
    apply Subtype.ext
    exact hX (congrArg Subtype.val hvw)
  have hY' : Function.Injective Y' := by
    intro v w hvw
    apply Subtype.ext
    exact hY (congrArg Subtype.val hvw)
  have hXd : LinearMap.det X' ≠ 0 := by
    intro hd
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd (LinearMap.ker_eq_bot.mpr hX')
  have hYd : LinearMap.det Y' ≠ 0 := by
    intro hd
    exact LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd (LinearMap.ker_eq_bot.mpr hY')
  have hXY' : X' * Y' = zeta • (Y' * X') := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun hXY v
  have hd := congrArg LinearMap.det hXY'
  simp only [map_mul, LinearMap.det_smul] at hd
  have hp : zeta ^ Module.finrank F W = 1 := by
    apply (mul_right_cancel₀ (mul_ne_zero hYd hXd))
    simpa only [one_mul, mul_comm (LinearMap.det X') (LinearMap.det Y')] using hd.symm
  have hdiv : 3 ∣ Module.finrank F W := by
    simpa only [hzeta] using orderOf_dvd_of_pow_eq_one hp
  have hle : Module.finrank F W ≤ 3 := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using W.finrank_le
  have hpos : 0 < Module.finrank F W := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hc (Submodule.finrank_eq_zero.mp hzero)
  have htop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by
    simp only [Module.finrank_pi, Fintype.card_fin]
    omega)
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro v
  exact Module.End.mem_eigenspace_iff.mp (show v ∈ W from htop ▸ Submodule.mem_top)

private lemma natural_scalar (u : Fˣ) :
    Representation.generalLinearNatural 3 (GeneralLinearGroup.scalar (Fin 3) u) =
      (u : F) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  change Matrix.mulVecLin (Matrix.scalar (Fin 3) (u : F)) v = _
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal, Pi.algebraMap_apply]

private lemma natural_injective (g : GL (Fin 3) F) :
    Function.Injective (Representation.generalLinearNatural 3 g) := by
  intro v w h
  have hh := congrArg (Representation.generalLinearNatural 3 g⁻¹) h
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply] using hh

/-- Determinants constrain every scalar commutation factor in GL₃. -/
private lemma scalar_factor_cube (x y : GL (Fin 3) F) (u : Fˣ)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 3) u * (y * x)) : u ^ 3 = 1 := by
  have hd := congrArg GeneralLinearGroup.det hxy
  simp only [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin] at hd
  apply mul_right_cancel (b := GeneralLinearGroup.det y * GeneralLinearGroup.det x)
  simpa only [one_mul, mul_comm (GeneralLinearGroup.det x) (GeneralLinearGroup.det y)] using hd.symm

private lemma common_centralizer_scalar [IsAlgClosed F]
    (x y z : GL (Fin 3) F) (u : Fˣ) (hu : u ≠ 1)
    (hxy : x * y = GeneralLinearGroup.scalar (Fin 3) u * (y * x))
    (hzx : Commute z x) (hzy : Commute z y) :
    ∃ c : Fˣ, z = GeneralLinearGroup.scalar (Fin 3) c := by
  let rho := Representation.generalLinearNatural (F := F) 3
  have hucube : (u : F) ^ 3 = 1 := by
    exact congrArg (fun a : Fˣ => (a : F)) (scalar_factor_cube x y u hxy)
  have huone : (u : F) ≠ 1 := by
    intro he
    exact hu (Units.ext he)
  have huorder : orderOf (u : F) = 3 := orderOf_eq_prime hucube huone
  have hlin : rho x * rho y = (u : F) • (rho y * rho x) := by
    have hh := congrArg rho hxy
    have hs : rho (GeneralLinearGroup.scalar (Fin 3) u) =
        (u : F) • (1 : Module.End F (Fin 3 → F)) := natural_scalar u
    simpa only [map_mul, hs, smul_mul_assoc, one_mul] using hh
  obtain ⟨c, hc⟩ := scalar_of_twisted_pair (rho x) (rho y) (rho z)
    (natural_injective x) (natural_injective y) (u : F) huorder hlin
    (hzx.map rho) (hzy.map rho)
  have hc0 : c ≠ 0 := by
    intro hz
    have hzero : rho z = 0 := by simpa [hz] using hc
    have hh : rho z (1 : Fin 3 → F) = rho z 0 := by rw [hzero]; rfl
    exact one_ne_zero (natural_injective z hh)
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Representation.generalLinearNatural_injective 3
  rw [natural_scalar]
  exact hc

private lemma exists_scalar_factor (H : Subgroup (GL (Fin 3) F))
    (hproj : IsMulCommutative (H.map ProjGenLinGroup.mk)) (g x : H) :
    ∃ u : rootsOfUnity 3 F,
      g.val * x.val = GeneralLinearGroup.scalar (Fin 3) u.val * (x.val * g.val) := by
  let := hproj
  let q : H →* H.map ProjGenLinGroup.mk := ProjGenLinGroup.mk.subgroupMap H
  have hcomm : ProjGenLinGroup.mk (x.val * g.val) =
      ProjGenLinGroup.mk (g.val * x.val) := by
    have hh := congrArg Subtype.val (mul_comm (q x) (q g))
    change ProjGenLinGroup.mk x.val * ProjGenLinGroup.mk g.val =
      ProjGenLinGroup.mk g.val * ProjGenLinGroup.mk x.val at hh
    simpa only [map_mul] using hh
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hcomm
  have hrel : g.val * x.val = GeneralLinearGroup.scalar (Fin 3) u * (x.val * g.val) :=
    hu.symm.trans (GeneralLinearGroup.scalar_commute u (x.val * g.val)).symm
  exact ⟨⟨u, by rw [mem_rootsOfUnity]; exact scalar_factor_cube g.val x.val u hrel⟩, hrel⟩

private lemma commute_of_same_factor (g h x : GL (Fin 3) F) (u : Fˣ)
    (hg : g * x = GeneralLinearGroup.scalar (Fin 3) u * (x * g))
    (hh : h * x = GeneralLinearGroup.scalar (Fin 3) u * (x * h)) :
    Commute (h⁻¹ * g) x := by
  have he : g * x * g⁻¹ = h * x * h⁻¹ := by
    rw [hg, hh]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  change (h⁻¹ * g) * x = x * (h⁻¹ * g)
  simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel,
    mul_one] using congrArg (fun t => h⁻¹ * t * g) he

/-- Two commutation factors separate projective classes by the scalar centralizer calculation. -/
private theorem card_projective_image_le_nine_of_noncommuting_algClosed [IsAlgClosed F]
    (H : Subgroup (GL (Fin 3) F))
    (hproj : IsMulCommutative (H.map ProjGenLinGroup.mk))
    (hnc : ¬ IsMulCommutative H) : Nat.card (H.map ProjGenLinGroup.mk) ≤ 3 ^ 2 := by
  classical
  obtain ⟨x, y, hxy⟩ : ∃ x y : H, x * y ≠ y * x := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  obtain ⟨u, hu⟩ := exists_scalar_factor H hproj x y
  have huone : u.val ≠ 1 := by
    intro he
    apply hxy
    apply Subtype.ext
    simpa only [he, map_one, one_mul, Subgroup.coe_mul] using hu
  let A := H.map ProjGenLinGroup.mk
  let q : H →* A := ProjGenLinGroup.mk.subgroupMap H
  have hq : Function.Surjective q := by
    rintro ⟨a, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  let s : A → H := fun a => (hq a).choose
  have hs (a : A) : q (s a) = a := (hq a).choose_spec
  let factor (g t : H) : rootsOfUnity 3 F := (exists_scalar_factor H hproj g t).choose
  have factor_spec (g t : H) :
      g.val * t.val = GeneralLinearGroup.scalar (Fin 3) (factor g t).val * (t.val * g.val) :=
    (exists_scalar_factor H hproj g t).choose_spec
  let evaluate : A → rootsOfUnity 3 F × rootsOfUnity 3 F :=
    fun a => (factor (s a) x, factor (s a) y)
  have hinj : Function.Injective evaluate := by
    intro a b hab
    have hx : factor (s a) x = factor (s b) x := congrArg Prod.fst hab
    have hy : factor (s a) y = factor (s b) y := congrArg Prod.snd hab
    have hcx : Commute ((s b).val⁻¹ * (s a).val) x.val := by
      apply commute_of_same_factor (s a).val (s b).val x.val (factor (s b) x).val
      · simpa only [hx] using factor_spec (s a) x
      · exact factor_spec (s b) x
    have hcy : Commute ((s b).val⁻¹ * (s a).val) y.val := by
      apply commute_of_same_factor (s a).val (s b).val y.val (factor (s b) y).val
      · simpa only [hy] using factor_spec (s a) y
      · exact factor_spec (s b) y
    obtain ⟨c, hc⟩ := common_centralizer_scalar x.val y.val
      ((s b).val⁻¹ * (s a).val) u.val huone hu hcx hcy
    have hqone : q ((s b)⁻¹ * s a) = 1 := by
      apply Subtype.ext
      change ProjGenLinGroup.mk ((s b).val⁻¹ * (s a).val) = 1
      rw [hc, ProjGenLinGroup.mk_scalar]
    rw [map_mul, map_inv, hs, hs, inv_mul_eq_one] at hqone
    exact hqone.symm
  calc
    Nat.card A ≤ Nat.card (rootsOfUnity 3 F × rootsOfUnity 3 F) :=
      Nat.card_le_card_of_injective evaluate hinj
    _ = Nat.card (rootsOfUnity 3 F) * Nat.card (rootsOfUnity 3 F) := Nat.card_prod _ _
    _ ≤ 3 * 3 := Nat.mul_le_mul (card_rootsOfUnity F 3) (card_rootsOfUnity F 3)
    _ = 3 ^ 2 := by norm_num

/-- Noncommuting lifts of an abelian projective subgroup have projective order at most nine. -/
theorem card_projective_image_le_nine_of_noncommuting [Finite F] (_h3 : (3 : F) ≠ 0)
    (H : Subgroup (GL (Fin 3) F))
    (hproj : IsMulCommutative (H.map ProjGenLinGroup.mk))
    (hnc : ¬ IsMulCommutative H) : Nat.card (H.map ProjGenLinGroup.mk) ≤ 3 ^ 2 := by
  classical
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E := GeneralLinearGroup.map (algebraMap F E)
  let j : PGL(3,F) →* PGL(3,E) := ProjGenLinGroup.map (algebraMap F E)
  let H' := H.map f
  have hf : Function.Injective f := matrix_map_injective _
  have hj : Function.Injective j := projective_map_injective _
  have heq : H'.map ProjGenLinGroup.mk = (H.map ProjGenLinGroup.mk).map j := by
    change (H.map f).map ProjGenLinGroup.mk = (H.map ProjGenLinGroup.mk).map j
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  have hproj' : IsMulCommutative (H'.map ProjGenLinGroup.mk) := by
    let := hproj
    rw [heq]
    infer_instance
  have hnc' : ¬ IsMulCommutative H' := by
    intro hcomm
    let := hcomm
    apply hnc
    let e : H ≃* H' := Subgroup.equivMapOfInjective H f hf
    apply IsMulCommutative.of_comm
    intro a b
    apply e.injective
    simp only [map_mul, mul_comm]
  have hb := card_projective_image_le_nine_of_noncommuting_algClosed H' hproj' hnc'
  rw [heq, Subgroup.card_map_of_injective hj] at hb
  exact hb

/-- The noncommuting branch for the full lift of an elementary subgroup of the actual PGL₃. -/
theorem elementary_card_le_nine_of_noncommuting_lift [Finite F] (h3 : (3 : F) ≠ 0)
    (A : Subgroup PGL(3,F)) [IsElementaryAbelian 3 A]
    (hnc : ¬ IsMulCommutative (matrixLift A)) : Nat.card A ≤ 3 ^ 2 := by
  have heq : (matrixLift A).map ProjGenLinGroup.mk = A :=
    Subgroup.map_comap_eq_self_of_surjective ProjGenLinGroup.mk_surjective A
  have hproj : IsMulCommutative ((matrixLift A).map ProjGenLinGroup.mk) := by
    rw [heq]
    infer_instance
  simpa only [heq] using card_projective_image_le_nine_of_noncommuting h3
    (matrixLift A) hproj hnc

end Matrix.ProjectiveDimensionThree
