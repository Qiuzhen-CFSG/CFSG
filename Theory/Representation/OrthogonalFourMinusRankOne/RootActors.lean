module

public import Theory.Representation.OrthogonalFourMinusRankOne.LocalGeometry
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Fixed spaces and ratios of Hermitian root actors

The centralizer R_t in the canonical Sylow root group is the additive fixed
field. It is quadratic of rank s and fixes a K-plane, so its binary action
ratio is two. The whole root group is elementary of rank 2s, fixes a K-line,
and is cubic but not quadratic, with ratio 3/2. Every nonquadratic subgroup
of this root group has the same fixed line. All statements include s=1.

The proof uses explicit fixed-space coordinate equivalences and the actual
finite-field cardinalities. These actor calculations give upper bounds;
classification of arbitrary ambient actors and proofs of global minima are
separate obligations.
Source: Aschbacher–Smith, K.3.1.2, printed p.454, and D.2.1, printed p.178.
-/

@[expose] public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.HermitianEquiv
open Representation.BinaryOffender
open Matrix.SpecialLinearGroup
variable (s : ℕ) [NeZero s]
local instance : Algebra (ZMod 2) (fixedField s) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space s) :=
  Module.compHom (Space s) (algebraMap (ZMod 2) (fixedField s))

/-- The source's `R_t` in the canonical Sylow group. -/
def fixedRootGroup : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)) :=
  upperUnipotent (Field s) ⊓ involutionCentralizer s

theorem mem_fixedRootGroup_iff (A : Matrix.SpecialLinearGroup (Fin 2) (Field s)) :
    A ∈ fixedRootGroup s ↔ ∃ u : fixedField s, upper s u.val = A :=
  mem_root_centralizer_iff s A

private theorem root_fixed_of_entries (u : Field s) (X : Space s)
    (hb : X.val 1 1 = 0)
    (hz : u * conjugation s (X.val 0 1) + conjugation s u * X.val 0 1 = 0) :
    action s (upper s u) X = X := by
  by_cases hu : u = 0
  · subst u
    change action s (Matrix.SpecialLinearGroup.transvection zero_ne_one 0) X = X
    rw [transvection_coeff_zero, map_one, Module.End.one_apply]
  · exact (root_fixed_iff s hu X).mpr ⟨hb, hz⟩

theorem mem_fixedSpace_fixedRootGroup_iff (X : Space s) :
    X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) ↔
      X.val 1 1 = 0 ∧ conjugation s (X.val 0 1) = X.val 0 1 := by
  constructor
  · intro h
    have h1 : action s (upper s 1) X = X :=
      h ⟨upper s 1, (mem_fixedRootGroup_iff s _).mpr ⟨1, rfl⟩⟩
    have he := (root_fixed_iff s one_ne_zero X).mp h1
    refine ⟨he.1, ?_⟩
    simpa only [one_mul, map_one, CharTwo.add_eq_zero] using he.2
  · rintro ⟨hb, hz⟩ g
    obtain ⟨u, hu⟩ := (mem_fixedRootGroup_iff s _).mp g.property
    change action s g.val X = X
    rw [← hu]
    apply root_fixed_of_entries s _ X hb
    have huf : conjugation s u.val = u.val := u.property
    rw [hz, huf, CharTwo.add_self_eq_zero]

theorem mem_fixedSpace_upper_iff (X : Space s) :
    X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) ↔
      X.val 1 1 = 0 ∧ X.val 0 1 = 0 := by
  constructor
  · intro h
    have hR : X ∈ fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) :=
      fun g => h ⟨g.val, g.property.1⟩
    obtain ⟨hb, hz⟩ := (mem_fixedSpace_fixedRootGroup_iff s X).mp hR
    obtain ⟨u, hu⟩ := exists_conjugation_ne s
    have hu0 : u ≠ 0 := by rintro rfl; exact hu (map_zero _)
    have he := (root_fixed_iff s hu0 X).mp
      (h ⟨upper s u, (mem_upperUnipotent _ _).mpr ⟨u, rfl⟩⟩)
    have he' : (u + conjugation s u) * X.val 0 1 = 0 := by
      rw [add_mul]
      simpa only [hz] using he.2
    refine ⟨hb, (mul_eq_zero.mp he').resolve_left ?_⟩
    intro hzero
    exact hu (CharTwo.add_eq_zero.mp hzero).symm
  · rintro ⟨hb, hz⟩ g
    obtain ⟨u, hu⟩ := (mem_upperUnipotent _ _).mp g.property
    change action s g.val X = X
    rw [← hu]
    exact root_fixed_of_entries s u X hb (by rw [hz, map_zero, mul_zero, mul_zero, add_zero])

/-- Coordinates on the fixed plane of `R_t`. -/
def fixedRootFixedEquivK :
    Representation.invariants ((action s).comp (fixedRootGroup s).subtype) ≃ₗ[fixedField s]
      (fixedField s × fixedField s) where
  toFun X := (⟨X.val.val 0 0, entry_fixed s X.val 0⟩,
    ⟨X.val.val 0 1, ((mem_fixedSpace_fixedRootGroup_iff s X.val).mp X.property).2⟩)
  invFun ab := ⟨(coordinates s).symm ((ab.1, 0), ab.2.val),
    (mem_fixedSpace_fixedRootGroup_iff s _).mpr ⟨rfl, ab.2.property⟩⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    have hb := ((mem_fixedSpace_fixedRootGroup_iff s X.val).mp X.property).1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinates_symm_val, hb, entry_conjugate s X.val 1 0]
  right_inv ab := rfl
  map_add' X Y := rfl
  map_smul' c X := rfl

/-- Coordinates on the common fixed line of the entire Sylow root group. -/
def upperFixedEquivK :
    Representation.invariants ((action s).comp (upperUnipotent (Field s)).subtype) ≃ₗ[fixedField s]
      fixedField s where
  toFun X := ⟨X.val.val 0 0, entry_fixed s X.val 0⟩
  invFun a := ⟨(coordinates s).symm ((a, 0), 0),
    (mem_fixedSpace_upper_iff s _).mpr ⟨rfl, rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨hb, hz⟩ := (mem_fixedSpace_upper_iff s X.val).mp X.property
    have hz' : X.val.val 1 0 = 0 := by
      rw [← entry_conjugate s X.val 1 0, hz, map_zero]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinates_symm_val, hb, hz, hz']
  right_inv a := rfl
  map_add' X Y := rfl
  map_smul' c X := rfl

def fixedRootFixedEquiv :
    fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s) ≃ₗ[ZMod 2]
      (fixedField s × fixedField s) :=
  { (fixedRootFixedEquivK s).toAddEquiv with map_smul' := ZMod.map_smul ((fixedRootFixedEquivK s).toAddEquiv) }

def upperFixedEquiv :
    fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) ≃ₗ[ZMod 2]
      fixedField s :=
  { (upperFixedEquivK s).toAddEquiv with map_smul' := ZMod.map_smul ((upperFixedEquivK s).toAddEquiv) }

theorem fixedRoot_fixed_Kfinrank :
    Module.finrank (fixedField s)
      (Representation.invariants ((action s).comp (fixedRootGroup s).subtype)) = 2 := by
  rw [(fixedRootFixedEquivK s).finrank_eq, Module.finrank_prod]
  simp

/-- The absolute degree of the fixed field is the source parameter. -/
theorem fixedField_binary_finrank : Module.finrank (ZMod 2) (fixedField s) = s := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedField s)
  rw [card_fixedField, Nat.card_zmod] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc.symm

theorem space_binary_finrank : Module.finrank (ZMod 2) (Space s) = 4 * s := by
  have hc := Module.natCard_eq_pow_finrank (K := fixedField s) (V := Space s)
  rw [card_fixedField, finrank_space, ← pow_mul, Nat.mul_comm s 4] at hc
  have hb := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Space s)
  have he : 2 ^ Module.finrank (ZMod 2) (Space s) = 2 ^ (4 * s) := by
    simpa only [Nat.card_zmod] using hb.symm.trans hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he

theorem fixedRoot_fixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace (SL2.BinarySmall.hermitian s) (fixedRootGroup s)) =
      2 * s := by
  rw [(fixedRootFixedEquiv s).finrank_eq, Module.finrank_prod, fixedField_binary_finrank]
  omega

theorem upper_fixed_finrank :
    Module.finrank (ZMod 2) (fixedSpace (SL2.BinarySmall.hermitian s)
      (upperUnipotent (Field s))) = s := by
  rw [(upperFixedEquiv s).finrank_eq, fixedField_binary_finrank]

theorem fixedRoot_fixedCodim :
    fixedCodim (SL2.BinarySmall.hermitian s) (fixedRootGroup s) = 2 * s := by
  have h := fixedCodim_add_finrank (SL2.BinarySmall.hermitian s) (fixedRootGroup s)
  rw [fixedRoot_fixed_finrank, space_binary_finrank] at h
  omega

theorem upper_fixedCodim :
    fixedCodim (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) = 3 * s := by
  have h := fixedCodim_add_finrank (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s))
  rw [upper_fixed_finrank, space_binary_finrank] at h
  omega


/-- Fixed-field root parameters, as a homomorphism into the actual layer. -/
def fixedRootHom : Multiplicative (fixedField s) →*
    Matrix.SpecialLinearGroup (Fin 2) (Field s) where
  toFun u := upper s u.toAdd.val
  map_one' := transvection_coeff_zero _
  map_mul' u v := transvection_add _ u.toAdd.val v.toAdd.val

omit [NeZero s] in
theorem fixedRootHom_injective : Function.Injective (fixedRootHom s) := by
  intro u v h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  have he := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) (Field s) => A.val 0 1) h
  simpa [fixedRootHom, upper, transvection_coe] using he

theorem range_fixedRootHom : (fixedRootHom s).range = fixedRootGroup s := by
  ext A
  rw [mem_fixedRootGroup_iff]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u.toAdd, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨Multiplicative.ofAdd u, rfl⟩

/-- The root centralizer is the additive group of the actual fixed field. -/
def fixedRootEquiv : Multiplicative (fixedField s) ≃* fixedRootGroup s :=
  (MonoidHom.ofInjective (fixedRootHom_injective s)).trans
    (MulEquiv.subgroupCongr (range_fixedRootHom s))

theorem fixedRoot_rank : rank (fixedRootGroup s) = s := by
  rw [rank, ← Nat.card_congr (fixedRootEquiv s).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (fixedField s) ≃ fixedField s),
    card_fixedField, Nat.log_pow (by decide : 1 < 2)]

theorem upper_rank : rank (upperUnipotent (Field s)) = 2 * s := by
  rw [rank, card_upperUnipotent, GaloisField.card 2 (2 * s)
    (Nat.mul_ne_zero (by decide) (NeZero.ne s)), Nat.log_pow (by decide : 1 < 2)]

private theorem elementary_of_additive_equiv {F H : Type*} [Field F] [CharP F 2]
    [Group H] (e : Multiplicative F ≃* H) : IsElementaryAbelian 2 H where
  toIsMulCommutative := ⟨⟨fun x y => e.symm.injective (by simp [mul_comm])⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
    apply e.symm.injective
    rw [map_pow, map_one, pow_two]
    change Multiplicative.ofAdd ((e.symm x).toAdd + (e.symm x).toAdd) = Multiplicative.ofAdd 0
    rw [CharTwo.add_self_eq_zero])

theorem fixedRoot_elementary : IsElementaryTwo (fixedRootGroup s) := by
  refine ⟨?_, elementary_of_additive_equiv (fixedRootEquiv s)⟩
  intro h
  have he := fixedRoot_rank s
  rw [h] at he
  have hz : s = 0 := by simpa [rank] using he.symm
  exact NeZero.ne s hz

theorem upper_elementary : IsElementaryTwo (upperUnipotent (Field s)) := by
  refine ⟨?_, elementary_of_additive_equiv
    (MonoidHom.ofInjective (upperUnipotentHom_injective (Field s)))⟩
  intro h
  have he := upper_rank s
  rw [h] at he
  have hz : 2 * s = 0 := by simpa [rank] using he.symm
  have hs := NeZero.ne s
  omega

theorem fixedRoot_quadratic :
    IsQuadratic (SL2.BinarySmall.hermitian s) (fixedRootGroup s) := by
  apply (root_subgroup_quadratic_iff s _ inf_le_left).mpr
  intro u v hu hv
  have hu' := ((mem_involutionCentralizer_iff s _).mp hu.2) 0 1
  have hv' := ((mem_involutionCentralizer_iff s _).mp hv.2) 0 1
  have hu'' : conjugation s u = u := by simpa [upper, transvection_coe] using hu'
  have hv'' : conjugation s v = v := by simpa [upper, transvection_coe] using hv'
  rw [hu'', hv'', CharTwo.add_self_eq_zero]

open scoped ENNReal

theorem fixedRoot_actionRatio :
    actionRatio (SL2.BinarySmall.hermitian s) (fixedRootGroup s) = 2 := by
  rw [actionRatio, fixedRoot_fixedCodim, fixedRoot_rank, Nat.cast_mul]
  exact ENNReal.mul_div_cancel_right (by exact_mod_cast NeZero.ne s) (by simp)

theorem upper_actionRatio :
    actionRatio (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) = 3 / 2 := by
  rw [actionRatio, upper_fixedCodim, upper_rank]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by simp)
    (by exact_mod_cast Nat.mul_ne_zero (by decide : 2 ≠ 0) (NeZero.ne s))
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using (ENNReal.natCast_ne_top (2 * s)))).mpr
  push_cast
  ring

/-- Concrete actors supply the upper bounds in the orthogonal row of B.4.5. -/
theorem ratio_upper_bounds :
    quadraticRatio (SL2.BinarySmall.hermitian s) ≤ 2 ∧
      cubicRatio (SL2.BinarySmall.hermitian s) ≤ 3 / 2 := by
  constructor
  · exact iInf_le_of_le (fixedRootGroup s) (iInf_le_of_le
      ⟨fixedRoot_elementary s, fixedRoot_quadratic s⟩ (le_of_eq (fixedRoot_actionRatio s)))
  · exact iInf_le_of_le (upperUnipotent (Field s)) (iInf_le_of_le
      ⟨upper_elementary s, root_subgroup_cubic s _ le_rfl⟩ (le_of_eq (upper_actionRatio s)))


/-- Every nonquadratic subgroup of this Sylow root group has the same fixed
line as the full root group. -/
theorem fixedSpace_eq_upper_of_not_quadratic
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hA : A ≤ upperUnipotent (Field s))
    (hn : ¬ IsQuadratic (SL2.BinarySmall.hermitian s) A) :
    fixedSpace (SL2.BinarySmall.hermitian s) A =
      fixedSpace (SL2.BinarySmall.hermitian s) (upperUnipotent (Field s)) := by
  have hn' := (root_subgroup_quadratic_iff s A hA).not.mp hn
  push Not at hn'
  obtain ⟨u, v, huA, hvA, huv⟩ := hn'
  have hu0 : u ≠ 0 := by rintro rfl; simp at huv
  have hv0 : v ≠ 0 := by rintro rfl; simp at huv
  ext X
  constructor
  · intro hX
    obtain ⟨hb, hzu⟩ := (root_fixed_iff s hu0 X).mp (hX ⟨_, huA⟩)
    have hzv := ((root_fixed_iff s hv0 X).mp (hX ⟨_, hvA⟩)).2
    apply (mem_fixedSpace_upper_iff s X).mpr
    refine ⟨hb, ?_⟩
    have he : (u * conjugation s v + conjugation s u * v) * X.val 0 1 = 0 := by
      linear_combination u * hzv + v * hzu -
        (u * conjugation s (X.val 0 1)) * CharTwo.add_self_eq_zero v
    exact (mul_eq_zero.mp he).resolve_left huv
  · intro hX g
    exact hX ⟨g.val, hA g.property⟩

theorem fixedCodim_eq_of_not_quadratic
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field s)))
    (hA : A ≤ upperUnipotent (Field s))
    (hn : ¬ IsQuadratic (SL2.BinarySmall.hermitian s) A) :
    fixedCodim (SL2.BinarySmall.hermitian s) A = 3 * s := by
  unfold fixedCodim
  rw [fixedSpace_eq_upper_of_not_quadratic s A hA hn]
  exact upper_fixedCodim s



end Representation.OrthogonalFourMinus.RankOne
