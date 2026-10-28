module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The central quotient for the local analysis of PSL₄(3)

The carrier is Mathlib's actual SL₄(3)/Z(SL₄(3)). Its kernel has order two;
projective involution lifts square to scalar matrices. Projectively commuting
lifts have central commutators of exponent two, so their squares commute.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed p.4,
repeated as Theorem 0.1.1(4) on printed p.482 of `refs/quasithin.pdf`.
-/

open Matrix Subgroup
open scoped commutatorElement
noncomputable section
namespace Matrix.PSL4Three.LocalThree

public abbrev SL := SpecialLinearGroup (Fin 4) (ZMod 3)
public abbrev P := ProjectiveSpecialLinearGroup (Fin 4) (ZMod 3)
public abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 3)
@[expose] public def project : SL →* P := QuotientGroup.mk' (center SL)
public theorem project_surjective : Function.Surjective project := QuotientGroup.mk'_surjective _
public theorem project_eq_one_iff (g : SL) : project g = 1 ↔ g ∈ center SL :=
  QuotientGroup.eq_one_iff g

public theorem center_square (g : SL) (hg : g ∈ center SL) : g ^ 2 = 1 := by
  obtain ⟨c, hc, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  have hc2 : c ^ 2 = 1 := (by decide : ∀ c : ZMod 3, c ^ 4 = 1 → c ^ 2 = 1) c hc
  apply Subtype.ext
  change (g : Mat) ^ 2 = 1
  rw [← he, ← map_pow, hc2, map_one]

public theorem card_center : Nat.card (center SL) = 2 := by
  rw [Atlas.ExceptionalSupport.card_sl_center]
  norm_num

public theorem square_scalar (g : SL) (hg : (project g)^2 = 1) :
    ∃ c : ZMod 3, c ^ 2 = 1 ∧ (g : Mat)^2 = c • (1 : Mat) := by
  have hz : g ^ 2 ∈ center SL := (project_eq_one_iff _).mp (by simpa using hg)
  obtain ⟨c, hc, he⟩ := SpecialLinearGroup.mem_center_iff.mp hz
  refine ⟨c, (by decide : ∀ c : ZMod 3, c^4=1 → c^2=1) c hc, ?_⟩
  simpa only [SpecialLinearGroup.coe_pow, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal] using he.symm

public theorem project_eq_one_of_scalar (g : SL) (c : ZMod 3) (hg : (g : Mat) = c • 1) :
    project g = 1 := by
  apply (project_eq_one_iff _).mpr
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  change (x : Mat) * (g : Mat) = (g : Mat) * (x : Mat)
  rw [hg, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]


/-- The square of a lift centralizes every projectively commuting lift. -/
public theorem square_commute_of_project_commute (x y : SL)
    (h : Commute (project x) (project y)) : Commute (x ^ 2) y := by
  have hz : ⁅x, y⁆ ∈ center SL := (project_eq_one_iff _).mp (by
    rw [map_commutatorElement]
    exact h.commutator_eq)
  apply commutatorElement_eq_one_iff_commute.mp
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp hz x, mul_inv_cancel_right, ← pow_two]
  exact center_square _ hz

end Matrix.PSL4Three.LocalThree
