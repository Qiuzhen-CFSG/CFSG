module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/LinearGroups/Orthogonal/SingularOrthogonality.lean and
SingularPoints.lean, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. Changes: use the native CFSG Clifford Spin
natural action and hyperbolic coordinates, and add explicit crossing lines.
-/

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.NormalRootExtraction.SingularGeometry.Transitivity
import Mathlib.Tactic

/-!
# Perpendicularity and crossing lines in the Spin natural module

Polar perpendicularity descends to singular projective lines and is invariant
under the actual Spin natural action. The standard lines through e₀, e₁, f₀
and f₀ + f₁ give the crossings between the two nontrivial stabilizer orbits
used in the rank-three primitivity argument. This is the concrete split
quadratic geometry underlying GLS3, 1.10.1(b).
-/

@[expose] public section
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace Triality.SimplyConnected.NormalRootExtraction
open Theory.AlgebraicGroup
variable (k : Type*) [Field k]

def SingularPerp (p q : SingularLines k) : Prop :=
  (quadraticForm k).polarBilin p.val.rep q.val.rep = 0

theorem singularLineMk_rep (p : SingularLines k) :
    singularLineMk k p.val.rep p.val.rep_nonzero p.prop = p :=
  Subtype.ext (Projectivization.mk_rep p.val)

theorem singularPerp_symmetric : ∀ ⦃p q⦄, SingularPerp k p q → SingularPerp k q p := by
  intro p q h
  exact (QuadraticMap.polar_comm _ _ _).trans h

theorem singularPerp_mk_iff (u v : QuadraticSpace k) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : quadraticForm k u = 0) (hqv : quadraticForm k v = 0) :
    SingularPerp k (singularLineMk k u hu hqu) (singularLineMk k v hv hqv) ↔
      (quadraticForm k).polarBilin u v = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep k u hu
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  change (quadraticForm k).polarBilin (Projectivization.mk k u hu).rep
    (Projectivization.mk k v hv).rep = 0 ↔ _
  rw [← ha, ← hb]
  change (quadraticForm k).polarBilin (a.val • u) (b.val • v) = 0 ↔ _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_eq_zero,
    a.ne_zero, b.ne_zero, false_or]

theorem singularPerp_base_iff (p : SingularLines k) :
    SingularPerp k (baseLine k) p ↔ p.val.rep.2 0 = 0 := by
  conv_lhs => rw [← singularLineMk_rep k p]
  rw [baseLine, singularPerp_mk_iff]
  simp only [quadraticForm, hyperbolicForm_polar]
  simp [baseVector, Pi.single_apply]

def singularE (i : Fin 4) : QuadraticSpace k := (Pi.single i 1, 0)
def singularF (i : Fin 4) : QuadraticSpace k := (0, Pi.single i 1)

theorem singularE_ne_zero (i : Fin 4) : singularE k i ≠ 0 := by
  intro h
  have := congrArg (fun v : QuadraticSpace k => v.1 i) h
  simp [singularE] at this

theorem singularF_ne_zero (i : Fin 4) : singularF k i ≠ 0 := by
  intro h
  have := congrArg (fun v : QuadraticSpace k => v.2 i) h
  simp [singularF] at this

theorem singularE_singular (i : Fin 4) : quadraticForm k (singularE k i) = 0 := by
  simp [singularE, quadraticForm, hyperbolicForm_apply]

theorem singularF_singular (i : Fin 4) : quadraticForm k (singularF k i) = 0 := by
  simp [singularF, quadraticForm, hyperbolicForm_apply]

def eLine (i : Fin 4) : SingularLines k :=
  singularLineMk k (singularE k i) (singularE_ne_zero k i) (singularE_singular k i)

def fLine (i : Fin 4) : SingularLines k :=
  singularLineMk k (singularF k i) (singularF_ne_zero k i) (singularF_singular k i)

def crossingLine : SingularLines k :=
  singularLineMk k (singularF k 0 + singularF k 1)
    (by
      intro h
      have := congrArg (fun v : QuadraticSpace k => v.2 0) h
      simp [singularF] at this)
    (by simp [singularF, quadraticForm, hyperbolicForm_apply])

theorem singularPerp_eLine_eLine (i j : Fin 4) :
    SingularPerp k (eLine k i) (eLine k j) := by
  rw [eLine, eLine, singularPerp_mk_iff]
  simp only [quadraticForm, hyperbolicForm_polar]
  simp [singularE]

theorem singularPerp_eLine_fLine_iff (i j : Fin 4) :
    SingularPerp k (eLine k i) (fLine k j) ↔ i ≠ j := by
  rw [eLine, fLine, singularPerp_mk_iff]
  simp only [quadraticForm, hyperbolicForm_polar]
  simp [singularE, singularF, Pi.single_apply, eq_comm]

theorem eLine_one_ne_base : eLine k 1 ≠ baseLine k := by
  intro h
  have h' := congrArg Subtype.val h
  change Projectivization.mk k (singularE k 1) _ = Projectivization.mk k (baseVector k) _ at h'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h'
  have := congrArg (fun v : QuadraticSpace k => v.1 1) hc
  simp [singularE, baseVector] at this

theorem fLine_zero_ne_eLine_one : fLine k 0 ≠ eLine k 1 := by
  intro h
  have h' := congrArg Subtype.val h
  change Projectivization.mk k (singularF k 0) _ = Projectivization.mk k (singularE k 1) _ at h'
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h'
  have := congrArg (fun v : QuadraticSpace k => v.2 0) hc
  simp [singularE, singularF] at this

theorem crossingLine_not_perp_base : ¬ SingularPerp k (baseLine k) (crossingLine k) := by
  rw [baseLine, crossingLine, singularPerp_mk_iff]
  simp only [quadraticForm, hyperbolicForm_polar]
  simp [baseVector, singularF, Pi.single_apply]

theorem crossingLine_not_perp_eLine_one : ¬ SingularPerp k (eLine k 1) (crossingLine k) := by
  rw [eLine, crossingLine, singularPerp_mk_iff]
  simp only [quadraticForm, hyperbolicForm_polar]
  simp [singularE, singularF, Pi.single_apply, eq_comm]

variable [IsAlgClosed k]

theorem naturalAction_polar (g : Points k) (u v : QuadraticSpace k) :
    (quadraticForm k).polarBilin ((naturalAction k g).val u) ((naturalAction k g).val v) =
      (quadraticForm k).polarBilin u v := by
  have hq := (mem_quadraticIsometrySubgroup _ _).mp (naturalAction k g).prop
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add, hq]

theorem singularPerp_smul_iff (g : Points k) (p q : SingularLines k) :
    SingularPerp k (g • p) (g • q) ↔ SingularPerp k p q := by
  rw [← singularLineMk_rep k p, ← singularLineMk_rep k q,
    singularLineMk_smul, singularLineMk_smul, singularPerp_mk_iff,
    singularPerp_mk_iff, naturalAction_polar]

end Triality.SimplyConnected.NormalRootExtraction
