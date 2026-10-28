module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/Borel.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.TorusRootAction
public import Mathlib.Algebra.Group.Subgroup.Pointwise
set_option warningAsError false

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
open Matrix
open scoped Pointwise
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
variable (m : ℕ) (hcard : Nat.card F = 3^(2*m+1))
set_option maxHeartbeats 2000000

theorem torus_inv_conjugate_mem (l : Fˣ) {g : Ambient F}
    (hg : g ∈ rootSubgroup m hcard) :
    (torus m l)⁻¹ * g * torus m l ∈ rootSubgroup m hcard := by
  obtain ⟨⟨a,b,c⟩,rfl⟩ := hg
  rw [torus_conjugate_root m hcard]
  exact ⟨(_,_,_),rfl⟩

theorem torus_conjugate_mem (l : Fˣ) {g : Ambient F}
    (hg : g ∈ rootSubgroup m hcard) :
    torus m l * g * (torus m l)⁻¹ ∈ rootSubgroup m hcard := by
  simpa only [← torus_inv, inv_inv] using torus_inv_conjugate_mem m hcard l⁻¹ hg

theorem torus_le_root_normalizer :
    splitTorus (F := F) m ≤ Subgroup.normalizer (rootSubgroup m hcard : Set (Ambient F)) := by
  rintro g ⟨l,rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact torus_conjugate_mem m hcard l
  · intro hu
    have h := torus_inv_conjugate_mem m hcard l hu
    simpa only [torusHom, MonoidHom.coe_mk, OneHom.coe_mk, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

def borel : Subgroup (Ambient F) := rootSubgroup m hcard ⊔ splitTorus m

theorem borel_eq_product : (borel m hcard : Set (Ambient F)) =
    (rootSubgroup m hcard : Set (Ambient F)) * (splitTorus (F := F) m : Set (Ambient F)) :=
  Subgroup.coe_mul_of_right_le_normalizer_left _ _ (torus_le_root_normalizer m hcard)

def borelParam (p : (F × F × F) × Fˣ) : Ambient F :=
  rootElement m p.1.1 p.1.2.1 p.1.2.2 * torus m p.2

theorem borelParam_00 (p : (F × F × F) × Fˣ) :
    (borelParam m p).val 0 0 = theta F m (p.2 : F) := by
  change (rootMatrix m p.1.1 p.1.2.1 p.1.2.2 *
    Matrix.diagonal (fun i => (torusDiagonal m p.2 i : F))) 0 0 = _
  rw [Matrix.mul_diagonal]
  simp [rootMatrix_expanded, rootExpanded, torusDiagonal]

theorem borelParam_injective : Function.Injective (borelParam (F := F) m) := by
  rintro ⟨⟨a,b,c⟩,l⟩ ⟨⟨d,e,f⟩,k⟩ h
  have h0 := congrArg (fun g : Ambient F => g.val 0 0) h
  simp only [borelParam_00] at h0
  have hlk : l = k := Units.ext ((theta F m).injective h0)
  subst k
  have hr : rootElement m a b c = rootElement m d e f := mul_right_cancel h
  have hp : (a,b,c) = (d,e,f) := rootMatrix_injective m (congrArg Units.val hr)
  exact Prod.ext hp rfl

theorem borelParam_mem (p : (F × F × F) × Fˣ) : borelParam m p ∈ borel m hcard :=
  (borel m hcard).mul_mem
    ((show rootSubgroup m hcard ≤ borel m hcard from le_sup_left)
      (show rootElement m p.1.1 p.1.2.1 p.1.2.2 ∈ rootSubgroup m hcard from
      ⟨p.1,rfl⟩))
    ((show splitTorus m ≤ borel m hcard from le_sup_right)
      (show torus m p.2 ∈ splitTorus m from ⟨p.2,rfl⟩))

def borelEquiv : ((F × F × F) × Fˣ) ≃ borel m hcard :=
  Equiv.ofBijective (fun p => ⟨borelParam m p,borelParam_mem m hcard p⟩)
    ⟨fun _ _ h => borelParam_injective m (congrArg Subtype.val h), by
      rintro ⟨g,hg⟩
      rw [← SetLike.mem_coe, borel_eq_product] at hg
      obtain ⟨u,hu,t,ht,rfl⟩ := hg
      obtain ⟨p,rfl⟩ := hu
      obtain ⟨l,rfl⟩ := ht
      exact ⟨(p,l),rfl⟩⟩

theorem card_borel : Nat.card (borel m hcard) = Nat.card F ^ 3 * (Nat.card F - 1) := by
  rw [← Nat.card_congr (borelEquiv m hcard)]
  simp only [Nat.card_prod, Nat.card_units]
  ring
end Atlas.ReeG2
