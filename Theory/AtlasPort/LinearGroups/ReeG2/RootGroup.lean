module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/RootGroup.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG imports, Lean 4.33 proof adaptations, and public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.RootMultiplication
set_option warningAsError false

@[expose] public section

/-! The actual three-parameter subgroup of the generated matrix group. -/
noncomputable section
namespace Atlas.ReeG2
variable {F : Type*} [Field F] [Finite F] [CharP F 3]
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem rootElement_zero (m : ℕ) : rootElement (F := F) m 0 0 0 = 1 := by
  apply Units.ext
  exact rootMatrix_zero m

theorem rootElement_mul (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1))
    (a b c d e f : F) :
    rootElement m a b c * rootElement m d e f =
      rootElement m (a+d) (b+e-a*(theta F m d)^3)
        (c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3) := by
  apply Units.ext
  exact rootMatrix_mul m hcard a b c d e f

theorem rootElement_inv (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1)) (a b c : F) :
    (rootElement m a b c)⁻¹ =
      rootElement m (-a) (-(b+a*(theta F m a)^3)) (-(c+a*b-a^2*(theta F m a)^3)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [rootElement_mul m hcard]
  simp only [map_neg, add_neg_cancel]
  have hb : b + -(b+a*(theta F m a)^3) - a*(-theta F m a)^3 = 0 := by ring
  have hc : (3 : F) = 0 := CharP.cast_eq_zero F 3
  convert rootElement_zero (F := F) m using 1 <;> congr 1 <;>
    ring_nf <;> reduce_mod_char!

def rootSubgroup (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1)) : Subgroup (Ambient F) where
  carrier := Set.range (fun p : F × F × F => rootElement m p.1 p.2.1 p.2.2)
  one_mem' := ⟨(0,0,0), rootElement_zero m⟩
  mul_mem' := by
    rintro _ _ ⟨⟨a,b,c⟩,rfl⟩ ⟨⟨d,e,f⟩,rfl⟩
    exact ⟨(a+d,b+e-a*(theta F m d)^3,
      c+f-d*b+a*(theta F m d)^3*d-a^2*(theta F m d)^3),
      (rootElement_mul m hcard a b c d e f).symm⟩
  inv_mem' := by
    rintro _ ⟨⟨a,b,c⟩,rfl⟩
    exact ⟨(-a,-(b+a*(theta F m a)^3),-(c+a*b-a^2*(theta F m a)^3)),
      (rootElement_inv m hcard a b c).symm⟩

def rootParameterEquiv (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1)) :
    (F × F × F) ≃ rootSubgroup m hcard :=
  Equiv.ofBijective (fun p => ⟨rootElement m p.1 p.2.1 p.2.2, ⟨p,rfl⟩⟩)
    ⟨fun _ _ h => rootMatrix_injective m (congrArg (fun g => g.val.val) h),
      by rintro ⟨g,p,hp⟩; exact ⟨p, Subtype.ext hp⟩⟩

theorem card_rootSubgroup (m : ℕ) (hcard : Nat.card F = 3 ^ (2*m+1)) :
    Nat.card (rootSubgroup m hcard) = Nat.card F ^ 3 := by
  rw [← Nat.card_congr (rootParameterEquiv m hcard), Nat.card_prod, Nat.card_prod]
  ring

@[simp] theorem alpha_zero (m : ℕ) : alpha (F := F) m 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [alphaMatrix]

@[simp] theorem beta_zero (m : ℕ) : beta (F := F) m 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [betaMatrix]

@[simp] theorem gamma_zero (m : ℕ) : gamma (F := F) m 0 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gammaMatrix]

def rootGenerated (m : ℕ) : Subgroup (Ambient F) :=
  Subgroup.closure (Set.range (alpha (F := F) m) ∪ Set.range (beta (F := F) m) ∪
    Set.range (gamma (F := F) m))

theorem rootSubgroup_eq_generated (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    rootSubgroup m hcard = rootGenerated (F := F) m := by
  apply le_antisymm
  · rintro g ⟨⟨a,b,c⟩, rfl⟩
    apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Or.inl (Or.inl ⟨a,rfl⟩))
      · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨b,rfl⟩))
    · exact Subgroup.subset_closure (Or.inr ⟨c,rfl⟩)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with (ha | hb) | hc
    · obtain ⟨a,rfl⟩ := ha
      exact ⟨(a,0,0), by simp [rootElement]⟩
    · obtain ⟨b,rfl⟩ := hb
      exact ⟨(0,b,0), by simp [rootElement]⟩
    · obtain ⟨c,rfl⟩ := hc
      exact ⟨(0,0,c), by simp [rootElement]⟩

theorem rootSubgroup_le_generated (m : ℕ) (hcard : Nat.card F = 3^(2*m+1)) :
    rootSubgroup m hcard ≤ generated F m := by
  rw [rootSubgroup_eq_generated]
  apply Subgroup.closure_mono
  intro g hg
  exact Or.inl (Or.inl hg)
end Atlas.ReeG2
