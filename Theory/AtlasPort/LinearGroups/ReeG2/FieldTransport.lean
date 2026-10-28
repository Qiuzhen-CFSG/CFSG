module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/ReeG2/FieldTransport.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearGroups.ReeG2.Generators

/-!
# Field transport for the small Ree matrix group

Entrywise field transport commutes with the Frobenius twist, hence carries each
root, torus and Weyl generator to the corresponding generator. Closure induction
restricts this equivalence to the actual generated subgroups. No cardinality
restriction is needed for transport; both fields have characteristic three.
-/

@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable {F K : Type*} [Field F] [Finite F] [CharP F 3]
  [Field K] [Finite K] [CharP K 3]

/-- Entrywise field transport of the ambient invertible matrices. -/
def ambientFieldEquiv (e : F ≃+* K) : Ambient F ≃* Ambient K :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

omit [Finite F] [CharP F 3] [Finite K] [CharP K 3] in
@[simp] theorem ambientFieldEquiv_entry (e : F ≃+* K) (g : Ambient F) (i j : Fin 7) :
    (ambientFieldEquiv e g).val i j = e (g.val i j) := rfl

theorem transport_alpha (e : F ≃+* K) (m : ℕ) (a : F) :
    ambientFieldEquiv e (alpha m a) = alpha m (e a) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientFieldEquiv_entry,alpha,alphaMatrix,-theta_apply,map_theta]

theorem transport_beta (e : F ≃+* K) (m : ℕ) (b : F) :
    ambientFieldEquiv e (beta m b) = beta m (e b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientFieldEquiv_entry,beta,betaMatrix,-theta_apply,map_theta]

theorem transport_gamma (e : F ≃+* K) (m : ℕ) (c : F) :
    ambientFieldEquiv e (gamma m c) = gamma m (e c) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientFieldEquiv_entry,gamma,gammaMatrix,-theta_apply,map_theta]

theorem transport_torus (e : F ≃+* K) (m : ℕ) (l : Fˣ) :
    ambientFieldEquiv e (torus m l) = torus m (Units.mapEquiv e.toMulEquiv l) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientFieldEquiv_entry,torus,diagonalUnit,torusDiagonal,-theta_apply,map_theta]

omit [Finite F] [CharP F 3] [Finite K] [CharP K 3] in
theorem transport_upsilon (e : F ≃+* K) :
    ambientFieldEquiv e upsilon = upsilon := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientFieldEquiv_entry,upsilon,upsilonMatrix]

theorem transport_mem_generated (e : F ≃+* K) (m : ℕ) {g : Ambient F}
    (hg : g ∈ generated F m) : ambientFieldEquiv e g ∈ generated K m := by
  have hle : generated F m ≤ (generated K m).comap (ambientFieldEquiv e).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    change ambientFieldEquiv e g ∈ generated K m
    rcases hg with (((⟨a,rfl⟩ | ⟨b,rfl⟩) | ⟨c,rfl⟩) | ⟨l,rfl⟩) | hw
    · rw [transport_alpha]
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inl ⟨e a,rfl⟩))))
    · rw [transport_beta]
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl (Or.inr ⟨e b,rfl⟩))))
    · rw [transport_gamma]
      exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨e c,rfl⟩)))
    · rw [transport_torus]
      exact Subgroup.subset_closure (Or.inl (Or.inr ⟨_,rfl⟩))
    · have : g = upsilon := Set.mem_singleton_iff.mp hw
      subst g
      rw [transport_upsilon]
      exact Subgroup.subset_closure (Or.inr rfl)
  exact hle hg

/-- Concrete equivalence between the actual matrix groups over equivalent fields. -/
def fieldEquiv (e : F ≃+* K) (m : ℕ) : Model F m ≃* Model K m where
  toFun g := ⟨ambientFieldEquiv e g.val,transport_mem_generated e m g.property⟩
  invFun g := ⟨ambientFieldEquiv e.symm g.val,transport_mem_generated e.symm m g.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.symm_apply_apply _
  right_inv g := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact e.apply_symm_apply _
  map_mul' g h := Subtype.ext ((ambientFieldEquiv e).map_mul g.val h.val)

end Atlas.ReeG2
