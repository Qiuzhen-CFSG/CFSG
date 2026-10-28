module
public import Theory.SpecificGroups.SymplecticFour.PlaneNaturalQuotient

/-!
# Displacements of the symplectic plane residual

The upper and lower SL₂ transvections in the literal plane Levi move all
four natural coordinates. Their four displacements generate the additive
natural module, without assuming closure under defining-field scalars.
This is used to recover the whole block layer from its local commutators.
Source: Aschbacher–Smith, original4.3.7, printed p.616; the local matrices
are those of F.1.12(I)(2), printed pp.262–264.
-/

public section
open Matrix
namespace Theory.SpecificGroups.SymplecticFour.PlaneNatural
variable {F : Type*} [Field F] [CharP F 2]

/-- The plane residual moves the entire additive natural four-space. -/
theorem displacements_span (Q : AddSubgroup (Vector F))
    (hQ : ∀ (g : planeLocal (F := F)) v, g.val.val.mulVec v - v ∈ Q) :
    Q = ⊤ := by
  let a : SpecialLinearGroup (Fin 2) F := ⟨!![1,1;0,1],by simp⟩
  let b : SpecialLinearGroup (Fin 2) F := ⟨!![1,0;1,1],by simp⟩
  have ha : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change a.val * a.val = (1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hb : b⁻¹ = b := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    change b.val * b.val = (1 : Matrix (Fin 2) (Fin 2) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [b,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  apply top_unique
  intro v _
  have h0 := hQ (Plane.levi a) (Sum.elim ![0,v (.inl 0)] 0)
  have h1 := hQ (Plane.levi b) (Sum.elim ![v (.inl 1),0] 0)
  have h2 := hQ (Plane.levi b) (Sum.elim (0 : Fin 2 → F) ![0,-v (.inr 0)])
  have h3 := hQ (Plane.levi a) (Sum.elim (0 : Fin 2 → F) ![-v (.inr 1),0])
  have he :
      ((Plane.levi a).val.val.mulVec (Sum.elim ![0,v (.inl 0)] 0) -
        Sum.elim ![0,v (.inl 0)] 0) +
      ((Plane.levi b).val.val.mulVec (Sum.elim ![v (.inl 1),0] 0) -
        Sum.elim ![v (.inl 1),0] 0) +
      ((Plane.levi b).val.val.mulVec (Sum.elim (0 : Fin 2 → F) ![0,-v (.inr 0)]) -
        Sum.elim (0 : Fin 2 → F) ![0,-v (.inr 0)]) +
      ((Plane.levi a).val.val.mulVec (Sum.elim (0 : Fin 2 → F) ![-v (.inr 1),0]) -
        Sum.elim (0 : Fin 2 → F) ![-v (.inr 1),0]) = v := by
    simp only [Plane.levi_matrix,ha,hb]
    ext i
    rcases i with i | i <;> fin_cases i <;>
      simp [a,b, mulVec,dotProduct,Fintype.sum_sum_type,
        Fin.sum_univ_two, fromBlocks, CharTwo.neg_eq]
  exact he ▸ Q.add_mem (Q.add_mem (Q.add_mem h0 h1) h2) h3
end Theory.SpecificGroups.SymplecticFour.PlaneNatural
