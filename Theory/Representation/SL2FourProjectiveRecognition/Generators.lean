module

public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors

/-!
# Concrete generators for the SL₂(4) projective recognition argument

The Weyl matrix exchanges the coordinate lines and conjugates each upper
root into its lower root. Mathlib's transvection induction therefore gives
generation by that Weyl matrix and the full upper root group. The explicit
six-factor word is diag(ω,ω+1), where ω²=ω+1, so it preserves the first
coordinate line used in the projective criterion.

The final invariance and equivariance lemmas are the direct representation
consumers: checks on the prescribed generators extend to the entire group.
Closed field and matrix identities are kernel-checked calculations over
four elements; group generation uses the algebraic induction theorem.
Source: Aschbacher–Smith G.1.3, printed pp.327–328, specialized to SL₂(4).
-/

@[expose] public section
noncomputable section
open Matrix Subgroup
namespace Representation.SL2FourNatural.ProjectiveRecognition

def weyl : SL := ⟨!![0,1;1,0], by decide +kernel⟩
def omega : F := QuadraticAlgebra.omega

theorem omega_sq : omega ^ 2 = omega + 1 := by decide +kernel
theorem omega_ne_zero : omega ≠ 0 := by decide +kernel
theorem omega_ne_one : omega ≠ 1 := by decide +kernel
theorem field_cases (t : F) : t = 0 ∨ t = 1 ∨ t = omega ∨ t = omega + 1 := by
  revert t
  decide +kernel

theorem weyl_mul_self : weyl * weyl = 1 := by decide +kernel
theorem weyl_inv : weyl⁻¹ = weyl := inv_eq_of_mul_eq_one_right weyl_mul_self

theorem upper_zero : upper 0 = 1 := by decide +kernel

theorem upper_add (t s : F) : upper (t+s) = upper t * upper s := by
  apply Subtype.ext
  change (!![1,t+s;0,1] : Matrix (Fin 2) (Fin 2) F) = !![1,t;0,1] * !![1,s;0,1]
  funext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem upper_mul_self (t : F) : upper t * upper t = 1 := by
  rw [← upper_add, CharTwo.add_self_eq_zero, upper_zero]

theorem upper_one_braid : upper 1 * weyl * upper 1 = weyl * upper 1 * weyl := by
  decide +kernel

theorem weyl_upper_weyl (t : F) :
    weyl * upper t * weyl = SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t := by
  apply Subtype.ext
  change (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) F) * !![1,t;0,1] * !![0,1;1,0] = _
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, SpecialLinearGroup.transvection_coe]

theorem upper_weyl_induction (P : SL → Prop)
    (hupper : ∀ t : F, P (upper t)) (hweyl : P weyl)
    (hmul : ∀ a b, P a → P b → P (a*b)) (g : SL) : P g := by
  apply Matrix.SL2.transvection_induction P ?_ hmul g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · rw [← BorelFactors.upper_eq_transvection]
    exact hupper t
  · rw [← weyl_upper_weyl]
    exact hmul _ _ (hmul _ _ hweyl (hupper t)) hweyl
  · exact False.elim (hij rfl)

theorem closure_weyl_upper :
    closure ({weyl} ∪ Set.range upper : Set SL) = ⊤ := by
  apply top_unique
  intro g _
  apply upper_weyl_induction (fun a => a ∈ closure ({weyl} ∪ Set.range upper : Set SL))
    (fun t => subset_closure (Or.inr ⟨t,rfl⟩))
    (subset_closure (Or.inl rfl)) (fun _ _ => mul_mem) g

def diagonalWord : SL := upper omega * weyl * upper (omega+1) * weyl * upper omega * weyl

theorem diagonalWord_val : diagonalWord.val = !![omega,0;0,omega+1] := by decide +kernel

theorem diagonalWord_pow_three : diagonalWord ^ 3 = 1 := by decide +kernel

theorem weyl_action (v : V) : specialLinearNatural 2 weyl v = ![v 1,v 0] := by
  rw [specialLinearNatural_apply]
  funext i
  fin_cases i <;> simp [weyl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem diagonalWord_action (v : V) :
    specialLinearNatural 2 diagonalWord v = ![omega*v 0,(omega+1)*v 1] := by
  rw [specialLinearNatural_apply,diagonalWord_val]
  funext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two]

theorem weyl_map_first :
    (Submodule.span F {(![1,0] : V)}).map (specialLinearNatural 2 weyl) =
      Submodule.span F {(![0,1] : V)} := by
  rw [Submodule.map_span,Set.image_singleton,weyl_action]
  rfl

theorem diagonalWord_map_first :
    (Submodule.span F {(![1,0] : V)}).map (specialLinearNatural 2 diagonalWord) =
      Submodule.span F {(![1,0] : V)} := by
  rw [Submodule.map_span,Set.image_singleton,diagonalWord_action]
  have he : (![omega * (![1,0] : V) 0,(omega+1) * (![1,0] : V) 1] : V) =
      omega • (![1,0] : V) := by funext i; fin_cases i <;> simp
  rw [he]
  apply Submodule.span_singleton_smul_eq
  exact isUnit_iff_ne_zero.mpr omega_ne_zero

abbrev firstLine : Submodule F V := Submodule.span F {(![1,0] : V)}

theorem mem_firstLine (v : V) : v ∈ firstLine ↔ v 1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t,rfl⟩
    simp
  · intro hv
    refine ⟨v 0, ?_⟩
    funext i
    fin_cases i <;> simp [hv]

theorem firstLine_weyl_ne : firstLine ≠ firstLine.map (specialLinearNatural 2 weyl) := by
  intro he
  have hv : (![1,0] : V) ∈ firstLine.map (specialLinearNatural 2 weyl) :=
    he ▸ Submodule.subset_span (Set.mem_singleton _)
  rw [weyl_map_first,Submodule.mem_span_singleton] at hv
  obtain ⟨t,ht⟩ := hv
  have hz := congrFun ht 0
  simp at hz

theorem diagonalWord_firstLine : firstLine.map (specialLinearNatural 2 diagonalWord) = firstLine :=
  diagonalWord_map_first

theorem upper_fixed_firstLine (t : F) (v : V) (hv : v ∈ firstLine) :
    specialLinearNatural 2 (upper t) v = v := by
  have hv := (mem_firstLine v).mp hv
  change Matrix.mulVec (upper t).val v = v
  funext i
  fin_cases i <;> simp [upper,Matrix.mulVec,dotProduct,Fin.sum_univ_two,hv]

theorem upper_displacement_firstLine (t : F) (v : V) :
    specialLinearNatural 2 (upper t) v - v ∈ firstLine := by
  apply (mem_firstLine _).mpr
  change (Matrix.mulVec (upper t).val v) 1 - v 1 = 0
  simp [upper,Matrix.mulVec,dotProduct,Fin.sum_univ_two]

section Representations
variable {M N : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [AddCommGroup N] [Module (ZMod 2) N]

theorem invariant_of_upper_weyl (ρ : Representation (ZMod 2) SL M)
    (A : Submodule (ZMod 2) M)
    (hupper : ∀ t v, v ∈ A → ρ (upper t) v ∈ A)
    (hweyl : ∀ v, v ∈ A → ρ weyl v ∈ A) :
    ∀ g v, v ∈ A → ρ g v ∈ A := by
  intro g
  apply upper_weyl_induction (fun a => ∀ v, v ∈ A → ρ a v ∈ A) hupper hweyl ?_ g
  intro a b ha hb v hv
  rw [map_mul,Module.End.mul_apply]
  exact ha _ (hb v hv)

theorem equivariant_of_upper_weyl (ρ : Representation (ZMod 2) SL M)
    (τ : Representation (ZMod 2) SL N) (f : M →ₗ[ZMod 2] N)
    (hupper : ∀ t v, f (ρ (upper t) v) = τ (upper t) (f v))
    (hweyl : ∀ v, f (ρ weyl v) = τ weyl (f v)) :
    ∀ g v, f (ρ g v) = τ g (f v) := by
  intro g
  apply upper_weyl_induction (fun a => ∀ v, f (ρ a v) = τ a (f v)) hupper hweyl ?_ g
  intro a b ha hb v
  rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,ha,hb]
end Representations

end Representation.SL2FourNatural.ProjectiveRecognition
