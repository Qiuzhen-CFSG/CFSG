module
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.FieldTheory.BinaryTorusInvolution

/-!
# Small invariant subsets for the natural unitary torus

In the natural ternary action, the outer coordinate weights range over the
whole multiplicative field, while the middle weight has image of order q+1.
Thus any torus orbit of a nonzero vector has more than q elements. This excludes
the q-element root-center subspaces occurring in the degree-6n configuration
of a binary unitary hexagon, without character or semisimplicity arguments.

Source: Fong--Seitz I (6D), printed pp.42--43, and the equality case in (4D),
printed pp.22--23; the literal matrix torus is Huppert II.10.12.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace Representation.SU3.NaturalTorus
variable {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])

omit [Finite F] in
private theorem torus_apply (k : Fˣ) (v : Fin 3 → F) :
    Matrix.mulVec (hermitianTorusSU J hJ k).val.val v =
    ![(J.conj (k : F))⁻¹*v 0, (J.conj (k : F)*(k : F)⁻¹)*v 1, (k : F)*v 2] := by
  ext i
  fin_cases i <;> simp [hermitianTorusSU, hermitianTorusGL, hermitianTorusMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem weight_range_le (W : Set (Fin 3 → F)) (v : Fin 3 → F)
    (hW : ∀ k : Fˣ, Matrix.mulVec (hermitianTorusSU J hJ k).val.val v ∈ W)
    (i : Fin 3) (hv : v i ≠ 0) (f : Fˣ →* Fˣ)
    (hf : ∀ k : Fˣ, (Matrix.mulVec (hermitianTorusSU J hJ k).val.val v) i =
      (f k : F)*v i) : Nat.card f.range ≤ Nat.card W := by
  classical
  let k (z : f.range) : Fˣ := Classical.choose z.property
  have hk (z : f.range) : f (k z) = z.val := Classical.choose_spec z.property
  let g : f.range → W := fun z => ⟨Matrix.mulVec (hermitianTorusSU J hJ (k z)).val.val v,hW _⟩
  apply Nat.card_le_card_of_injective g
  intro z w he
  apply Subtype.ext
  apply Units.ext
  have hc := congrArg (fun a : W => a.val i) he
  change (Matrix.mulVec (hermitianTorusSU J hJ (k z)).val.val v) i =
    (Matrix.mulVec (hermitianTorusSU J hJ (k w)).val.val v) i at hc
  rw [hf,hf,hk,hk] at hc
  exact mul_right_cancel₀ hv hc

/-- A nonzero vector has more than fixed-field order many images under the
full special-unitary torus. Any invariant set containing it is therefore too large
for the q-element root-center subspaces in Fong--Seitz (6D). -/
theorem card_lt_of_nonzero_orbit {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = (2^n)^2) (hconj : ∀ x, J.conj x=x^(2^n))
    (W : Set (Fin 3 → F)) (v : Fin 3 → F) (hv : v ≠ 0)
    (hW : ∀ k : Fˣ, Matrix.mulVec (hermitianTorusSU J hJ k).val.val v ∈ W) :
    2^n < Nat.card W := by
  have hq : 2 < (2:ℕ)^n := (by decide : 2 < (2:ℕ)^2).trans_le
    (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  fin_cases i
  · let f : Fˣ →* Fˣ := invMonoidHom.comp (Units.map J.conj.toMonoidHom)
    have hs : Function.Surjective f := by
      intro z
      refine ⟨Units.map J.conj.toMonoidHom z⁻¹,?_⟩
      apply Units.ext
      simpa [f] using J.conj_involutive (z : F)
    have hb := weight_range_le J hJ W v hW 0 hi f (by
      intro k; simp [torus_apply,f])
    rw [MonoidHom.range_eq_top.mpr hs,Nat.card_congr (Subgroup.topEquiv).toEquiv,
      Nat.card_units,hcard] at hb
    have hh : 2^n < (2^n)^2-1 := by
      have hsub : (2^n)^2-1+1=(2^n)^2 := Nat.sub_add_cancel (one_le_pow₀ (by omega : 1 ≤ (2:ℕ)^n))
      nlinarith
    exact hh.trans_le hb
  · let f := FiniteField.BinaryTorusInvolution.displacement J.conj
    have hb := weight_range_le J hJ W v hW 1 hi f (by
      intro k; simp [torus_apply,f,FiniteField.BinaryTorusInvolution.displacement])
    rw [FiniteField.BinaryTorusInvolution.card_displacement J.conj (by omega)
      (by simpa only [pow_mul,Nat.mul_comm 2 n] using hcard) hconj] at hb
    omega
  · have hb := weight_range_le J hJ W v hW 2 hi (MonoidHom.id Fˣ) (by
      intro k; rw [torus_apply]; rfl)
    rw [MonoidHom.range_eq_top.mpr Function.surjective_id,
      Nat.card_congr (Subgroup.topEquiv).toEquiv,Nat.card_units,hcard] at hb
    have hh : 2^n < (2^n)^2-1 := by
      have hsub : (2^n)^2-1+1=(2^n)^2 := Nat.sub_add_cancel (one_le_pow₀ (by omega : 1 ≤ (2:ℕ)^n))
      nlinarith
    exact hh.trans_le hb
end Representation.SU3.NaturalTorus
