module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms.AdaptedBasis
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Determining the remaining matrix from the S4 relations

After the cubic and reflection are normalized, commutation with the reflection
forces the shape of three columns of the double transposition. The involution
and Klein-four relations then determine Janko's parameters. Only the remaining
256 binary combinations are kernel checked; arbitrary automorphisms are not
enumerated. The column reconstruction proves that this check covers the actual
action in the supplied basis, with the original actor labels.

Source: Janko, J. Algebra 9 (1968), Section 1, printed p.2,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

private def columnHom (w x y z : BinaryFour) : BinaryFour →* BinaryFour where
  toFun v := Multiplicative.ofAdd (fun i =>
    (v.toAdd 0) * w.toAdd i + (v.toAdd 1) * x.toAdd i +
      (v.toAdd 2) * y.toAdd i + (v.toAdd 3) * z.toAdd i)
  map_one' := by ext i; simp
  map_mul' v v' := by
    ext i
    change ((v.toAdd 0 + v'.toAdd 0) * w.toAdd i +
      (v.toAdd 1 + v'.toAdd 1) * x.toAdd i +
      (v.toAdd 2 + v'.toAdd 2) * y.toAdd i +
      (v.toAdd 3 + v'.toAdd 3) * z.toAdd i) =
      (v.toAdd 0 * w.toAdd i + v.toAdd 1 * x.toAdd i +
        v.toAdd 2 * y.toAdd i + v.toAdd 3 * z.toAdd i) +
      (v'.toAdd 0 * w.toAdd i + v'.toAdd 1 * x.toAdd i +
        v'.toAdd 2 * y.toAdd i + v'.toAdd 3 * z.toAdd i)
    ring

private theorem columnHom_e (w x y z : BinaryFour) :
    columnHom w x y z (jankoUnit 0) = w ∧ columnHom w x y z (jankoUnit 1) = x ∧
    columnHom w x y z (jankoUnit 2) = y ∧ columnHom w x y z (jankoUnit 3) = z := by
  simp [columnHom, jankoUnit]

private theorem word : ∀ v : BinaryFour, v =
    (jankoUnit 0) ^ (v.toAdd 0).val * (jankoUnit 1) ^ (v.toAdd 1).val *
    (jankoUnit 2) ^ (v.toAdd 2).val * (jankoUnit 3) ^ (v.toAdd 3).val := by decide +kernel

private theorem ext_basis (f g : BinaryFour →* BinaryFour) (h : ∀ i, f (jankoUnit i) = g (jankoUnit i)) : f = g := by
  apply MonoidHom.ext
  intro v
  conv_lhs => rw [word v]
  conv_rhs => rw [word v]
  simp only [map_mul, map_pow, h]

private theorem eq_columnHom (f : BinaryFour →* BinaryFour) :
    f = columnHom (f (jankoUnit 0)) (f (jankoUnit 1)) (f (jankoUnit 2)) (f (jankoUnit 3)) := by
  apply ext_basis
  intro i
  fin_cases i <;> simp [columnHom, jankoUnit]

private def reducedA (α p q β γ δ ε τ : ZMod 2) : BinaryFour →* BinaryFour :=
  columnHom (jankoUnit 0) (Multiplicative.ofAdd ![p,q,β,0])
    (Multiplicative.ofAdd ![α*δ,0,τ,0]) (Multiplicative.ofAdd ![γ,δ,ε,τ])

private theorem commuting_shape (f : BinaryFour →* BinaryFour) (α : ZMod 2)
    (hfix : f (jankoUnit 0) = jankoUnit 0) (hcomm : ∀ v, f (jankoParameterD α v) = jankoParameterD α (f v)) :
    ∃ p q β γ δ ε τ, f = reducedA α p q β γ δ ε τ := by
  let x := f (jankoUnit 1)
  let y := f (jankoUnit 2)
  let z := f (jankoUnit 3)
  have hf : f = columnHom (jankoUnit 0) x y z := by
    simpa only [hfix] using eq_columnHom f
  have hx3 : x.toAdd 3 = 0 := by
    have h := congrArg (fun v : BinaryFour => v.toAdd 2) (hcomm (jankoUnit 1))
    simp [hf, columnHom, jankoUnit, jankoParameterD, Pi.single_apply] at h
    exact h
  have hy : y = Multiplicative.ofAdd ![α * z.toAdd 1, 0, z.toAdd 3, 0] := by
    have h := hcomm (jankoUnit 3)
    rw [hf] at h
    ext i
    have hi := congrArg (fun v : BinaryFour => v.toAdd i) h
    fin_cases i <;> simp [columnHom, jankoUnit, jankoParameterD, Pi.single_apply] at hi ⊢
    all_goals linear_combination hi
  refine ⟨x.toAdd 0, x.toAdd 1, x.toAdd 2, z.toAdd 0, z.toAdd 1,
    z.toAdd 2, z.toAdd 3, ?_⟩
  rw [hf, hy]
  congr 1
  · ext i; fin_cases i <;> simp [hx3]
  · ext i; fin_cases i <;> rfl

private def rel (A : BinaryFour →* BinaryFour) : Prop :=
  let C := jankoSourceC
  let B := fun v => C (A (C (C v)))
  (∀ i, A (A (jankoUnit i)) = jankoUnit i) ∧
  (∀ i, A (B (jankoUnit i)) = B (A (jankoUnit i))) ∧
  (∀ i, C (B (C (C (jankoUnit i)))) = A (B (jankoUnit i)))

private instance (A : BinaryFour →* BinaryFour) : Decidable (rel A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem reduced_test : ∀ α p q β γ δ ε τ,
    rel (reducedA α p q β γ δ ε τ) →
      q = 1 ∧ τ = 1 ∧ ε = 0 ∧ p = β * γ ∧ β * δ = 0 := by
  unfold rel
  decide +kernel


/-- The S4 relations force exactly the source's four-parameter matrix in
any adapted basis. No matrix catalogue or parameter hypothesis is assumed. -/
public theorem JankoAdaptedBasis.parameters
    {ρ : SymmetricFour →* MulAut BinaryFour} (R : JankoAdaptedBasis ρ) :
    ∃ β γ δ : ZMod 2, β * δ = 0 ∧
      ∀ v, ρ jankoA (R.basis v) = R.basis (jankoParameterA R.alpha β γ δ v) := by
  let σ : SymmetricFour →* MulAut BinaryFour :=
    (MulAut.congr R.basis.symm).toMonoidHom.comp ρ
  let f : BinaryFour →* BinaryFour := (σ jankoA).toMonoidHom
  have hc (v) : σ jankoC⁻¹ v = jankoSourceC v := by
    change R.basis.symm (ρ jankoC⁻¹ (R.basis v)) = _
    rw [R.action_c, MulEquiv.symm_apply_apply]
  have hc' (v) : σ jankoC v = jankoSourceC (jankoSourceC v) := by
    have hh : jankoC = jankoC⁻¹ * jankoC⁻¹ := by decide +kernel
    rw [hh, map_mul, MulAut.mul_apply, hc, hc]
  have hd (v) : σ jankoD v = jankoParameterD R.alpha v := by
    change R.basis.symm (ρ jankoD (R.basis v)) = _
    rw [R.action_d, MulEquiv.symm_apply_apply]
  have hb (v) : σ jankoB v = jankoSourceC (f (jankoSourceC (jankoSourceC v))) := by
    simp only [jankoB, map_mul, MulAut.mul_apply, hc, hc', f, MulEquiv.coe_toMonoidHom]
  have hfix : f (jankoUnit 0) = jankoUnit 0 := by
    change R.basis.symm (ρ jankoA (R.basis (jankoUnit 0))) = _
    rw [R.fixed_a, MulEquiv.symm_apply_apply]
  have hcomm (v) : f (jankoParameterD R.alpha v) = jankoParameterD R.alpha (f v) := by
    rw [← hd v, ← hd (f v)]
    change σ jankoA (σ jankoD v) = σ jankoD (σ jankoA v)
    have hh : jankoA * jankoD = jankoD * jankoA := by decide +kernel
    rw [← MulAut.mul_apply, ← map_mul, hh, map_mul, MulAut.mul_apply]
  have hr : rel f := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      change σ jankoA (σ jankoA (jankoUnit i)) = jankoUnit i
      have hh : jankoA * jankoA = 1 := by decide +kernel
      rw [← MulAut.mul_apply, ← map_mul, hh, map_one, MulAut.one_apply]
    · intro i
      change f (jankoSourceC (f (jankoSourceC (jankoSourceC (jankoUnit i))))) =
        jankoSourceC (f (jankoSourceC (jankoSourceC (f (jankoUnit i)))))
      rw [← hb, ← hb]
      change σ jankoA (σ jankoB (jankoUnit i)) = σ jankoB (σ jankoA (jankoUnit i))
      have hh : jankoA * jankoB = jankoB * jankoA := by decide +kernel
      rw [← MulAut.mul_apply, ← map_mul, hh, map_mul, MulAut.mul_apply]
    · intro i
      change jankoSourceC
        (jankoSourceC (f (jankoSourceC (jankoSourceC
          (jankoSourceC (jankoSourceC (jankoUnit i))))))) =
        f (jankoSourceC (f (jankoSourceC (jankoSourceC (jankoUnit i)))))
      rw [← hb, ← hb, ← hc', ← hc]
      change σ jankoC⁻¹ (σ jankoB (σ jankoC (jankoUnit i))) =
        σ jankoA (σ jankoB (jankoUnit i))
      have hh : jankoC⁻¹ * jankoB * jankoC = jankoA * jankoB := by decide +kernel
      simp only [← MulAut.mul_apply, ← map_mul, ← mul_assoc, hh]
  obtain ⟨p,q,β,γ,δ,ε,τ,hf⟩ := commuting_shape f R.alpha hfix hcomm
  obtain ⟨hq,hτ,hε,hp,hβδ⟩ := reduced_test R.alpha p q β γ δ ε τ (hf ▸ hr)
  refine ⟨β,γ,δ,hβδ,?_⟩
  intro v
  apply R.basis.symm.injective
  change f v = R.basis.symm (R.basis (jankoParameterA R.alpha β γ δ v))
  rw [MulEquiv.symm_apply_apply, hf, hq, hτ, hε, hp]
  ext i
  fin_cases i <;> simp [reducedA, columnHom, jankoUnit, jankoParameterA] <;> ring

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
