module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms.Coefficients
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms.InitialBasis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.NormalForms.SylowFixedSpace
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction

/-!
# Janko's four normal forms for the actual binary complement action

The S4 relations determine the parameter matrix for `a`. The actual Sylow
center forces the common fixed space of `a,b,d` to be the first coordinate
line. These conditions leave five parameter tuples. Four are the published
coordinate cases, and the fifth becomes Case III by replacing the second
basis vector by the product of the first two. All changes of coordinates
preserve the original actor labels.

Source: Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 1, printed p.2,
DOI 10.1016/0021-8693(68)90002-1.

`InitialBasis` constructs the initial adapted basis from the fixed/moved
decomposition for the cubic and the distinguished central involution.
`binaryAction_jankoCoordinates` combines that construction with the actual
Sylow-center condition, proving all four alternatives for `LocalData`
without additional premises. The ambient exclusions of Cases III and IV
belong to the subsequent recognition argument.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy

private def parameterTuples : Finset (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2) :=
  {(0,1,1,0), (1,1,1,0), (1,0,0,1), (1,0,1,0), (1,0,1,1)}

private theorem parameter_cases : ∀ α β γ δ : ZMod 2, β * δ = 0 →
    (∀ v : BinaryFour,
      jankoParameterA α β γ δ v = v ∧
        jankoSourceC (jankoParameterA α β γ δ (jankoSourceC (jankoSourceC v))) = v ∧
        jankoParameterD α v = v → v = 1 ∨ v = jankoUnit 0) →
    (α,β,γ,δ) ∈ parameterTuples := by
  decide +kernel

private def changeSecond : BinaryFour ≃* BinaryFour where
  toFun v := Multiplicative.ofAdd ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 2, v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![v.toAdd 0 + v.toAdd 1, v.toAdd 1, v.toAdd 2, v.toAdd 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_mul' := by decide +kernel

private theorem coordinate_cases (α β γ δ : ZMod 2)
    (h : (α,β,γ,δ) ∈ parameterTuples) :
    ∃ k : JankoCase, ∃ e : BinaryFour ≃* BinaryFour,
      (∀ v, jankoParameterA α β γ δ (e v) = e (jankoSourceA k v)) ∧
      (∀ v, jankoSourceC (e v) = e (jankoSourceC v)) ∧
      (∀ v, jankoParameterD α (e v) = e (jankoSourceD k v)) := by
  simp only [parameterTuples, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩ |
    ⟨rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl⟩
  · exact ⟨.one, MulEquiv.refl _, by decide +kernel⟩
  · exact ⟨.two, MulEquiv.refl _, by decide +kernel⟩
  · exact ⟨.three, MulEquiv.refl _, by decide +kernel⟩
  · exact ⟨.four, MulEquiv.refl _, by decide +kernel⟩
  · exact ⟨.three, changeSecond, by decide +kernel⟩

/-- An adapted basis and the actual Sylow-center condition imply all four
source normal forms, including the fifth-tuple change of basis. -/
public theorem jankoCoordinates_of_adaptedBasis
    {ρ : SymmetricFour →* MulAut BinaryFour} (R : JankoAdaptedBasis ρ)
    (hc : ∀ P : Sylow 2 (BinaryFour ⋊[ρ] SymmetricFour), Nat.card (Subgroup.center P) = 2) :
    ∃ k : JankoCase, Nonempty (JankoCoordinates ρ k) := by
  obtain ⟨β,γ,δ,hβδ,ha⟩ := R.parameters
  have hc_left (v) : ρ jankoC (R.basis v) = R.basis (jankoSourceC (jankoSourceC v)) := by
    have hh : jankoC = jankoC⁻¹ * jankoC⁻¹ := by decide +kernel
    rw [hh, map_mul, MulAut.mul_apply, R.action_c, R.action_c]
  have hb (v) : ρ jankoB (R.basis v) =
      R.basis (jankoSourceC (jankoParameterA R.alpha β γ δ (jankoSourceC (jankoSourceC v)))) := by
    simp only [jankoB, map_mul, MulAut.mul_apply, hc_left, ha, R.action_c]
  have hz : ρ jankoA (R.basis (jankoUnit 0)) = R.basis (jankoUnit 0) ∧
      ρ jankoB (R.basis (jankoUnit 0)) = R.basis (jankoUnit 0) ∧
      ρ jankoD (R.basis (jankoUnit 0)) = R.basis (jankoUnit 0) := by
    have hC : jankoSourceC (jankoUnit 0) = jankoUnit 0 := by decide +kernel
    have hD : ∀ α, jankoParameterD α (jankoUnit 0) = jankoUnit 0 := by decide +kernel
    refine ⟨R.fixed_a, ?_, ?_⟩
    · simp only [jankoB, map_mul, MulAut.mul_apply, hc_left, hC, R.fixed_a, R.action_c]
    · rw [R.action_d, hD]
  have hz1 : R.basis (jankoUnit 0) ≠ 1 := by
    intro h
    have he : jankoUnit 0 = 1 := R.basis.injective (h.trans R.basis.map_one.symm)
    exact (by decide +kernel : jankoUnit 0 ≠ 1) he
  have hfixed (v : BinaryFour)
      (hv : jankoParameterA R.alpha β γ δ v = v ∧
        jankoSourceC (jankoParameterA R.alpha β γ δ (jankoSourceC (jankoSourceC v))) = v ∧
        jankoParameterD R.alpha v = v) : v = 1 ∨ v = jankoUnit 0 := by
    have hv' : ρ jankoA (R.basis v) = R.basis v ∧
        ρ jankoB (R.basis v) = R.basis v ∧ ρ jankoD (R.basis v) = R.basis v := by
      rw [ha, hb, R.action_d, hv.1, hv.2.1, hv.2.2]
      exact ⟨rfl,rfl,rfl⟩
    rcases jankoSylow_fixed_eq_one_or ρ hc _ hz hz1 _ hv' with h | h
    · exact Or.inl (R.basis.injective (h.trans R.basis.map_one.symm))
    · exact Or.inr (R.basis.injective h)
  obtain ⟨k,e,heA,heC,heD⟩ := coordinate_cases R.alpha β γ δ
    (parameter_cases R.alpha β γ δ hβδ hfixed)
  refine ⟨k, ⟨{ basis := e.trans R.basis, action_a := ?_, action_c := ?_, action_d := ?_ }⟩⟩
  · intro v
    change ρ jankoA (R.basis (e v)) = R.basis (e (jankoSourceA k v))
    rw [ha, heA]
  · intro v
    change ρ jankoC⁻¹ (R.basis (e v)) = R.basis (e (jankoSourceC v))
    rw [R.action_c, heC]
  · intro v
    change ρ jankoD (R.basis (e v)) = R.basis (e (jankoSourceD k v))
    rw [R.action_d, heD]

/-- Application to the literal action of the supplied complement.
Only the initial adapted-basis construction remains as an explicit premise. -/
public theorem binaryAction_jankoCoordinates_of_adaptedBasis
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)
    (R : JankoAdaptedBasis (D.binaryAction K hK)) :
    ∃ k : JankoCase, Nonempty (JankoCoordinates (D.binaryAction K hK) k) :=
  jankoCoordinates_of_adaptedBasis R (D.binarySemidirect_sylow_center_card K hK)

/-- Janko's four local normal forms for the literal binary complement action.
The initial basis and the Sylow-center condition both follow from `LocalData`.
The basis respects the fixed actors and the source's right-conjugation convention. -/
public theorem binaryAction_jankoCoordinates
    {G : Type*} [Group G] [Finite G] (D : LocalData G)
    (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K) :
    ∃ k : JankoCase, Nonempty (JankoCoordinates (D.binaryAction K hK) k) := by
  obtain ⟨R⟩ := binaryAction_adaptedBasis D K hK
  exact binaryAction_jankoCoordinates_of_adaptedBasis D K hK R

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
