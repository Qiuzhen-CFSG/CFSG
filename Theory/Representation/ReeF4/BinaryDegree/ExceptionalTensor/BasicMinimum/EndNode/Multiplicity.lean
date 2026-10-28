module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortA2
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.WeightShift
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.RankOneCoefficients

/-!
# Short A2 multiplicity from two rank-one coefficient identities

The lowering operators are first coefficients of the actual rational root
action. Their mixed commutation and full coroot weight shifts are proved in
the imported modules. Raising at node 3 detects `f₂ f₃ v` and annihilates
`f₃ f₂ v`; raising at node 2 shows that the latter vector is nonzero.
Their independence gives dimension at least two in the full zero weight space.

The rank-one highest-string coefficient formula at exponents one and two is
proved from the rational root action in `RankOneCoefficients`. Discharging that
input gives the multiplicity bound from the short A2 highest vector alone.
Constructing that vector from the original F4 highest weight is a separate
geometric step.

Source: GLS3, Sections 1.12 and 1.14, for the two adjacent short simple roots;
this is the multiplicity step towards the 26-dimensional bound used in
Aschbacher--Smith, Quasithin, printed p.356 (PDF p.367).
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]


theorem lowerings_independent
    (B : AlgebraicFactor F) (hcoeff : RankOneHighestCoefficient B)
    (v : B.Space) (hv : IsShortA2HighestVector B v) :
    LinearIndependent F ![lowering B 2 (lowering B 3 v), lowering B 3 (lowering B 2 v)] := by
  have hweight := (mem_corootWeightSpace B _ v).mp hv.2.1
  have h2 : raising B 2 (lowering B 2 v) = v := by
    have h := hcoeff 2 (Or.inl rfl) 1 (Or.inl rfl) v hv.2.2.1 (by
      intro t
      simpa [shortA2Weight] using hweight 2 t)
    simpa using h
  have h3 : raising B 3 (lowering B 3 v) = v := by
    have h := hcoeff 3 (Or.inr rfl) 1 (Or.inl rfl) v hv.2.2.2 (by
      intro t
      simpa [shortA2Weight] using hweight 3 t)
    simpa using h
  have hf2 : lowering B 2 v ≠ 0 := fun hz => hv.1 (by
    simpa only [hz, map_zero] using h2.symm)
  have hf3 : lowering B 3 v ≠ 0 := fun hz => hv.1 (by
    simpa only [hz, map_zero] using h3.symm)
  have hleft : raising B 3 (lowering B 2 (lowering B 3 v)) = lowering B 2 v := by
    have h := congrArg (fun L : Module.End F B.Space => L (lowering B 3 v))
      (raising_commute_lowering B 3 2 (by decide))
    simpa only [Module.End.mul_apply, h3] using h
  have hright2 : raising B 2 (lowering B 3 (lowering B 2 v)) = lowering B 3 v := by
    have h := congrArg (fun L : Module.End F B.Space => L (lowering B 2 v))
      (raising_commute_lowering B 2 3 (by decide))
    simpa only [Module.End.mul_apply, h2] using h
  have hright3 : raising B 3 (lowering B 3 (lowering B 2 v)) = 0 := by
    have h := hcoeff 3 (Or.inr rfl) 2 (Or.inr rfl) (lowering B 2 v)
      (lowering_fixed_of_fixed B 3 2 (by decide) v hv.2.2.2) (by
        intro t
        have hw := (mem_corootWeightSpace B _ _).mp
          (lowering_mem_corootWeightSpace B 2 _ v hv.2.1) 3 t
        simpa [shortA2Weight, typeF4CartanMatrix] using hw)
    have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
    simpa only [Nat.cast_ofNat, htwo, zero_smul] using h
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    change lowering B 3 (lowering B 2 v) = 0 at hz
    exact hf3 (by simpa only [hz, map_zero] using hright2.symm)
  · intro c hc
    have h := congrArg (raising B 3) hc
    exact hf2 (by simpa only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, map_smul, hright3, smul_zero, hleft] using h.symm)

/-- Dimension counting with the rank-one highest-string coefficient made explicit. -/
theorem zero_weight_finrank_ge_two_of_rankOne
    (B : AlgebraicFactor F) (hcoeff : RankOneHighestCoefficient B)
    (hv : HasShortA2HighestVector B) : 2 ≤ Module.finrank F (corootWeightSpace B 0) := by
  obtain ⟨v, hv⟩ := hv
  obtain ⟨hleft, hright⟩ := lowerings_mem_zero B v hv.2.1
  let w : Fin 2 → corootWeightSpace B 0 :=
    ![⟨lowering B 2 (lowering B 3 v), hleft⟩, ⟨lowering B 3 (lowering B 2 v), hright⟩]
  have hw : LinearIndependent F w := by
    apply LinearIndependent.of_comp (corootWeightSpace B 0).subtype
    convert lowerings_independent B hcoeff v hv using 1
    funext i
    fin_cases i <;> rfl
  simpa using hw.fintype_card_le_finrank

/-- A short A2 highest vector supplies two independent vectors in the full
four-coroot zero weight space, over any algebraically closed field of characteristic two. -/
theorem zero_weight_finrank_ge_two
    (B : AlgebraicFactor F) (hv : HasShortA2HighestVector B) :
    2 ≤ Module.finrank F (corootWeightSpace B 0) :=
  zero_weight_finrank_ge_two_of_rankOne B (rankOneHighestCoefficient B) hv

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
