module
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Scalars
public import Theory.Representation.Triality.BinaryDegree.CarrierTransport.FiniteField
/-!
# Descent of fixed root parameters to the literal cubic coefficient field

A tuple fixed by graph and q-Frobenius has every entry fixed by q^3-Frobenius.
The actual finite-field embedding has exactly that image. Entrywise descent
therefore gives a bijection with the published fixed coordinate tuples,
preserving every coefficient rather than merely their number.
Source: Steinberg 11.8 and 13.3(a).
-/

public noncomputable section
namespace Triality.RestrictedWeights.CoordinateScalars
open Triality.Standard Triality.Standard.PositiveCoordinates
universe u
variable {k:Type u} [Field k]

@[expose] def parameterTwist (n:ℕ) (x:Fin 12→k) : Fin 12→k :=
  fun i=>x (diagram.symm i)^(2^n)

theorem parameterTwist_fixed_iff (n:ℕ) (x:Fin 12→k) :
    parameterTwist n x=x ↔ ∀i,x (diagram i)=x i^(2^n) := by
  constructor
  · intro h i
    simpa only [parameterTwist,Equiv.symm_apply_apply] using (congrFun h (diagram i)).symm
  · intro h
    funext i
    simpa only [parameterTwist,Equiv.apply_symm_apply] using (h (diagram.symm i)).symm

theorem fixed_coordinate_cube (n:ℕ) (x:Fin 12→k)
    (h:parameterTwist n x=x) (i:Fin 12) : x i^(2^(3*n))=x i := by
  have hx:∀i,x (diagram i)=x i^(2^n) := (parameterTwist_fixed_iff n x).mp h
  have hn : 2^(3*n)=(2^n*2^n)*2^n := by
    rw [show 3*n=n+n+n by omega,Nat.pow_add,Nat.pow_add]
  rw [hn,pow_mul,pow_mul,←hx i,←hx (diagram i),←hx (diagram (diagram i)),diagram_three]

@[expose] def embeddedFixedCoordinates {n:ℕ} {hn:0<n}
    (f:ExtensionField (binaryParameters n hn)→+*k) :
    FixedCoordinates (binaryParameters n hn) → {x:Fin 12→k // parameterTwist n x=x} := fun a=>
  ⟨fun i=>f (a.val i),by
    apply (parameterTwist_fixed_iff n _).mpr
    intro i
    rw [(twist_eq_self_iff _ _).mp a.property i,fieldFrobenius_apply,map_pow]
    rfl⟩

theorem embeddedFixedCoordinates_bijective {n:ℕ} {hn:0<n}
    (f:ExtensionField (binaryParameters n hn)→+*k) :
    Function.Bijective (embeddedFixedCoordinates f) := by
  constructor
  · intro a b h
    apply Subtype.ext
    funext i
    apply f.injective
    exact congrFun (congrArg Subtype.val h) i
  · intro x
    have hm (i:Fin 12) : x.val i∈f.range :=
      (BinaryDegree.CarrierTransport.coefficient_mem_range_iff f (x.val i)).mpr
        (fixed_coordinate_cube n x.val x.property i)
    choose a ha using hm
    have hf : twist (binaryParameters n hn) a=a := by
      apply (twist_eq_self_iff _ _).mpr
      intro i
      apply f.injective
      rw [ha,fieldFrobenius_apply,map_pow,ha]
      exact (parameterTwist_fixed_iff n x.val).mp x.property i
    refine ⟨⟨a,hf⟩,?_⟩
    apply Subtype.ext
    funext i
    exact ha i

/-- Fixed cubic-field tuples and fixed algebraically closed tuples have the same literal parameters. -/
@[expose] noncomputable def fixedCoordinatesEquiv {n:ℕ} {hn:0<n}
    (f:ExtensionField (binaryParameters n hn)→+*k) :
    FixedCoordinates (binaryParameters n hn) ≃ {x:Fin 12→k // parameterTwist n x=x} :=
  Equiv.ofBijective (embeddedFixedCoordinates f) (embeddedFixedCoordinates_bijective f)

end Triality.RestrictedWeights.CoordinateScalars
