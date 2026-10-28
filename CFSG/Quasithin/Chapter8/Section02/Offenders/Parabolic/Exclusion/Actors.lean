module

public import Theory.Representation.BinaryOffender.MinimumActorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# The minimum actor rank in the exceptional code case

The native setwise-pair stabilizer acts on the literal ten-dimensional M₂₂
code and cocode. Its checked involution displacement is at least three,
so every nontrivial elementary actor of ratio at most two has rank at
least two. An equivariant identification transports this assertion to the
actual source action; a group-family label is not enough.

Source: Aschbacher–Smith, Proposition 8.2.2(1), printed p.715, and H.14.4,
printed pp.397–398 (combined manuscript, 1 March 2004).
-/

public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion
open Subgroup Representation.BinaryOffender MathieuCode

/-- The rank bound for the literal setwise-pair action on the code. -/
theorem m22_code_actor_rank (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryTwo A) (hr : actionRatio m22OuterCodeRepresentation A ≤ 2) :
    2 ≤ rank A :=
  rank_ge_two_of_involution_displacement m22OuterCodeRepresentation
    (fun t ht => (m22Outer_involution_displacement_ge_three t ht).1) A hA hr

/-- The same bound for the literal cocode, with its distinct action retained. -/
theorem m22_cocode_actor_rank (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryTwo A) (hr : actionRatio m22OuterCocodeRepresentation A ≤ 2) :
    2 ≤ rank A :=
  rank_ge_two_of_involution_displacement m22OuterCocodeRepresentation
    (fun t ht => (m22Outer_involution_displacement_ge_three t ht).2) A hA hr

/-- Apply the code bound to a marked source representation. In particular
this supplies the minimum quadratic-actor rank required by 3.1.9(6) once
Table B.4.5 gives q = 2. The map and the intertwiner are both explicit. -/
theorem code_actor_rank_of_equivariant
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W)
    (f : D →* m22PairStabilizer) (hf : Function.Injective f)
    (E : W ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ d w, E (ρ d w) = m22OuterCodeRepresentation (f d) (E w))
    (A : Subgroup D) (hA : IsElementaryTwo A) (hr : actionRatio ρ A ≤ 2) :
    2 ≤ rank A := by
  apply rank_ge_two_of_involution_displacement ρ ?_ A hA hr
  intro t ht
  have ho : orderOf (f t) = 2 := (orderOf_injective f hf t).trans ht
  have h := (m22Outer_involution_displacement_ge_three (f t) ho).1
  rw [fixedCodim_map_equivariant ρ m22OuterCodeRepresentation f E hE,
    MonoidHom.map_zpowers]
  exact h

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion
