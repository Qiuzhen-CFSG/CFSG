module

public import Theory.AlgebraicGroup.Automorphisms.FiniteKernel
public import Theory.AlgebraicGroup.Automorphisms.Lang.Basic

universe u

/-!
# Commutative Lang surjectivity

This module proves the commutative terminal step in Steinberg's Lang
surjectivity argument.  For a commutative algebraic group, the regular Lang map
`g ↦ g * sigma(g⁻¹)` is itself an algebraic-group endomorphism.  Its abstract
kernel injects into the fixed-point subtype of `sigma`: if
`g * sigma(g⁻¹) = 1`, then `sigma g = g`.

Thus finite fixed points give a finite Lang kernel, and the general
finite-kernel endomorphism theorem for connected algebraic groups makes the
Lang morphism point-surjective.  This is the base case used by the solvable
Lang induction in Steinberg, *Endomorphisms of Linear Algebraic Groups*,
Theorem 10.4.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- In a commutative algebraic group, the Lang map is an algebraic-group
endomorphism. -/
public def commutativeLangMorphism
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism G G where
  toVariety := langMorphism sigma
  map_one := by
    rw [langMorphism_apply]
    simp
  map_mul := by
    intro x y
    rw [langMorphism_apply, langMorphism_apply, langMorphism_apply]
    simp [map_inv, map_mul]
    let hc := isMulCommutative_iff.mp hcomm
    calc
      x * y * ((sigma.onPoints y)⁻¹ * (sigma.onPoints x)⁻¹)
          = x * (y * ((sigma.onPoints y)⁻¹ * (sigma.onPoints x)⁻¹)) := by
            rw [mul_assoc]
      _ = x * ((sigma.onPoints x)⁻¹ * (y * (sigma.onPoints y)⁻¹)) := by
            congr 1
            calc
              y * ((sigma.onPoints y)⁻¹ * (sigma.onPoints x)⁻¹)
                  = (y * (sigma.onPoints y)⁻¹) *
                      (sigma.onPoints x)⁻¹ := by
                    rw [mul_assoc]
              _ = (sigma.onPoints x)⁻¹ *
                    (y * (sigma.onPoints y)⁻¹) := by
                    rw [hc (y * (sigma.onPoints y)⁻¹)
                      (sigma.onPoints x)⁻¹]
      _ = x * (sigma.onPoints x)⁻¹ *
            (y * (sigma.onPoints y)⁻¹) := by
            rw [mul_assoc]

/-- The point map of `commutativeLangMorphism` is the regular Lang map. -/
public theorem commutativeLangMorphism_onPoints_apply
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hcomm : IsMulCommutative (Variety.Point G))
    (g : Variety.Point G) :
    (commutativeLangMorphism sigma hcomm).onPoints g =
      (langMorphism sigma).toFun g := by
  rfl

/-- The kernel of the commutative Lang endomorphism is finite when the
fixed-point subtype of `sigma` is finite. -/
public theorem commutativeLangMorphism_kernel_finite
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hcomm : IsMulCommutative (Variety.Point G))
    (hfixed : Finite {x : Variety.Point G | sigma.onPoints x = x}) :
    Finite (commutativeLangMorphism sigma hcomm).kernel := by
  let kernelToFixed :
      (commutativeLangMorphism sigma hcomm).kernel →
        {x : Variety.Point G | sigma.onPoints x = x} :=
    fun x => ⟨x.1, by
      have hx := x.property
      change (commutativeLangMorphism sigma hcomm).onPoints x.1 = 1 at hx
      have hlang : x.1 * sigma.onPoints x.1⁻¹ = 1 := by
        simpa [commutativeLangMorphism_onPoints_apply,
          langMorphism_apply] using hx
      have hlang' : x.1 * (sigma.onPoints x.1)⁻¹ = 1 := by
        simpa [Morphism.map_inv] using hlang
      have hx_eq : x.1 = sigma.onPoints x.1 := by
        have hmul := congrArg (fun z => z * sigma.onPoints x.1) hlang'
        simpa [mul_assoc] using hmul
      exact hx_eq.symm⟩
  let _ := hfixed
  exact Finite.of_injective kernelToFixed (by
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : {x : Variety.Point G | sigma.onPoints x = x} =>
        (z : Variety.Point G)) hxy)

variable [IsAlgClosed k]

/-- Lang's morphism is point-surjective for connected commutative algebraic
groups with finite fixed-point subtype. -/
public theorem langMorphism_surjective_of_connected_commutative
    {G : Variety k} [AlgebraicGroup G]
    (sigma : AlgebraicGroup.Morphism G G)
    (hG : Variety.IsConnected G)
    (hcomm : IsMulCommutative (Variety.Point G))
    (hfixed : Finite {x : Variety.Point G | sigma.onPoints x = x}) :
    Function.Surjective (langMorphism sigma).toFun := by
  have hsurj :
      Function.Surjective (commutativeLangMorphism sigma hcomm).onPoints :=
    connected_endomorphism_surjective_of_finiteKernel
      (commutativeLangMorphism sigma hcomm) hG
      (commutativeLangMorphism_kernel_finite sigma hcomm hfixed)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, by
    rwa [← commutativeLangMorphism_onPoints_apply sigma hcomm x]⟩

end Theory.AlgebraicGroup
