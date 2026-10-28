module

public import Theory.GroupTheory.CoprimePrimeFusion
public import Theory.GroupTheory.PrimePowerDecomposition
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order360
public import GorensteinWalter.Classification

/-!
# Involution fusion above the two simple dihedral-eight quotient models

An odd kernel preserves involution orders. In a finite PSL2 quotient the
images are conjugate, and coprime prime-order fusion lifts their conjugacy
to the original group. The concrete PSL2(9)–A6 equivalence gives the same
conclusion for the A6 quotient.

The cubic-kernel wrapper retains the original surjection and the original
two involutions. It supplies the exact quotient-fusion implication needed
after the four-model classification, without assuming any source fusion.
-/

noncomputable section
namespace Theory.GroupTheory.DihedralEightCentralizer

/-- Any two involutions above a finite PSL2 quotient are conjugate when the
surjection has odd kernel. -/
public theorem involutions_isConj_of_psl2_quotient
    {G X F : Type*} [Group G] [Finite G] [Group X] [Field F] [Finite F]
    (f : G →* X) (hf : Function.Surjective f)
    (hker : Nat.Coprime 2 (Nat.card f.ker))
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have horder (a : G) (ha : orderOf a = 2) : orderOf (f a) = 2 := by
    apply (f.orderOf_eq_of_prime_power_of_coprime_ker hker a ?_).trans ha
    exact ⟨1, by simpa only [pow_one, ha] using pow_orderOf_eq_one a⟩
  apply f.isConj_of_map_isConj_of_prime_order_of_coprime_ker hf hker hx hy
  have hc := Theory.PSL2.involutions_isConj (e (f x)) (e (f y))
    ((e.orderOf_eq _).trans (horder x hx)) ((e.orderOf_eq _).trans (horder y hy))
  have hh := e.symm.toMonoidHom.map_isConj hc
  change IsConj (e.symm (e (f x))) (e.symm (e (f y))) at hh
  simpa only [e.symm_apply_apply] using hh

/-- A cubic-kernel cover of PSL2(7) or A6 has one involution class in the
original group. The quotient model is the only model input. -/
public theorem involutions_isConj_of_cubic_kernel_seven_or_six
    {G X : Type*} [Group G] [Finite G] [Group X]
    (f : G →* X) (hf : Function.Surjective f) (hker : Nat.card f.ker = 3)
    (hmodel : Nonempty (X ≃* GorensteinWalter.PSL2 (ZMod 7)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)))
    {x y : G} (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y := by
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by rw [hker]; decide
  rcases hmodel with hseven | hsix
  · let : Fact (Nat.Prime 7) := ⟨by decide⟩
    exact involutions_isConj_of_psl2_quotient (G := G) (X := X) (F := ZMod 7)
      f hf hcop hseven.some hx hy
  · exact involutions_isConj_of_psl2_quotient (G := G) (X := X) (F := Atlas.Comparisons.Exceptional.Nine.F)
      f hf hcop (hsix.some.trans Atlas.Comparisons.Exceptional.psl2NineCoordinatesEquivAlt6.symm) hx hy

end Theory.GroupTheory.DihedralEightCentralizer
