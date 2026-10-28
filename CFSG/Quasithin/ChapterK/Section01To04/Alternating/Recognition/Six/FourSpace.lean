module

public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace.Coordinates
public import Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings

/-!
# Recognition of faithful binary A₆ four-spaces

Choose a linear identification with the actual natural quotient and transport
the faithful image through GL₄(2) ≃ A₈. Every A₆ image there is the even
pointwise stabilizer of a pair, so any two such images are conjugate. Pulling
the conjugator back gives a linear automorphism; the injective actor maps
give the accompanying automorphism of A₆. Their conjugation identity proves
the required intertwining identity on the original vector space.

The argument applies to every faithful four-space. The `fourSpace` endpoint
retains the irreducibility hypothesis of the published input interface.
Source: Aschbacher–Smith, K.1.1, printed p.452 (PDF p.463), citing
Guralnick–Malle (2002), Theorem 6.2 and Table 6.3 for the degree conclusion.
The actual exceptional comparison retains its ATLAS attribution in
`Theory.LinearAlgebra.BinaryFourAlternatingEight` and its imports.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
open ChapterB.QuasisimpleSource Representation.Hexacode.SixDimensional
universe v

/-- Image conjugacy constructs both the actor automorphism and the linear intertwiner. -/
theorem actionEquiv_of_faithful_fourSpace
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 4) :
    Nonempty (ActionEquiv σ (alternatingNatural 6)) := by
  let e₀ : V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
    LinearEquiv.ofFinrankEq _ _ (hd.trans natural_finrank.symm)
  let e := naturalLinearEquivAlternatingEight
  let f := coordinateAction σ e₀
  let g := naturalLinearAction.comp (alternatingGroup (Fin 6)).subtype
  let F := e.toMonoidHom.comp f
  let G := e.toMonoidHom.comp g
  obtain ⟨p, a, ha⟩ :=
    Theory.SpecificGroups.SymmetricEight.AlternatingSixEmbeddings.exists_conjugating_equiv F G
      (e.injective.comp (coordinateAction_injective σ e₀ hf))
      (e.injective.comp natural_alternating_action_injective)
  let c := e.symm p
  have he (x : alternatingGroup (Fin 6)) : c * f x * c⁻¹ = g (a x) := by
    apply e.injective
    simpa [c, F, G] using ha x
  refine ⟨{ groupEquiv := a, linearEquiv := e₀.trans c, intertwines := ?_ }⟩
  intro x v
  have h := LinearEquiv.congr_fun (he x) (c (e₀ v))
  change c (e₀ (σ x (e₀.symm (c.symm (c (e₀ v)))))) =
    alternatingNatural 6 (a x) (c (e₀ v)) at h
  simpa only [LinearEquiv.symm_apply_apply, LinearEquiv.trans_apply] using h

/-- The intrinsic four-space recognition input to the K.1.1 assembly. -/
theorem fourSpace : FourSpace.{v} := by
  intro V _ _ _ σ hf _ hd
  exact actionEquiv_of_faithful_fourSpace σ hf hd

end CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six
