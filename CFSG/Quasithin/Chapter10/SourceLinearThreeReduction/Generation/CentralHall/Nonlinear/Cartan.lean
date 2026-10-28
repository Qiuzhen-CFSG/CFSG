module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Branches
public import Theory.Representation.OrthogonalFourMinusRankOne.CartanFixed

/-!
# From actual Cartan coordinates to the literal Hall action image

The coordinates below identify the original two-core quotient of L₀ with
two SL₂ factors and retain the original quotient map from L. The Hall
action is conjugation by the two diagonal characters. Fixing the upper
singular vectors forces both characters into the norm-one subgroups.
Section faithfulness makes these characters injective, and the inverse
of the original action-to-range equivalence gives the requested embedding.

Constructing these coordinates is an outstanding source obligation; no
injectivity or torus embedding is included in their fields. Source:
Aschbacher--Smith, 10.1.2(5) and 10.2.3, printed pp.742,745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
open Chapter3.Section02
open Representation.OrthogonalFourMinus
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} (B : Subgroup H) (hBM : B ≤ D.maximalLocal.subgroupOf H)
  (n : ℕ) [NeZero n]
  (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))

/-- Coordinates for the inner Cartan action after field-factor elimination.
The action and component map are those of the original source setup. -/
structure CartanCoordinates where
  quotientPair : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
    (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
      Matrix.SpecialLinearGroup (Fin 2) (Field n))
  component (l : L) :
    quotientPair (QuotientGroup.mk' (pCore 2 (localOrbit T L))
      ⟨(l : G), le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' (pCore 2 L) l), 1)
  characters : B →* (Field n)ˣ × (Field n)ˣ
  equivariant (b : B) (x : localOrbit T L ⧸ pCore 2 (localOrbit T L)) :
    quotientPair (CentralHall.action D B hBM b x) =
      (CartanFixed.diagonal n (characters b).1,
        CartanFixed.diagonal n (characters b).2) * quotientPair x *
      (CartanFixed.diagonal n (characters b).1,
        CartanFixed.diagonal n (characters b).2)⁻¹
  fixed (b : B) :
    FiniteModel.action n (CartanFixed.diagonal n (characters b).1)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1 ∧
    FiniteModel.action n (CartanFixed.diagonal n (characters b).2)
        (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1

variable {D B hBM n e}

/-- The original section-faithfulness premise makes the Cartan characters faithful. -/
theorem CartanCoordinates.characters_injective
    (p : CartanCoordinates D B hBM n e)
    (hfaith : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥) :
    Function.Injective p.characters := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro b hb
  apply mem_bot.mpr
  apply CentralHall.action_injective D B hBM hfaith
  rw [map_one]
  ext x
  apply p.quotientPair.injective
  have he := p.equivariant b x
  have hd : (CartanFixed.diagonal n (p.characters b).1,
      CartanFixed.diagonal n (p.characters b).2) = 1 := by
    rw [show p.characters b = 1 from hb]
    exact Prod.ext (CartanFixed.diagonal_one n) (CartanFixed.diagonal_one n)
  rw [hd, inv_one, one_mul, mul_one] at he
  exact he

/-- The geometric fixed-vector equations give an embedding of the literal
original action range, with both characters restricted to norm one. -/
theorem CartanCoordinates.image_embedding
    (p : CartanCoordinates D B hBM n e)
    (hfaith : B.map H.subtype ⊓ Chapter4.sectionCentralizer (localOrbit T L) = ⊥) :
    ∃ f : (CentralHall.action D B hBM).range →*
      FiniteField.BinaryNormOne.torus n × FiniteField.BinaryNormOne.torus n,
      Function.Injective f := by
  let r := MonoidHom.ofInjective (CentralHall.action_injective D B hBM hfaith)
  refine ⟨(CartanFixed.pairHom n p.characters p.fixed).comp r.symm.toMonoidHom, ?_⟩
  exact (CartanFixed.pairHom_injective n p.characters p.fixed
    (p.characters_injective hfaith)).comp r.symm.injective

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
