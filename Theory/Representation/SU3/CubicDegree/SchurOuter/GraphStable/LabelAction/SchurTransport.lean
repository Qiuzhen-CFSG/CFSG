module

public import Theory.Representation.BinaryOffender.SchurNormalizerAction
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent

/-!
# Covariance of the actual Schur-linear actor after scalar extension

A literal square-one normalizer operator that commutes with the component
Schur field extends to an involutory linear equivalence of the absolute space.
Its original covariance equation is preserved, even when the component
representation has central kernel. In particular the absolute character is
invariant under any automorphism inducing that same conjugation on the image.

Source: GM04, §3.5 and Proposition 4.11, internal pp.31--32.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender Representation.FrobeniusTensor
open SchurNormalizer
namespace Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) G V) [σ.IsIrreducible]

/-- The scalar extension of the literal Schur-linear actor intertwines the
absolute component action and the action pulled back by its lifted automorphism. -/
def absoluteActorEquiv (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hl : IsSchurLinear σ t) (β : MulAut G)
    (hβ : ∀ g, actionHom σ (β g) =
      (actionImage σ).normalizerMonoidHom t (actionHom σ g)) :
    (absoluteRep σ).Equiv ((absoluteRep σ).comp β.toMonoidHom) := by
  let T := absoluteActor σ (Closure σ) t hl
  have hT : T * T = 1 := absoluteActor_square σ (Closure σ) t hl ht
  refine .mk (LinearEquiv.ofInvolutive T (fun v => LinearMap.congr_fun hT v)) ?_
  intro g
  change T * absoluteRep σ g = absoluteRep σ (β g) * T
  have hc : t.val.val * σ g = σ (β g) * t.val.val := by
    have hh := congrArg (fun x : actionImage σ => x.val.val) (hβ g)
    change σ (β g) = t.val.val * σ g * (↑t.val⁻¹ : Module.End (ZMod 2) V) at hh
    rw [hh]
    simp only [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hs : schurActor σ t hl * σ.endFieldRep g =
      σ.endFieldRep (β g) * schurActor σ t hl := by
    ext v
    apply σ.asModuleEquiv.injective
    exact LinearMap.congr_fun hc (σ.asModuleEquiv v)
  change (schurActor σ t hl).baseChange (Closure σ) *
      (σ.endFieldRep g).baseChange (Closure σ) =
    (σ.endFieldRep (β g)).baseChange (Closure σ) *
      (schurActor σ t hl).baseChange (Closure σ)
  rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, hs]

/-- The lifted automorphism fixes the actual absolute character. -/
theorem absolute_character_lift (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hl : IsSchurLinear σ t) (β : MulAut G)
    (hβ : ∀ g, actionHom σ (β g) =
      (actionImage σ).normalizerMonoidHom t (actionHom σ g)) (g : G) :
    (absoluteRep σ).character (β g) = (absoluteRep σ).character g :=
  (congrFun (char_iso (absoluteActorEquiv σ t ht hl β hβ)) g).symm

end Representation.SU3.CubicDegree.SchurOuter.GraphStable.LabelAction
