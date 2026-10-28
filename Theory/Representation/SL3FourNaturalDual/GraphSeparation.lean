module

public import Theory.Representation.SL3FourNaturalDual.GraphSum

/-!
# A natural SL₃(4) section is moved by a graph actor

The natural and dual binary modules are not equivalent: the two elementary
matrices in positions (0,1) and (0,2) have the same displacement on the
vector (0,1,1), whereas their dual displacements lie on different coordinate
lines. An injective intertwiner would kill (1,0,0).

Absorbing the actual GL₃ correction in a graph relation therefore shows that
a graph actor cannot stabilize a natural section. This supplies the local
exclusion of F.9.18(4i); no full-module natural-plus-dual identification is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, printed p.955.
-/

@[expose] public noncomputable section
namespace Representation.SL3FourNaturalDual
open Matrix

/-- The natural and dual actions are inequivalent even after restriction to F₂. -/
theorem no_injective_natural_dual_intertwiner (e : W →ₗ[ZMod 2] W)
    (hinj : Function.Injective e)
    (he : ∀ g w, e (natural g w) = dualCoordinates g (e w)) : False := by
  let v : W := ![0, 1, 1]
  let b : W := ![1, 0, 0]
  have hnr : natural (root 1) v - v = b := by
    have h := congrArg Prod.fst (root_displacement 1 (v, 0))
    simpa [representation, Representation.prod, v, b] using h
  have hns : natural (secondRoot 1) v - v = b := by
    have h := congrArg Prod.fst (secondRoot_displacement 1 (v, 0))
    simpa [representation, Representation.prod, v, b] using h
  have hdr : dualCoordinates (root 1) (e v) - e v = ![0, 0, e v 0] := by
    have h := congrArg Prod.snd (root_displacement 1 (0, e v))
    simpa [representation, Representation.prod] using h
  have hds : dualCoordinates (secondRoot 1) (e v) - e v = ![0, e v 0, 0] := by
    have h := congrArg Prod.snd (secondRoot_displacement 1 (0, e v))
    simpa [representation, Representation.prod] using h
  have hr : e b = ![0, 0, e v 0] := by rw [← hnr, map_sub, he, hdr]
  have hs : e b = ![0, e v 0, 0] := by rw [← hns, map_sub, he, hds]
  have hz : e v 0 = 0 := by
    simpa using congrArg (fun w : W => w 2) (hr.symm.trans hs)
  have hb : e b = e 0 := by
    rw [hr, hz, map_zero]
    funext i
    fin_cases i <;> rfl
  have h := congrArg (fun w : W => w 0) (hinj hb)
  exact one_ne_zero h


variable {J U : Type*} [Group J] [AddCommGroup U] [Module (ZMod 2) U]

/-- A graph actor with any GL₃ correction moves every natural internal section. -/
theorem graph_moves_natural_section (ρ : Representation (ZMod 2) J U)
    (a : SL →* J) (t : J) (I : Submodule (ZMod 2) U) (e : I ≃ₗ[ZMod 2] W)
    (c : GeneralLinearGroup (Fin 3) F)
    (he : ∀ g w, ρ (a g) (e.symm w : U) = (e.symm (natural g w) : U))
    (ht : ∀ g, a g * t = t * a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) : I.map (ρ t) ≠ I := by
  intro hstable
  let τ : I ≃ₗ[ZMod 2] I := (translateEquiv ρ t I).trans
    (LinearEquiv.ofEq (I.map (ρ t)) I hstable)
  let s : W ≃ₗ[ZMod 2] W := ((matrixCoordinates c).trans e.symm).trans (τ.trans e)
  have hs (w : W) : (e.symm (s w) : U) = ρ t (e.symm (matrixCoordinates c w) : U) := by
    dsimp only [s, LinearEquiv.trans_apply]
    rw [e.symm_apply_apply]
    rfl
  have hi (g : SL) (w : W) : natural g (s w) = s (dualCoordinates g w) := by
    apply e.symm.injective
    apply Subtype.val_injective
    change (e.symm (natural g (s w)) : U) = (e.symm (s (dualCoordinates g w)) : U)
    rw [← he, hs, hs]
    change (ρ (a g) * ρ t) (e.symm (matrixCoordinates c w) : U) = _
    rw [← map_mul, ht, map_mul]
    change ρ t (ρ (a (PSL3.OuterSolvable.linearConjSL F c
      (SpecialLinearGroup.inverseTranspose g))) (e.symm (matrixCoordinates c w) : U)) = _
    rw [he, natural_linearConj]
    rfl
  apply no_injective_natural_dual_intertwiner s.symm.toLinearMap s.symm.injective
  intro g w
  apply s.injective
  change s (s.symm (natural g w)) = s (dualCoordinates g (s.symm w))
  rw [s.apply_symm_apply, ← hi, s.apply_symm_apply]

end Representation.SL3FourNaturalDual
