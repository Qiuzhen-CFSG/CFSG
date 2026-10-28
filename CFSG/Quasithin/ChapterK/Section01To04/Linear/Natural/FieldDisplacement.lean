module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Transport
public import Theory.Representation.FiniteFieldSemilinearDisplacement

/-!
# The source field-involution displacement on the original module

Finite semilinear descent supplies the half-dimension formula for an
involution whose coefficient automorphism has order two. Conjugating by the
actual binary coordinate equivalence and transporting the literal cyclic
fixed quotient gives codimension ns when the field degree is 2s.

This is the single-actor calculation in Aschbacher–Smith, K.3.2.1,
printed p.455, using the constructed descent theorem for H.0.1. It leaves
the coefficient-order identification and the common-fixed-space estimate
for a larger elementary actor to the remaining field-actor calculation.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterK.Linear.Natural
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (F : BinaryField) (n : ℕ)

/-- Descent gives the source half-dimension formula on the original action,
using the actual scalar equation and a nontrivial coefficient involution. -/
theorem field_involution_fixedCodim (E : V ≃ₗ[ZMod 2] (Fin n → F.Carrier))
    (a : G) (ha : orderOf a = 2) (σ : F.Carrier ≃+* F.Carrier) (hσ : orderOf σ = 2)
    (hsemi : ∀ (c : F.Carrier) (v : V),
      E (ρ a (E.symm (c • E v))) = σ c • E (ρ a v))
    (s : ℕ) (hr : F.degree = 2 * s) :
    fixedCodim ρ (Subgroup.zpowers a) = n * s := by
  let τ : Representation (ZMod 2) G (Fin n → F.Carrier) := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : V) : E (ρ g v) = τ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hσ' (c : F.Carrier) (v : Fin n → F.Carrier) : τ a (c • v) = σ c • τ a v := by
    have h := hsemi c (E.symm v)
    rw [E.apply_symm_apply] at h
    exact h
  have ht := FiniteFieldSemilinearDisplacement.fixedCodim_formula τ (by decide : 0 < 2)
    a ha σ hσ hσ'
  rw [field_finrank, hr, Module.finrank_pi, Fintype.card_fin] at ht
  have hc := fixedCodim_map_equivariant ρ τ (MonoidHom.id G) E hτ (Subgroup.zpowers a)
  simp only [Subgroup.map_id] at hc
  rw [← hc] at ht
  nlinarith

end CFSG.Quasithin.ChapterK.Linear.Natural
