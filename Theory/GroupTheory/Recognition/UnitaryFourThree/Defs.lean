module

public import Theory.GroupTheory.PResidual.Defs
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# The involution-centralizer configuration of type U₄(3)

These are Hypothesis 45.1 and the definition on printed p.244 of
Aschbacher, *Sporadic Groups* (Cambridge, 1994), §45, pp.242–249
(PDF spreads 127–130 in the local copy). The residual is O²(H), and
Q is O₂(O²(H)). In particular neither operation is interchangeable
with the other. The two factors are actual SL₂(3) groups, normal
inside O²(H), with intersection the specified central involution.

Right conjugation agrees with the source. The type condition quantifies
over the conjugates of z in Q outside ⟨z⟩. No recognition theorem or
isomorphism with U₄(3) is assumed in these definitions.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
open Subgroup
variable {G : Type*} [Group G]

def centralizer (z : G) : Subgroup G := Subgroup.centralizer {z}

def residual (z : G) : Subgroup G :=
  (pResidual 2 (centralizer z)).map (centralizer z).subtype

def core (z : G) : Subgroup G := (residual z).pCoreIn 2

def conjugate (Q : Subgroup G) (g : G) : Subgroup G :=
  Q.map (MulAut.conj g⁻¹).toMonoidHom

/-- The original centralizer hypothesis, before the two extra type conditions. -/
structure CentralizerHypothesis (z : G) : Prop where
  involution : orderOf z = 2
  factors : ∃ H₁ H₂ : Subgroup G,
    H₁ ⊔ H₂ = residual z ∧
    (H₁.subgroupOf (residual z)).Normal ∧
    (H₂.subgroupOf (residual z)).Normal ∧
    Nonempty (H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    Nonempty (H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
    H₁ ⊓ H₂ = zpowers z
  generalizedFitting_eq :
    (generalizedFitting (centralizer z)).map (centralizer z).subtype = core z
  fused : ∃ g : G, g⁻¹ * z * g ∈ core z ∧ g⁻¹ * z * g ∉ zpowers z

/-- Type U₄(3), as defined on p.244; this is an input to 45.11, not its conclusion. -/
structure IsType (z : G) : Prop extends CentralizerHypothesis z where
  intersection_card : ∀ g : G,
    g⁻¹ * z * g ∈ core z → g⁻¹ * z * g ∉ zpowers z →
    Nat.card (core z ⊓ conjugate (core z) g : Subgroup G) = 4
  centralizer_card : Nat.card (centralizer z) = 2 ^ 7 * 3 ^ 2

end Theory.GroupTheory.Recognition.UnitaryFourThree
end
