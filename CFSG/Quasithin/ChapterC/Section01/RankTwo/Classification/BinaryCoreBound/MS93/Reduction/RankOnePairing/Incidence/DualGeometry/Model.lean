module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.DualGeometry.SourceImages

/-!
# The finite matrix obligations for the dual MS93 pencil

These obligations involve only SL₃(2), its marked parabolics, and the
literal eight-element additive module. They are not hypotheses of MS93
(1.7). Their constructor must use the zero fixed-space condition on the
natural module, while the seed and neighboring plane use the dual module.

For the opposite planes the actors are products r*a with r in the
neighboring parabolic and a in the seed parabolic. This factorization is
needed to lift the seed containment literally: a normalizes X, so X^(r*a)
is X^r inside the original neighboring closure. An arbitrary containment
of quotient lines would only give that inclusion modulo the pairing kernel.

Source: Meierfrankenfeld--Stellmacher (1993), proof of (1.7)(ii), p.848.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
open Subgroup FixedGeometry.ValueConstruction

/-- Both modules use the same marking; the quotient action is contragredient. -/
def dualMark (σ : MulAut SL) : MulAut SL :=
  σ.trans BinaryLinearThree.AutomorphismAction.graph

/-- The line fixed by the seed parabolic in the dual module. -/
def seedLine (σ : MulAut SL) (g : SL) (i : Bool) : Subgroup Space :=
  fixedSpace (markedParabolic (dualMark σ) g i)

/-- The actual neighboring orbit span of that line. -/
noncomputable def neighboringPlane (σ : MulAut SL) (g : SL) (i : Bool) : Subgroup Space :=
  orbitSpan (dualMark σ) (modelParabolic g (!i)) (seedLine σ g i)

/-- Pure finite geometry to be proved from the zero natural fixed-space condition.
No field is an ambient-group commutator or an assertion about the source seed. -/
structure MatrixGeometry (σ : MulAut SL) (g : SL) (i : Bool) : Prop where
  seed_card : Nat.card (seedLine σ g i) = 2
  small_invariant : ∀ A : Subgroup Space, Nat.card A ≤ 4 →
    (∀ a ∈ markedParabolic σ g i, A.map (vectorAction a).toMonoidHom = A) →
    A ≤ modelValues σ g i
  star_cover : (⨆ p : modelParabolic g i,
    (neighboringPlane σ g i).map (vectorAction (dualMark σ p)).toMonoidHom) = ⊤
  star_neighbors : ∀ p : modelParabolic g i,
    ∃ r s : modelParabolic g (!i),
      (neighboringPlane σ g i).map (vectorAction (dualMark σ p)).toMonoidHom ≤
        seedLine σ g i ⊔ (seedLine σ g i).map
          (vectorAction (dualMark σ ((p : SL) * r))).toMonoidHom ∧
      (neighboringPlane σ g i).map (vectorAction (dualMark σ p)).toMonoidHom ≤
        seedLine σ g i ⊔ (seedLine σ g i).map
          (vectorAction (dualMark σ ((p : SL) * s))).toMonoidHom ∧
      (modelValues σ g i).map (vectorAction (σ ((p : SL) * r))).toMonoidHom ⊓
        (modelValues σ g i).map (vectorAction (σ ((p : SL) * s))).toMonoidHom ≤
          (modelValues σ g (!i)).map (vectorAction (σ p)).toMonoidHom ∧
      (modelValues σ g (!i)).map (vectorAction (σ p)).toMonoidHom ≤ modelValues σ g i
  opposite_cover : ∃ r s : modelParabolic g (!i), ∃ a b : modelParabolic g i,
    neighboringPlane σ g i ⊔ (neighboringPlane σ g i).map
      (vectorAction (dualMark σ ((r : SL) * a))).toMonoidHom = ⊤ ∧
    neighboringPlane σ g i ⊔ (neighboringPlane σ g i).map
      (vectorAction (dualMark σ ((s : SL) * b))).toMonoidHom = ⊤ ∧
    (modelValues σ g (!i)).map (vectorAction (σ ((r : SL) * a))).toMonoidHom ⊓
      (modelValues σ g (!i)).map (vectorAction (σ ((s : SL) * b))).toMonoidHom = ⊥
  core_fixed : neighboringPlane σ g i ≤
    fixedSpace (((pCore 2 (modelParabolic g (!i))).map
      (modelParabolic g (!i)).subtype).map (dualMark σ).toMonoidHom)
  irreducible : ∀ D : Subgroup Space, D ≤ modelValues σ g i →
    (∀ a ∈ markedParabolic σ g i, D.map (vectorAction a).toMonoidHom = D) →
    D = ⊥ ∨ D = modelValues σ g i

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing.Incidence.DualGeometry
