module

public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The local class in the Glauberman–Niles theorem

This is Definition C.1.17 of Aschbacher–Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), printed p.126.
An embedding retains the given abstract two-group B and its image as a Sylow
subgroup. The normal closure V, centralizer quotient H*, generalized Fitting
subgroup of H*, and its full inverse image are literal subgroup constructions.

The natural-module condition identifies both F*(H*) with the derived subgroup
of the actual projective matrix group and [V,F*(H*)]/C_[V,F*(H*)](F*(H*))
with its natural module. Conjugation is expressed using lifts in H. The
lift-independence theorem below verifies this convention. In particular n=1
is permitted: the actor is PSL₂(2)', rather than all of PSL₂(2).
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles

open Theory.GroupTheory
open scoped MatrixGroups

variable {B : Type u} [Group B] {H : Type v} [Group H]

/-- Ω₁(Z(B)), intrinsically in B. -/
def omegaCenter (B : Type u) [Group B] : Subgroup B :=
  (omega₁ (Subgroup.center B) (p := 2)).map (Subgroup.center B).subtype

/-- The literal normal closure of the embedded omega center. -/
def localV (e : B →* H) : Subgroup H :=
  Subgroup.normalClosure (omegaCenter B |>.map e : Set H)

instance localV_normal (e : B →* H) : (localV e).Normal :=
  Subgroup.normalClosure_normal

/-- The kernel of the action of H on V. -/
def localKernel (e : B →* H) : Subgroup H :=
  Subgroup.centralizer (localV e : Set H)

instance localKernel_normal (e : B →* H) : (localKernel e).Normal :=
  inferInstanceAs (Subgroup.centralizer (localV e : Set H)).Normal

/-- H* = H/C_H(V). -/
abbrev LocalStar (e : B →* H) := H ⧸ localKernel e

/-- The full inverse image in H of F*(H*); all conjugation formulas use it. -/
def actorLift (e : B →* H) : Subgroup H :=
  (generalizedFitting (LocalStar e)).comap (QuotientGroup.mk' (localKernel e))

instance actorLift_normal [Finite H] (e : B →* H) : (actorLift e).Normal :=
  inferInstanceAs ((generalizedFitting (LocalStar e)).comap
    (QuotientGroup.mk' (localKernel e))).Normal

/-- The moved subgroup [V,F*(H*)], computed with the full inverse image. -/
def moved (e : B →* H) : Subgroup H := ⁅localV e, actorLift e⁆

instance moved_normal [Finite H] (e : B →* H) : (moved e).Normal :=
  inferInstanceAs (⁅localV e, actorLift e⁆).Normal

/-- The fixed subgroup of the moved subgroup, intrinsically in that subgroup. -/
def movedFixed (e : B →* H) : Subgroup (moved e) :=
  (Subgroup.centralizer (actorLift e : Set H)).subgroupOf (moved e)

instance movedFixed_normal [Finite H] (e : B →* H) : (movedFixed e).Normal :=
  inferInstanceAs ((Subgroup.centralizer (actorLift e : Set H)).subgroupOf
    (moved e)).Normal

/-- The literal moved module modulo its fixed points. -/
abbrev MovedModule [Finite H] (e : B →* H) := moved e ⧸ movedFixed e

/-- The element of F*(H*) represented by a lift. -/
def actorProjection (e : B →* H) : actorLift e →* generalizedFitting (LocalStar e) :=
  (QuotientGroup.mk' (localKernel e)).restrict (fun _ hx => hx)

/-- Actual conjugation on the moved subgroup. -/
def movedConjugate [Finite H] (e : B →* H) (h : H) (w : moved e) : moved e :=
  ⟨h * (w : H) * h⁻¹, (moved_normal e).conj_mem w w.property h⟩

/-- The moved subgroup lies in V. -/
theorem moved_le_localV (e : B →* H) : moved e ≤ localV e :=
  Subgroup.commutator_le_left _ _

/-- Two representatives of the same element of H* induce the same
conjugation on V. This justifies computing the source action with lifts. -/
theorem conjugate_eq_of_quotient_eq (e : B →* H) {a b w : H}
    (hab : QuotientGroup.mk' (localKernel e) a =
      QuotientGroup.mk' (localKernel e) b) (hw : w ∈ localV e) :
    a * w * a⁻¹ = b * w * b⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := (QuotientGroup.mk'_eq_mk' (localKernel e)).mp hab
  have hc : w * k = k * w := Subgroup.mem_centralizer_iff.mp hk w hw
  calc
    a * w * a⁻¹ = a * (k * w * k⁻¹) * a⁻¹ := by rw [← hc]; simp [mul_assoc]
    _ = (a * k) * w * (a * k)⁻¹ := by simp [mul_assoc]

/-- The natural-module formula is independent of the chosen actor lift. -/
theorem movedConjugate_eq_of_projection_eq [Finite H] (e : B →* H)
    {a b : actorLift e} (hab : actorProjection e a = actorProjection e b)
    (w : moved e) : movedConjugate e a w = movedConjugate e b w := by
  apply Subtype.ext
  exact conjugate_eq_of_quotient_eq e (congrArg Subtype.val hab)
    (moved_le_localV e w.property)

/-- A marked identification of the source actor and its actual natural module.
The canonical SL₂-to-PSL₂ equivalence in characteristic two supplies the
matrix of each projective actor, including the derived order-three actor
when the field has two elements. -/
structure NaturalModel [Finite H] (e : B →* H)
    (F : Type) [Field F] [CharP F 2] where
  actorIso : generalizedFitting (LocalStar e) ≃* commutator PSL(2,F)
  moduleIso : MovedModule e ≃* Multiplicative (Fin 2 → F)
  intertwining : ∀ (a : actorLift e) (w : moved e),
    Multiplicative.toAdd (moduleIso
      (QuotientGroup.mk' (movedFixed e) (movedConjugate e a w))) =
    Representation.specialLinearNatural 2
      (Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
        (actorIso (actorProjection e a) : PSL(2,F)))
      (Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (movedFixed e) w)))

/-- Definition C.1.17 with the embedding of B explicitly marked. No
pushing-up conclusion is part of membership in this class. -/
structure InLocalClass [Finite H] (e : B →* H) : Prop where
  injective : Function.Injective e
  sylow : ∃ T : Sylow 2 H, e.range = (T : Subgroup H) ∧
    ChapterB.IsMinimalParabolicOver T ⊤
  fitting : generalizedFitting H = pCore 2 H
  natural : ∃ (n : ℕ), 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F)
    (_ : CharP F 2), Nat.card F = 2 ^ n ∧ Nonempty (NaturalModel e F)

/-- C.1.18(3) uses the two-residual O²(H), not the two-core O₂(H).
The named types include their actual conjugation modules and ambient
subnormality. -/
def BlockAlternative (H : Type v) [Group H] : Prop :=
  IsBlockOfType (pResidual 2 H)
    ((∃ n, IsL2EvenBlock (pResidual 2 H) n) ∨ IsAlternatingBlock (pResidual 2 H) 3)

/-- The local conclusion for a fixed pair in B. -/
def Alternatives (D₁ D₂ : Subgroup B) (e : B →* H) : Prop :=
  D₁.map e ≤ Subgroup.center H ∨ (D₂.map e).Normal ∨ BlockAlternative H

/-- The model yields the expected size, as a consequence of its actual
module isomorphism, never as a substitute for that isomorphism. -/
theorem NaturalModel.module_card [Finite H] (e : B →* H)
    {F : Type} [Field F] [CharP F 2] (m : NaturalModel e F) :
    Nat.card (MovedModule e) = Nat.card F ^ 2 := by
  calc
    Nat.card (MovedModule e) = Nat.card (Fin 2 → F) :=
      Nat.card_congr m.moduleIso.toEquiv
    _ = Nat.card F ^ 2 := by rw [Nat.card_fun, Nat.card_fin]

end CFSG.Quasithin.ChapterC.GlaubermanNiles

end
