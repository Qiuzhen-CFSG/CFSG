module

public import Theory.GroupTheory.MarkedBinaryAction
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction.Centralizers
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics

/-!
# Extending the actual derived-coordinate representations

Compose the published derived embedding with the ambient injection and
identify its range with E. Conjugation then supplies the binary linear action;
its kernel is the proved ambient centralizer F. Factoring through F gives a
faithful homomorphism, and injectivity of the coordinate embedding proves its
restriction agrees with the published parabolic representation.

Source: Aschbacher--Smith 14.2.21, printed p.989.
-/

public section

open Subgroup Theory.LinearAlgebra.BinaryFivePointStabilizer
open ReeTwo.ParabolicConcrete ReeTwo.Centralizer
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction

private def coordinateEquiv {H M : Type*} [Group H] [Group M]
    (i : H →* M) (hi : Function.Injective i) (E : Subgroup H)
    (d : Multiplicative DerivedSpace →* H) (hd : Function.Injective d) (hr : d.range = E) :
    Multiplicative DerivedSpace ≃* E.map i :=
  (MonoidHom.ofInjective (f := i.comp d) (hi.comp hd)).trans
    (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, hr]))

/-- A concrete coordinate embedding constructs the ambient quotient representation,
including its equation on every vector and its exact restriction to the local action. -/
private theorem extend_action {H M : Type*} [Group H] [Group M]
    (i : H →* M) (hi : Function.Injective i) (E F : Subgroup H)
    [(E.map i).Normal] [(F.map i).Normal]
    (d : Multiplicative DerivedSpace →* H) (hd : Function.Injective d) (hr : d.range = E)
    (r : H →* stabilizer markedVector)
    (heq : ∀ g v, d (Multiplicative.ofAdd ((r g).val v)) = g * d (Multiplicative.ofAdd v) * g⁻¹)
    (hC : centralizer (E.map i : Set M) = F.map i)
    (hz : i (d (Multiplicative.ofAdd markedVector)) ∈ center M) :
    ∃ ρ : M ⧸ F.map i →* stabilizer markedVector,
      Function.Injective ρ ∧
      (∀ g v, i (d (Multiplicative.ofAdd ((ρ (QuotientGroup.mk' _ g)).val v))) =
        g * i (d (Multiplicative.ofAdd v)) * g⁻¹) ∧
      (∀ h, ρ (QuotientGroup.mk' _ (i h)) = r h) := by
  let e := coordinateEquiv i hi E d hd hr
  have hz' : (e (Multiplicative.ofAdd markedVector) : M) ∈ center M := hz
  let a := Theory.GroupTheory.MarkedBinaryAction.representation (E.map i) e markedVector hz'
  have ha : a.ker = F.map i :=
    (Theory.GroupTheory.MarkedBinaryAction.representation_ker _ _ _ _).trans hC
  let ρ := QuotientGroup.lift (F.map i) a ha.ge
  have hρ : Function.Injective ρ :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr ha.symm
  have hconj (g : M) (v : DerivedSpace) :
      i (d (Multiplicative.ofAdd ((ρ (QuotientGroup.mk' _ g)).val v))) =
        g * i (d (Multiplicative.ofAdd v)) * g⁻¹ := by
    exact Theory.GroupTheory.MarkedBinaryAction.representation_conjugation (E.map i) e markedVector hz' g v
  refine ⟨ρ, hρ, hconj, ?_⟩
  intro h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Multiplicative.ofAdd.injective
  apply hd
  apply hi
  rw [hconj, heq, map_mul, map_mul, map_inv]

/-- Explicit conjugation on the full-Ree derived coordinates extends to Mc/F. -/
theorem ree_extended_action {M : Type*} [Group M]
    (i : Tits.ExceptionalParabolics.FullRee.first →* M) (hi : Function.Injective i)
    [(reeE.map i).Normal] [(reeF.map i).Normal]
    (hC : centralizer (reeE.map i : Set M) = reeF.map i)
    (hz : i (reeDerivedEmbedding (Multiplicative.ofAdd markedVector)) ∈ center M) :
    ∃ ρ : M ⧸ reeF.map i →* stabilizer markedVector,
      Function.Injective ρ ∧
      (∀ g v, i (reeDerivedEmbedding (Multiplicative.ofAdd
          ((ρ (QuotientGroup.mk' _ g)).val v))) =
        g * i (reeDerivedEmbedding (Multiplicative.ofAdd v)) * g⁻¹) ∧
      (∀ h, ρ (QuotientGroup.mk' _ (i h)) = reeRepresentation h) :=
  extend_action i hi reeE reeF reeDerivedEmbedding reeDerivedEmbedding_injective
    reeDerivedEmbedding_range reeRepresentation reeRepresentation_conjugation hC hz

/-- The same construction with the literal Atlas Tits derived embedding. -/
theorem tits_extended_action {M : Type*} [Group M]
    (i : Tits.ExceptionalParabolics.first →* M) (hi : Function.Injective i)
    [(titsE.map i).Normal] [(titsF.map i).Normal]
    (hC : centralizer (titsE.map i : Set M) = titsF.map i)
    (hz : i (titsDerivedEmbedding (Multiplicative.ofAdd markedVector)) ∈ center M) :
    ∃ ρ : M ⧸ titsF.map i →* stabilizer markedVector,
      Function.Injective ρ ∧
      (∀ g v, i (titsDerivedEmbedding (Multiplicative.ofAdd
          ((ρ (QuotientGroup.mk' _ g)).val v))) =
        g * i (titsDerivedEmbedding (Multiplicative.ofAdd v)) * g⁻¹) ∧
      (∀ h, ρ (QuotientGroup.mk' _ (i h)) = titsRepresentation h) :=
  extend_action i hi titsE titsF titsDerivedEmbedding titsDerivedEmbedding_injective
    titsDerivedEmbedding_range titsRepresentation titsRepresentation_conjugation hC hz
end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.AmbientDerivedAction
