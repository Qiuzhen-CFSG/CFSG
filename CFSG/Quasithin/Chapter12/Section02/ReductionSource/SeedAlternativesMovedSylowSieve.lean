module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models
-- The concrete componentHom action is needed for the literal intertwiner.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveKernel
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveTwists
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveModels
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# Invariant-model exclusions for the literal moved chosen seed

The original component homomorphism has characteristic kernel whenever its
marked model has trivial center. Model automorphism intertwiners therefore
fix the homogeneous chosen subspace. Transport through the original inclusion
in G forces T to normalize V, contradicting strict movement. This removes the
natural SL₂ and G₂ rows and the invariant deleted permutation rows of B.4.2.

The actual table application is `SeedAlternativesMovedSylowSieveAssembly`.
Source: Aschbacher--Smith D.3.5(5), combined manuscript of 1 March 2004,
printed pp.195--196, applied to the choice in 3.2.5 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A center-free chosen component image has characteristic kernel: it is the
preimage of the center of the original quasisimple two-core quotient. -/
theorem componentHom_kernel_characteristic (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L)) (hz : center D.componentImage = ⊥) :
    D.componentHom.ker.Characteristic := by
  let := hq
  exact kernel_characteristic_of_quasisimple_quotient (pCore 2 L)
    D.componentHom D.componentQuotientHom D.componentQuotientHom_surjective
    D.componentQuotientHom_mk hz

/-- Automorphism invariance of a marked center-free model forces normalization
of the original chosen subgroup. Neither the model action nor its kernel is
replaced by an unrelated quotient. -/
theorem sylow_normalizes_of_model_twists (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    {P W : Type*} [Group P] [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) P W) (hz : center P = ⊥)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) τ)
    (htwist : ∀ a : MulAut P, ∃ d : W ≃ₗ[ZMod 2] W,
      ∀ g v, d (τ g v) = τ (a g) (d v)) :
    (T : Subgroup G) ≤ normalizer (V : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf H
  let R := (T : Subgroup G).subgroupOf H
  let ρ := reducedRepresentation H
  have hz' : center D.componentImage = ⊥ := center_eq_bot_of_model_equiv e.groupEquiv hz
  have hker := D.componentHom_kernel_characteristic hq hz'
  let j : X ≃* L := subgroupOfEquivOfLe le_sup_left
  let r := D.componentHom.comp j.toMonoidHom
  let f := e.groupEquiv.toMonoidHom.comp r
  have hf : Function.Surjective f := e.groupEquiv.surjective.comp
    (D.componentHom_surjective.comp j.surjective)
  let : f.ker.Characteristic :=
    characteristic_kernel_model_transport D.componentHom hker j e.groupEquiv
  let b : Representation.Equiv (invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation
      (τ.comp f) := Representation.Equiv.mk e.linearEquiv (by
    intro x
    apply LinearMap.ext
    intro v
    have he := e.intertwines (D.componentHom (j x)) v
    change e.linearEquiv ((invariantSubspace ρ X D.space D.irrPlus.invariant).toRepresentation x v) = _ at he
    exact he)
  have hn := homogeneous_invariant_of_model_twists ρ D.irrPlus
    (D.seed_inf_fixedSpace_eq_bot hc) f hf τ b htwist
  have hnV := Theory.GroupTheory.ReducedNormal.subspaceImage_normalizes
    H (T : Subgroup G) le_sup_right D.space hn
  change (T : Subgroup G) ≤ normalizer (subspaceImage H D.space : Set G) at hnV
  rwa [D.image_eq] at hnV

/-- The invariant deleted permutation rows cannot occur for a moved seed. -/
theorem seed_not_alternatingNatural_of_moved (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (n : ℕ) (hn : 5 ≤ n) (h6 : n ≠ 6) :
    ¬ Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural n)) := by
  rintro ⟨e⟩
  have hz : center (alternatingGroup (Fin n)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))
  have hs := D.sylow_normalizes_of_model_twists hq hc (alternatingNatural n) hz e
    (alternating_natural_twist n hn h6)
  exact hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hs)

/-- The natural rank-one linear row cannot occur for a moved seed. -/
theorem seed_not_linearTwo_of_moved (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) (F : BinaryField) :
    ¬ Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 2)) := by
  rintro ⟨e⟩
  have hs := D.sylow_normalizes_of_model_twists hq hc (linearNatural F 2)
    (Theory.PSL2.sl2_center_eq_bot F.Carrier) e (linear_two_natural_twist (F := F.Carrier))
  exact hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hs)

/-- The nonbinary natural G₂ row cannot occur for a moved seed. -/
theorem seed_not_g2_of_moved (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) (F : BinaryField) (hF : 1 < F.degree) :
    ¬ Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (binaryG2 F)) := by
  rintro ⟨e⟩
  have hf : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hF)
  have hs := D.sylow_normalizes_of_model_twists hq hc (binaryG2 F)
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot hf) e
    (g2_natural_twist hf)
  exact hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hs)

/-- The derived binary G₂ row is also invariant and cannot be a moved seed. -/
theorem seed_not_g2Two_of_moved (D : ChosenModule T L V)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) :
    ¬ Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) := by
  rintro ⟨e⟩
  have hs := D.sylow_normalizes_of_model_twists hq hc _
    g2_two_derived_center_eq_bot e g2_two_derived_natural_twist
  exact hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hs)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
