module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.FiveGeneration.Calculation
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.ActorImage
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment.QuotientTransport

/-!
# Applying positioned S₅ generation to the original centralizer actor

The image of the original eight-actor in the literal radical quotient has
order four. Its specified position outside A₅ permits the local E₁ generation
calculation. Transport back through the actual quotient equivalence and
lift through the original restricted family, removing the solvable kernel.

This discharges the `hfive` premise of the marked S₅ centralizer consumer.
The actual quotient equivalence and the position of the actor remain the
independent model inputs; no unrestricted E-generation assertion is used.
The original consumer application is also checked in
`Scratch/FiveGeneration/ConsumerApplication.lean` without importing the
CentralizerContainment umbrella into this module.

Source: Aschbacher–Smith E.1.2, E.1.5, E.1.8, E.1.10 and E.1.14(7),
pp.210–214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
variable {G : Type*} [Group G] [Finite G]

/-- The marked S₅ quotient consumer with its positioned-four-group generation
premise discharged. The quotient equivalence and original actor position remain explicit. -/
theorem centralizer_le_of_positioned_symmetric_five_quotient {T : Sylow 2 G}
    (d : LargeFamilyObstruction T) {A : Subgroup G} (hA : A ∈ d.family)
    (hAT : A ≤ (T : Subgroup G)) (hcard : Nat.card A = 8)
    {z : G} (hzA : z ∈ A) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hsmall : Nat.card (A.subgroupOf (centralizerResidualOvergroup T z) ⊓
      solvableRadical (centralizerResidualOvergroup T z) :
      Subgroup (centralizerResidualOvergroup T z)) < 4)
    (e : ((centralizerResidualOvergroup T z) ⧸
      solvableRadical (centralizerResidualOvergroup T z)) ≃* Equiv.Perm (Fin 5))
    (hpos : ¬ ((A.subgroupOf (centralizerResidualOvergroup T z)).map
      (QuotientGroup.mk' (solvableRadical (centralizerResidualOvergroup T z)))).map
        e.toMonoidHom ≤ alternatingGroup (Fin 5)) :
    centralizer ({z} : Set G) ≤ d.overgroup := by
  let K := centralizerResidualOvergroup T z
  let q := QuotientGroup.mk' (solvableRadical K)
  let a := (A.subgroupOf K).map q
  let S := (T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)).mapSurjective
    (f := q) (QuotientGroup.mk'_surjective _)
  let := d.elementary.1 A hA
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf
    (hAT.trans le_sup_right)
  let : IsElementaryAbelian 2 a := IsElementaryAbelian.map q
  have ha : Nat.card a = 4 :=
    quotient_actor_card_four_of_small_radical_intersection hAT hcard hzA hz hTz hsmall
  have hc : Nat.card (a.map e.toMonoidHom) = 4 :=
    (Nat.card_congr (a.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm.trans ha
  have haS : a ≤ (S : Subgroup _) := map_mono (comap_mono hAT)
  have hg := FiveGeneration.positioned_four_generation
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
    (a.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom) hc (map_mono haS) hpos
  have hgen : eSubgroup 1 (S : Subgroup _) a ⊔ (S : Subgroup _) = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_sup, map_eSubgroup_equiv, map_top_of_surjective _ e.surjective]
    exact hg
  let Ω := Subgroup.map q '' ChiefOrbit.restrictedFamily K d.family
  have hΩ : IsElementaryFamily Ω :=
    (ChiefOrbit.restrictedFamily_elementary K d.elementary).map q (QuotientGroup.mk'_surjective _)
  have haΩ : a ∈ Ω := by
    refine ⟨A.subgroupOf K, ?_, rfl⟩
    change (A.subgroupOf K).map K.subtype ∈ d.family
    rwa [map_subgroupOf_eq_of_le (show A ≤ K from hAT.trans le_sup_right)]
  apply centralizer_le_of_residual_quotient_family_generation d hTz
  change eFamilySubgroup 1 (S : Subgroup _) Ω ⊔
    normalizer (weakClosure (S : Subgroup _) Ω : Set _) = ⊤
  apply top_unique
  rw [← hgen]
  have hEF : eSubgroup 1 (S : Subgroup _) a ≤ eFamilySubgroup 1 (S : Subgroup _) Ω :=
    le_iSup_of_le (⟨a, haΩ, haS⟩ : {B : Subgroup (K ⧸ solvableRadical K) //
      B ∈ Ω ∧ B ≤ (S : Subgroup _)}) le_rfl
  exact sup_le (hEF.trans le_sup_left)
    ((sylow_le_weakClosure_normalizer S hΩ).trans le_sup_right)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors
