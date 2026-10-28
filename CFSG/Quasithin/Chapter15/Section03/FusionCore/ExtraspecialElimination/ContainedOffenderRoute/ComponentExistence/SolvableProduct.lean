module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct.GroupStructure
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SaturatedLift

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
open ComponentReduction FactorGeneration ClassificationCases
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

private theorem threeCore_map_subtype {D : Type*} [Group D]
    (N : Subgroup D) (K : Subgroup N) :
    ((pCore 3 K).map K.subtype).map N.subtype =
      (pCore 3 (K.map N.subtype)).map (K.map N.subtype).subtype := by
  let e := K.equivMapOfInjective N.subtype N.subtype_injective
  rw [← pCore_map_iso 3 e, map_map, map_map]
  rfl

private theorem coinvariants_map_subtype {D W : Type*} [Group D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (N : Subgroup D) (K : Subgroup N) :
    Representation.Coinvariants.ker (ρ.comp (K.map N.subtype).subtype) =
      Representation.Coinvariants.ker ((ρ.comp N.subtype).comp K.subtype) := by
  unfold Representation.Coinvariants.ker
  congr 1
  ext w
  constructor
  · rintro ⟨⟨x, v⟩, rfl⟩
    obtain ⟨k, hk, he⟩ := x.property
    refine ⟨(⟨k, hk⟩, v), ?_⟩
    change ρ (k : D) v - v = ρ (x : D) v - v
    change (k : D) = (x : D) at he
    rw [he]
  · rintro ⟨⟨k, v⟩, rfl⟩
    exact ⟨(⟨(k : N), mem_map_of_mem N.subtype k.property⟩, v), rfl⟩

universe u
variable {G : Type u} [Group G]
    {κ : GroupClass.{u}} {H M Y V Y0 T ZS Z E : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : PlacedInput κ H M Y V Y0 T ZS Z E)

/-- The selected actor, restricted to its actual conjugate span. -/
abbrev actorInSpan :=
  (starImage H d.selected.carrier).subgroupOf (starImage H (localSpan d.selected.carrier H))

theorem actor_le_span : starImage H d.selected.carrier ≤
    starImage H (localSpan d.selected.carrier H) :=
  map_mono (comap_mono (le_conjugateSpanBy d.selected.carrier H))

theorem actorInSpan_elementary : IsElementaryTwo (actorInSpan d) := by
  let : IsElementaryAbelian 2 (starImage H d.selected.carrier) := d.selected.best.1.2
  refine ⟨?_, IsElementaryAbelian.subgroupOf (actor_le_span d)⟩
  intro h
  have hm := congrArg (map (starImage H (localSpan d.selected.carrier H)).subtype) h
  rw [Subgroup.map_bot, map_subgroupOf_eq_of_le (actor_le_span d)] at hm
  exact d.selected.best.1.1 hm

variable (c : TwoFactorCase (starAction d))

/-- A canonical source factor on which the selected actor projects nontrivially. -/
noncomputable abbrev factor := Product.chosen c.product (actorInSpan d)

theorem factor_eq : factor d c = c.first ∨ factor d c = c.second :=
  Product.chosen_eq c.product (actorInSpan d)

theorem factor_normal : (factor d c).Normal :=
  Product.chosen_normal c.product (actorInSpan d)

/-- The chosen factor embedded in H*, with the literal inclusion from J*. -/
noncomputable abbrev imageFactor :=
  (factor d c).map (starImage H (localSpan d.selected.carrier H)).subtype

theorem imageFactor_le : imageFactor d c ≤ starImage H (localSpan d.selected.carrier H) :=
  map_subtype_le _

theorem imageFactor_subnormal :
    ((imageFactor d c).subgroupOf (starImage H (localSpan d.selected.carrier H))).IsSubnormal := by
  change ((factor d c).map (starImage H (localSpan d.selected.carrier H)).subtype |>.comap
    (starImage H (localSpan d.selected.carrier H)).subtype).IsSubnormal
  rw [comap_map_eq_self_of_injective (starImage H (localSpan d.selected.carrier H)).subtype_injective]
  exact (factor_normal d c).isSubnormal

/-- Restricting through the literal factor inclusion preserves its moved space. -/
theorem imageFactor_rank
    (hrank : Module.finrank (ZMod 2) (Representation.Coinvariants.ker
      ((starAction d).comp (factor d c).subtype)) = 2) :
    Module.finrank (ZMod 2) (Representation.Coinvariants.ker
      (d.action.representation.comp (imageFactor d c).subtype)) = 2 := by
  rw [coinvariants_map_subtype]
  exact hrank

variable (e₁ : c.first ≃* Equiv.Perm (Fin 3)) (e₂ : c.second ≃* Equiv.Perm (Fin 3))

noncomputable def imageFactorModel : imageFactor d c ≃* Equiv.Perm (Fin 3) :=
  ((factor d c).equivMapOfInjective (starImage H (localSpan d.selected.carrier H)).subtype
    (starImage H (localSpan d.selected.carrier H)).subtype_injective).symm.trans
      (Product.chosenModel c.product (actorInSpan d) e₁ e₂)

include e₁ e₂ in
/-- Cubic generation uses the original actor, not a subgroup of the factor. -/
theorem imageFactor_threeCore :
    (pCore 3 (imageFactor d c)).map (imageFactor d c).subtype =
      ⁅(pCore 3 (imageFactor d c)).map (imageFactor d c).subtype,
        starImage H d.selected.carrier⁆ := by
  have hh := congrArg (map (starImage H (localSpan d.selected.carrier H)).subtype)
    (Product.chosen_threeCore_commutator c.product (actorInSpan d)
      (actorInSpan_elementary d) e₁ e₂)
  rw [map_commutator, threeCore_map_subtype] at hh
  simpa only [actorInSpan, map_subgroupOf_eq_of_le (actor_le_span d)] using hh

/-- Assembly from the two outstanding consequences of the source data.
The moved-plane ranks and ambient orbit bounds are explicit here and must
be discharged before eliminating the B.5.6(3) alternative. -/
noncomputable def of_rank_and_orbit
    (hrank : ∀ F : Subgroup (starImage H (localSpan d.selected.carrier H)),
      F = c.first ∨ F = c.second → Module.finrank (ZMod 2)
        (Representation.Coinvariants.ker ((starAction d).comp F.subtype)) = 2)
    (horbit : ∀ F : Subgroup (starImage H (localSpan d.selected.carrier H)),
      F = c.first ∨ F = c.second →
        (Set.range fun h : H ⧸ pCore 2 H =>
          (F.map (starImage H (localSpan d.selected.carrier H)).subtype).map
            (MulAut.conj h).toMonoidHom).ncard ≤ 2) :
    SolvableStarFactor H ZS Z d.selected.carrier d.action :=
  solvableStarFactorOfImage H ZS Z d.selected.carrier d.action d.selected.le_local
    (imageFactor d c) (imageFactor_le d c) (imageFactor_subnormal d c)
    (imageFactorModel d c e₁ e₂) (imageFactor_threeCore d c e₁ e₂)
    (imageFactor_rank d c (hrank _ (factor_eq d c))) (horbit _ (factor_eq d c))

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.SolvableProduct
