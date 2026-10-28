module

public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Stellmacher.SectionNine.DistanceOneChiefFrattini
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# Elementary structure of the canonical initial chief quotient

The actual initial core quotient is elementary abelian precisely when its
Frattini subgroup commutes with the initial residual modulo the initial
center. The criterion uses the proved greatestness characterization of the
canonical subgroup, so it does not require unfolding its sealed definition.
The proved ambient Frattini commutator bound therefore establishes elementary
structure for the canonical quotient in the distance-one chief branch.
No numerical chief index, core equality, or identification of the initial
center kernel with the initial core is assumed.

Source: Stellmacher (9.1), printed p.47, relation (10).
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext

universe u

public theorem distance_one_le_chief_subgroup_iff
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) {subgroup : Subgroup G}
    (hcore : subgroup ≤ q ctx.Γ ctx.criticalPath.a) :
    subgroup ≤ distanceOneChiefSubgroup ctx ↔
      ⁅subgroup, e ctx.Γ ctx.criticalPath.a⁆ ≤ z ctx.Γ ctx.criticalPath.a := by
  have hproperties := distance_one_chief_subgroup_properties ctx
  constructor
  · intro hle
    exact (Subgroup.commutator_mono hle le_rfl).trans_eq hproperties.2.2.2.1
  · intro hcommutator
    have hcoreStabilizer : q ctx.Γ ctx.criticalPath.a ≤
        stabilizer ctx.Γ ctx.criticalPath.a := by
      rw [q, ctx.Γ.twoCoreAt_def]
      exact Subgroup.map_subtype_le _
    exact (Subgroup.le_commutatorPreimage hcore hcommutator).trans
      (hproperties.2.2.2.2 _ (Subgroup.commutatorPreimage_le _ _ _)
        (Subgroup.commutator_commutatorPreimage_eq _ _ _
          (hcoreStabilizer.trans (stabilizer_le_normalizer_z ctx.Γ ctx.criticalPath.a))
          (hproperties.2.1.trans hproperties.1)
          (distance_one_initial_center_full_residual ctx)))

public theorem distance_one_chief_quotient_elementary_iff_frattini
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) :
    IsElementaryAbelian 2 (DistanceOneChiefQuotient ctx) ↔
      ⁅FrattiniAmbient (q ctx.Γ ctx.criticalPath.a),
        e ctx.Γ ctx.criticalPath.a⁆ ≤ z ctx.Γ ctx.criticalPath.a := by
  have hcore : IsPGroup 2 (q ctx.Γ ctx.criticalPath.a) := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact (pCore_isPGroup (p := 2) (G := stabilizer ctx.Γ ctx.criticalPath.a)).map
      (stabilizer ctx.Γ ctx.criticalPath.a).subtype
  have hfrattiniCore : FrattiniAmbient (q ctx.Γ ctx.criticalPath.a) ≤
      q ctx.Γ ctx.criticalPath.a := Subgroup.map_subtype_le _
  constructor
  · intro helementary
    have hfrattini := Subgroup.frattini_le_of_elementary_quotient hcore
      ((distanceOneChiefSubgroup ctx).subgroupOf (q ctx.Γ ctx.criticalPath.a))
      helementary
    apply (distance_one_le_chief_subgroup_iff ctx hfrattiniCore).mp
    rintro element ⟨representative, hrepresentative, rfl⟩
    exact hfrattini hrepresentative
  · intro hcommutator
    have hmap := (distance_one_le_chief_subgroup_iff ctx hfrattiniCore).mpr hcommutator
    apply Subgroup.elementary_quotient_of_frattini_le hcore
    intro element helement
    exact hmap (Subgroup.mem_map_of_mem (q ctx.Γ ctx.criticalPath.a).subtype helement)

public theorem distance_one_chief_quotient_elementary_of_frattini
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hfrattini : ⁅FrattiniAmbient (q ctx.Γ ctx.criticalPath.a),
      e ctx.Γ ctx.criticalPath.a⁆ ≤ z ctx.Γ ctx.criticalPath.a) :
    IsElementaryAbelian 2 (DistanceOneChiefQuotient ctx) :=
  (distance_one_chief_quotient_elementary_iff_frattini ctx).mpr hfrattini

public theorem distance_one_chief_quotient_elementary
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (branch : DistanceOneChiefBranchData ctx) :
    IsElementaryAbelian 2 (DistanceOneChiefQuotient ctx.toLocalContext) :=
  distance_one_chief_quotient_elementary_of_frattini ctx.toLocalContext
    (distance_one_chief_frattini_commutator_le ctx hb hfaith branch)

end Stellmacher.SectionNine
