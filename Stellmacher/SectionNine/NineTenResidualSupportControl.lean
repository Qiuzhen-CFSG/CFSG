module

public import Stellmacher.SectionNine.NineResidualImageOddCore
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction

/-!
# The actual extracted residual lies in the selected actor commutator

Retain a genuine geometric extraction and its uniform residual commutator
bound for actors outside the coatom. For any such actor, map the residual
through a surjective action of the actual vertex stabilizer which kills its
two-core. Its image lies in the commutator of the target odd core with the
same actor image, hence in that actor's canonical transvection factor when
the later action supplies one.

First transport the ambient commutator inclusion to the literal vertex
subgroup, using its injective inclusion in the ambient group. Map it through
the supplied action. Residual monotonicity and the genuine local residual
image theorem place its first argument in the target's odd core. Every group,
actor and action is retained; no smaller center-generated extraction group
is identified with the generic module-generated extraction group.

This is the group-image part of the selected-support step in Stellmacher
(9.10), printed p.57, after assertions (3)--(4). The separate quotient-action
formula transports the resulting displacement control to neighbor centers.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_extracted_residual_image_le_actor_commutator
    {G X : Type u} [Group G] [Finite G] [Group X] [Finite X]
    {T A B : Subgroup G} (ctx : SectionNineLocalContext G T A B)
    (vertex neighbor : ctx.Γ.Vertex) (V E A0 : Subgroup G) (originalActor : G)
    (data : NineThreeGeometricData ctx.Γ vertex neighbor V E A0 originalActor)
    (hactors : ∀ b : G, b ∈ V → b ∉ A0 →
      twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers b⁆)
    (action : GAt ctx.Γ vertex →* X) (hsurj : Function.Surjective action)
    (hkernel : pCore 2 (GAt ctx.Γ vertex) ≤ action.ker)
    (actor : GAt ctx.Γ vertex) (hactor : (actor : G) ∈ V) (hactorNot : (actor : G) ∉ A0) :
    ((twoResidualIn E).subgroupOf (GAt ctx.Γ vertex)).map action ≤
      ⁅SectionOne.oddCore X, Subgroup.zpowers (action actor)⁆ := by
  let Γ := ctx.Γ
  let P := GAt Γ vertex
  let F := twoResidualIn E
  have hFP : F ≤ P := (twoResidualIn_le E).trans data.group_le
  have hnative : F.subgroupOf P ≤ ⁅F.subgroupOf P, Subgroup.zpowers actor⁆ := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hFP,
      MonoidHom.map_zpowers]
    exact hactors actor hactor hactorNot
  have himage : (F.subgroupOf P).map action ≤
      ⁅(F.subgroupOf P).map action, Subgroup.zpowers (action actor)⁆ := by
    simpa only [Subgroup.map_commutator, MonoidHom.map_zpowers] using
      Subgroup.map_mono (f := action) hnative
  have hlocal := nine_local_residual_image_le_oddCore ctx vertex
    (Γ.act data.x⁻¹ neighbor) ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor)
    action hsurj hkernel
  have hresidual : F ≤ EAt Γ vertex := by
    change twoResidualIn E ≤ Γ.twoResidualAt vertex
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_mono E P data.group_le
  have hnativeResidual : F.subgroupOf P ≤ (EAt Γ vertex).subgroupOf P :=
    fun _ hx => hresidual hx
  exact himage.trans (Subgroup.commutator_mono
    ((Subgroup.map_mono hnativeResidual).trans hlocal) le_rfl)

end Stellmacher.SectionNine
