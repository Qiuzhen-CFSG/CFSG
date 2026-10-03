module
public import Stellmacher.SectionNine.NineThreeOrbitQuadraticFixedSubgroup
public import Stellmacher.SectionNine.NineThreeGeometricExtraction
/-!
# The geometric fixed-subgroup argument in (9.3)

Let a vertex in the initial orbit contribute its center to the actual actor
module of a geometric extraction. Assume that the new-center stabilizer
intersection acts quadratically on that center, and that the actor-module
centralizer lies in the original vertex core. Then a subgroup W of that
intersection has index at most two, lies in both the original core and the
old neighboring center, and is centralized by the extracted group. Its
fixed space in the original center escapes the new stabilizer.

The orbit fixed-subgroup theorem supplies W and an escaping fixed actor.
The geometric generation clause and the conjugate actor's core containment
make the extracted group centralize W. Its residual conjugator fixes W,
which pulls W back into the old neighboring center. Finally W centralizes
the actor module, so the supplied centralizer containment puts it in the
original core. The explicit quadratic and centralizer inputs are proved
from (7.5) and the actual ambient (7.7)(b) in the two consumers.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, the repeated
application of (1.2), `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_geometric_small_fixed_subgroup
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (u0 d l : ctx.Γ.Vertex)
    (hu : IsConjugateVertex ctx.Γ ctx.criticalPath.a u0)
    (V E A0 : Subgroup G) (actor : G)
    (haZu : actor ∈ ZAt ctx.Γ u0)
    (hZuV : ZAt ctx.Γ u0 ≤ V)
    (data : NineThreeGeometricData ctx.Γ d l V E A0 actor)
    (hquad : ⁅⁅ZAt ctx.Γ u0,
      ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0⁆,
      ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓ GAt ctx.Γ u0⁆ = ⊥)
    (hcentralizer : Subgroup.centralizer (V : Set G) ≤ QAt ctx.Γ u0) :
    let m := ctx.Γ.act data.x⁻¹ l
    ∃ W : Subgroup G, W ≤ ZAt ctx.Γ m ∧ W ≤ QAt ctx.Γ u0 ∧
      W ≤ ZAt ctx.Γ l ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ u0 : Subgroup G) ≤ 2 * Nat.card W ∧
      E ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ ZAt ctx.Γ u0 ⊓ Subgroup.centralizer (W : Set G) ≤ GAt ctx.Γ m := by
  let Γ := ctx.Γ
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ u0
  have hback : d ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZmp : IsPGroup 2 (ZAt Γ m) := by
    let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hback
    exact IsElementaryAbelian.isPGroup 2 (ZAt Γ m)
  have hYp : IsPGroup 2 Y := hZmp.to_le inf_le_left
  have hZaNot : ¬ ZAt Γ u0 ≤ GAt Γ m := fun hle => data.actor_outside (hle haZu)
  obtain ⟨W,hWY,hWcard,hWnot⟩ := nine_three_quadratic_fixed_subgroup_at_vertex ctx
    u0 hu Y inf_le_right hYp hquad (GAt Γ m) hZaNot
  obtain ⟨a,ha,haNot⟩ := Set.not_subset.mp hWnot
  have hWm : W ≤ ZAt Γ m := hWY.trans inf_le_left
  have hZmQm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m d hback).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hAxC : (V).conjBy data.x ≤ Subgroup.centralizer (W : Set G) :=
    data.conjugate_core_le.trans (Subgroup.le_centralizer_iff.mp (hWm.trans hZmQm))
  have hEC : E ≤ Subgroup.centralizer (W : Set G) := by
    rw [data.actor_generated a (hZuV ha.1) haNot]
    exact sup_le ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ha.2)) hAxC
  have hxE : data.x ∈ E := (Subgroup.map_subtype_le _) data.residual_mem
  have hWl : W ≤ ZAt Γ l := by
    intro z hz
    have hzmap : z ∈ (ZAt Γ l).map (MulAut.conj data.x).toMonoidHom := by
      have hzm := hWm hz
      change z ∈ CosetGraphContext.z Γ (Γ.act data.x⁻¹ l) at hzm
      rw [z_act,inv_inv] at hzm
      exact hzm
    have hzback := (Subgroup.mem_map_equiv).mp hzmap
    change data.x⁻¹ * z * data.x ∈ ZAt Γ l at hzback
    have hcomm : z * data.x = data.x * z :=
      Subgroup.mem_centralizer_iff.mp (hEC hxE) z hz
    have he : data.x⁻¹ * z * data.x = z := by
      rw [mul_assoc,hcomm,inv_mul_cancel_left]
    exact he ▸ hzback
  have hVfirstE : V ≤ E := by rw [data.generated]; exact le_sup_left
  have hWC : W ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le hVfirstE)
  have hWQu : W ≤ QAt Γ u0 := hWC.trans hcentralizer
  exact ⟨W,hWm,hWQu,hWl,hWcard,hEC,hWnot⟩

end Stellmacher.SectionNine
