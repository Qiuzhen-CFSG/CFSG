module
public import Stellmacher.SectionNine.NineThreeQuadraticFixedSubgroup
public import Stellmacher.SectionNine.NineThreeNextModuleCentralizerTwo
public import Stellmacher.SectionNine.NineThreeGeometricExtraction

/-!
# The small fixed subgroup in the first extraction

For the first geometric extraction in (9.3), there is a subgroup W of the
new center's intersection with the initial stabilizer of index at most two
which lies in the initial core and in the original neighboring center. The
extracted group E centralizes W, and C_Za(W) is not contained in the new
stabilizer. The ambient context and actual extraction witnesses are retained.

The mutual quadratic action from (7.5) applies to the new-center intersection.
The fixed-subgroup theorem supplies W and a centralizing initial-center
vector outside the new stabilizer. The outside-generation clause and the
conjugate actor's containment in the new core make E centralize W. Its
residual conjugator therefore fixes W, pulling W from the conjugated center
back into the original center. Since W centralizes V at the first step,
the proved ambient-retaining (7.7)(b) puts W in the first-step core; the
edge centralizer equality (7.4) then puts it in the initial core.

Source: Stellmacher (9.3), printed p.49 / PDF p.39 of
`refs/files/stellmacher-n-group.pdf`, the application of (1.2) immediately
before relation (2). Only critical distance greater than one is used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_first_small_fixed_subgroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (l : ctx.Γ.Vertex) (E A0 : Subgroup G) (actor : G)
    (haZa : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' l
      (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor) :
    let m := ctx.Γ.act data.x⁻¹ l
    ∃ W : Subgroup G, W ≤ ZAt ctx.Γ m ∧ W ≤ QAt ctx.Γ ctx.criticalPath.a ∧
      W ≤ ZAt ctx.Γ l ∧
      Nat.card (ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) ≤ 2 * Nat.card W ∧
      E ≤ Subgroup.centralizer (W : Set G) ∧
      ¬ ZAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (W : Set G) ≤ GAt ctx.Γ m := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act data.x⁻¹ l
  let Y := ZAt Γ m ⊓ GAt Γ cp.a
  have hback : cp.a' ∈ neighborhood Γ m :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp data.neighbor))
  have hZmp : IsPGroup 2 (ZAt Γ m) := by
    let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hback
    exact IsElementaryAbelian.isPGroup 2 (ZAt Γ m)
  have hYp : IsPGroup 2 Y := hZmp.to_le inf_le_left
  have hZaV : ZAt Γ cp.a ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZmVend : ZAt Γ m ≤ VAt Γ cp.a' := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,data.neighbor,rfl⟩
  have hYVend : Y ≤ VAt Γ cp.a' := inf_le_left.trans hZmVend
  have hquad : ⁅⁅ZAt Γ cp.a,Y⁆,Y⁆ = ⊥ := by
    have hq := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb
    exact bot_unique ((Subgroup.commutator_mono
      (Subgroup.commutator_mono hZaV hYVend) hYVend).trans_eq hq.2.2)
  have hZaNot : ¬ ZAt Γ cp.a ≤ GAt Γ m := fun hle => data.actor_outside (hle haZa)
  obtain ⟨W,hWY,hWcard,hWnot⟩ := nine_three_quadratic_fixed_subgroup ctx.toLocalContext
    Y inf_le_right hYp hquad (GAt Γ m) hZaNot
  obtain ⟨a,ha,haNot⟩ := Set.not_subset.mp hWnot
  have hWm : W ≤ ZAt Γ m := hWY.trans inf_le_left
  have hZmQm : ZAt Γ m ≤ Subgroup.centralizer (QAt Γ m : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core m cp.a' hback).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hAxC : (VAt Γ cp.firstStep).conjBy data.x ≤ Subgroup.centralizer (W : Set G) :=
    data.conjugate_core_le.trans (Subgroup.le_centralizer_iff.mp (hWm.trans hZmQm))
  have hEC : E ≤ Subgroup.centralizer (W : Set G) := by
    rw [data.actor_generated a (hZaV ha.1) haNot]
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
  have hVfirstE : VAt Γ cp.firstStep ≤ E := by rw [data.generated]; exact le_sup_left
  have hWC : W ≤ Subgroup.centralizer (VAt Γ cp.firstStep : Set G) :=
    (Subgroup.le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le hVfirstE)
  have hWQfirst : W ≤ QAt Γ cp.firstStep := hWC.trans
    (nine_three_next_module_centralizer_two ctx).2
  have hWT : W ≤ T := hWQfirst.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hWQa : W ≤ QAt Γ cp.a := by
    change W ≤ q Γ cp.a
    rw [← (lemma_seven_four ctx.sectionSeven Γ cp).edge_centralizer]
    exact le_inf hWT (hWC.trans (Subgroup.centralizer_le hZaV))
  exact ⟨W,hWm,hWQa,hWl,hWcard,hEC,hWnot⟩

end Stellmacher.SectionNine
