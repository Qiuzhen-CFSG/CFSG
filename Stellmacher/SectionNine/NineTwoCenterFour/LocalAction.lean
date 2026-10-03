module

public import Stellmacher.SectionNine.GeneratedContext
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionFiveToSeven.Result7_6
public import Stellmacher.QuotientModuleFixedPoints
public import Stellmacher.QuotientModuleCommutator
public import Stellmacher.QuotientModuleWitness
public import Stellmacher.SectionEight.LocalQuotientCore
public import Stellmacher.SectionOne.Defs

/-!
# Local action inputs to the center-size deduction in (9.2)

The scan-correct noncontainment of the neighboring core intersection makes
the actual Sylow image nontrivial. Thus the faithful initial-center quotient
satisfies the original Section One hypotheses, using local solvability and
the Sylow-center generation theorem for its trivial two-core.

In the commuting critical-pair case, (7.5) identifies the first-step center
with the Sylow omega-center. An explicit commutator containment in that
center therefore makes the projected actor's commutator Sylow-fixed. Finally,
(7.5) gives a trivial residual centralizer in the initial core; the initial
center lies in that core, so its residual-fixed subgroup is trivial. This
last statement supplies the fixed-complement elimination in the later
application of the four-element supports of (1.7).

All quotient constructions retain the supplied witness action. The results
use only the genuine Section Seven data and the commuting critical-pair
condition; they do not descend ambient Hypothesis Two to the graph group.
The commutator-center containment is an explicit premise, not a use of (6.4).

Source: Stellmacher (7.4), (7.5), and (9.2), the latter on printed p.48 /
PDF p.38 of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext
universe u

public theorem nine_two_quotient_hypotheses
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (h : SectionSevenHypotheses G T A B)
    (Γ : CosetGraphContext G T A B) (cp : CriticalPath Γ)
    (m : Γ.Vertex)
    (hnot : ¬ QAt Γ cp.firstStep ⊓ QAt Γ m ≤ QAt Γ cp.a)
    [IsElementaryAbelian 2 (ZAt Γ cp.a)]
    (w : QuotientModuleWitness (GAt Γ cp.a)
      (GAt Γ cp.a ⊓ Subgroup.centralizer (ZAt Γ cp.a : Set G)) (ZAt Γ cp.a)) :
    let _ := w.groupX
    let _ := w.finiteX
    let _ := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
    SectionOne.Hypotheses w.X (ZAt Γ cp.a) := by
  let := w.groupX
  let := w.finiteX
  let := MulDistribMulAction.compHom (ZAt Γ cp.a) w.action
  let P := stabilizer Γ cp.a
  have hlocal := (SevenSix.edge_local_data h Γ cp).1
  let : Group.IsSolvable P := hlocal.2
  obtain ⟨_, sylow, hsylow⟩ := hlocal.1.1.2.1
  have hTP : T ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hnative : (sylow : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hsylow
  let quotientSylow := sylow.mapSurjective w.surjective
  have hnontrivial : (quotientSylow : Subgroup w.X) ≠ ⊥ := by
    intro hbot
    apply hnot
    intro actor hactor
    have hactorT : actor ∈ T :=
      (SevenSix.local_cores_le_edge_sylow h Γ cp).2 hactor.1
    let lift : P := ⟨actor, hTP hactorT⟩
    have hlift : lift ∈ (sylow : Subgroup P) := by
      rw [hnative]
      exact hactorT
    have hkernel : lift ∈ w.projection.ker := by
      have himage : w.projection lift ∈ (quotientSylow : Subgroup w.X) :=
        Subgroup.mem_map_of_mem w.projection hlift
      rwa [hbot, Subgroup.mem_bot] at himage
    rw [w.kernel_eq] at hkernel
    change actor ∈ q Γ cp.a
    rw [← (lemma_seven_four h Γ cp).edge_centralizer]
    exact ⟨hactorT, hkernel.2⟩
  let : Nontrivial quotientSylow :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hnontrivial
  obtain ⟨exponent, hpositive, hcard⟩ :=
    quotientSylow.isPGroup'.nontrivial_iff_card.mp inferInstance
  have heven : Even (Nat.card w.X) := by
    apply even_iff_two_dvd.mpr
    apply (show 2 ∣ Nat.card quotientSylow by
      rw [hcard]
      exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpositive)).trans
    exact Subgroup.card_subgroup_dvd_card _
  exact ⟨Group.isSolvable_of_surjective w.surjective, heven,
    w.action_faithful, SectionEight.local_quotient_twoCore_eq_bot Γ cp.a w⟩

public theorem nine_two_commutator_fixed_by_sylow
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (m : ctx.Γ.Vertex)
    (hcenter : ⁅ZAt ctx.Γ ctx.criticalPath.a,
      QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    commutatorAction
      (((QAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ m).subgroupOf
        (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)
      (ZAt ctx.Γ ctx.criticalPath.a) ≤
    FixedPoints.subgroup
      ((T.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)
      (ZAt ctx.Γ ctx.criticalPath.a) := by
  let := w.groupX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hTP : T ≤ stabilizer Γ cp.a := cp.S_le_edge_stabilizers.trans inf_le_left
  have hactor : q Γ cp.firstStep ⊓ q Γ m ≤ stabilizer Γ cp.a :=
    (inf_le_left.trans (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2).trans hTP
  have hmap := w.commutatorAction_image_map_subtype _ hactor
  apply (Subgroup.map_le_map_iff_of_injective (z Γ cp.a).subtype_injective).mp
  rw [w.fixedPoints_map_subtype T hTP]
  apply le_inf (Subgroup.map_subtype_le _)
  rw [hmap]
  apply hcenter.trans
  change z Γ cp.firstStep ≤ Subgroup.centralizer (T : Set G)
  rw [(lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center.1]
  exact (SevenSix.omegaOneCenter_le_centerAmbient _).trans
    (SevenSix.centerAmbient_le_centralizer _)

public theorem nine_two_residual_fixed_eq_bot
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    FixedPoints.subgroup
      (((EAt ctx.Γ ctx.criticalPath.a).subgroupOf
        (GAt ctx.Γ ctx.criticalPath.a)).map w.projection)
      (ZAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
  let := w.groupX
  let := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hcenter : z Γ cp.a ≤ q Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hresidual : e Γ cp.a ≤ stabilizer Γ cp.a := by
    rw [CosetGraphContext.e, Γ.twoResidualAt_def]
    exact Subgroup.map_subtype_le _
  apply Subgroup.map_injective (z Γ cp.a).subtype_injective
  rw [w.fixedPoints_map_subtype (e Γ cp.a) hresidual, Subgroup.map_bot]
  apply le_bot_iff.mp
  exact (inf_le_inf_right _ hcenter).trans_eq
    (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).centralizer_residual

end Stellmacher.SectionNine
