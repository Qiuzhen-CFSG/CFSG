module
public import Stellmacher.SectionNine.NineFourActorClosureAction
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The adjacent-module intersection centralizes the core intersection

Suppose the literal initial/remote core intersection in (9.4) lies in the
join of the actor closure and the next core. Then the next/remote module
intersection centralizes it. This is the geometric consequence of the
source's actor-cover assertion, shared by both auxiliary branches.

The actor closure centralizes the remote module. The next core's
commutators with the next module lie in the next center, so the cover
places all relevant commutators in that center. Independently, the remote
core bounds them by the remote center. These two centers are disjoint
lines in the initial center, by the post-(9.3) center splitting, and the
commutator is therefore trivial. The cover is an explicit input supplied
by the independent factor-image argument.

Source: Stellmacher (9.4), printed p.51/PDF p.41, the displayed
centralization preceding relation (6), and its reuse on printed p.52.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem sup_commutator_le {G : Type*} [Group G]
    (P U W D Z : Subgroup G) (hPZ : P ≤ Subgroup.normalizer Z)
    (hUP : U ≤ P) (hWP : W ≤ P)
    (hUD : ⁅U,D⁆ ≤ Z) (hWD : ⁅W,D⁆ ≤ Z) : ⁅U ⊔ W,D⁆ ≤ Z :=
  (Subgroup.commutator_mono (sup_le
    (Subgroup.le_commutatorPreimage hUP hUD)
    (Subgroup.le_commutatorPreimage hWP hWD)) le_rfl).trans
      (Subgroup.commutator_commutatorPreimage_le P D Z hPZ)

public theorem nine_four_intersection_centralizes_core_of_actor_cover
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex) (actor : G)
    (hcentral : actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act conjugator remote ≠ ctx.criticalPath.firstStep)
    (hcover : QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act conjugator remote) ≤
      conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator))
        (QAt ctx.Γ ctx.criticalPath.a) ⊔ QAt ctx.Γ ctx.criticalPath.firstStep) :
    ⁅VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ (ctx.Γ.act conjugator remote),
      QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ (ctx.Γ.act conjugator remote)⁆ = ⊥ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act conjugator remote
  let U := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let I := U ⊓ VAt Γ d
  let R := QAt Γ cp.a ⊓ QAt Γ d
  let C := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator)) (QAt Γ cp.a)
  let P := GAt Γ cp.firstStep
  have hCn := (nine_four_actor_closure_action ctx.toLocalContext remote actor hcentral
    conjugator hremote).1
  have hCI : ⁅C,I⁆ ≤ Z := by
    have hc : C ≤ Subgroup.centralizer (I : Set G) :=
      hCn.trans (Subgroup.centralizer_le (show (I:Set G) ⊆ VAt Γ d from inf_le_right))
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le
  have hQnP : QAt Γ cp.firstStep ≤ P := by
    change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hQI : ⁅QAt Γ cp.firstStep,I⁆ ≤ Z := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).2.1
  have hCZ : C ≤ Subgroup.normalizer Z := by
    have hZnVd : Z ≤ VAt Γ d :=
      (((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 cp.firstStep
        ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2).trans
          (nine_seven_neighbor_center_le_module Γ
            (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))
    exact hCn.trans ((Subgroup.centralizer_le hZnVd).trans
      (Subgroup.centralizer_le_normalizer _))
  have hQZ : QAt Γ cp.firstStep ≤ Subgroup.normalizer Z :=
    hQnP.trans (stabilizer_le_normalizer_z Γ cp.firstStep)
  have hRZn : ⁅R,I⁆ ≤ Z := by
    have hcover' : R ≤ C ⊔ QAt Γ cp.firstStep := hcover
    exact (Subgroup.commutator_mono hcover' (show I ≤ I from le_rfl)).trans
      (sup_commutator_le (Subgroup.normalizer Z) C (QAt Γ cp.firstStep) I Z
        le_rfl hCZ hQZ hCI hQI)
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hremote
  have hRZd : ⁅I,R⁆ ≤ ZAt Γ d :=
    (Subgroup.commutator_mono inf_le_right inf_le_right).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb d ⟨mover,hmover⟩).2.1
  have hdis := (nine_three_center_split ctx hb ⟨1,Γ.act_one _⟩ cp.firstStep_adj
    ((mem_neighborhood_iff_adjacent Γ).mp hremote) hne.symm).2.1
  apply le_bot_iff.mp
  rw [← hdis.eq_bot]
  exact le_inf (by simpa only [Subgroup.commutator_comm] using hRZn) hRZd

end Stellmacher.SectionNine
