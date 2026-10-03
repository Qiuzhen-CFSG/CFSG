module
public import Stellmacher.SectionNine.NineFourReduction

/-!
# The normalized actor closure fixes the moved module

If the original actor centralizes a remote module and a conjugator moves
that vertex next to the initial vertex, the literal initial-core conjugate
closure of the conjugated actor centralizes the moved module. The initial
core normalizes that closure. These are the action properties of T used in
the noncentral auxiliary-subgroup case of (9.4).

Conjugation transports the original centralizer membership. By (7.3), the
initial core lies in the moved vertex stabilizer and hence normalizes its
module. A module normalizer normalizes its centralizer, so all generating
conjugates remain in that centralizer. Multiplying the conjugating elements
shows directly that the initial core normalizes their generated closure.
No critical-distance, transvection or counterexample assumption is needed
for these two action properties.

Source: Stellmacher (9.4), printed p.51/PDF p.41, the definition of T and
the assertion that it centralizes the moved-remote module, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_four_actor_closure_action
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (remote : ctx.Γ.Vertex) (actor : G)
    (hcentral : actor ∈ Subgroup.centralizer (VAt ctx.Γ remote : Set G))
    (conjugator : G)
    (hremote : ctx.Γ.act conjugator remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a) :
    let T0 := conjugateClosure (Subgroup.zpowers (conjugator⁻¹*actor*conjugator))
      (QAt ctx.Γ ctx.criticalPath.a)
    T0 ≤ Subgroup.centralizer (VAt ctx.Γ (ctx.Γ.act conjugator remote) : Set G) ∧
      QAt ctx.Γ ctx.criticalPath.a ≤ Subgroup.normalizer (T0 : Set G) := by
  let Γ := ctx.Γ
  let Qa := QAt Γ ctx.criticalPath.a
  let d := Γ.act conjugator remote
  let Vd := VAt Γ d
  let u := conjugator⁻¹*actor*conjugator
  let U := Subgroup.zpowers u
  let T0 := conjugateClosure U Qa
  have hu : u ∈ Subgroup.centralizer (Vd : Set G) := by
    have hmap := Subgroup.map_centralizer_le_centralizer_image
      (VAt Γ remote : Set G) (MulAut.conj conjugator⁻¹).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj conjugator⁻¹).toMonoidHom hcentral)
    change (MulAut.conj conjugator⁻¹) actor ∈
      Subgroup.centralizer ((VAt Γ remote).map
        (MulAut.conj conjugator⁻¹).toMonoidHom : Set G) at hmap
    change u ∈ Subgroup.centralizer (v Γ (Γ.act conjugator remote) : Set G)
    rw [v_act]
    simpa only [u,MulAut.conj_apply,inv_inv] using hmap
  have hQaVd : Qa ≤ Subgroup.normalizer (Vd : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core ctx.criticalPath.a d
      hremote default).2.2.trans (stabilizer_le_normalizer_v Γ d)
  have hnormal : Subgroup.normalizer (Vd : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (Vd : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (Vd : Set G))
  constructor
  · apply (Subgroup.closure_le _).mpr
    rintro point ⟨mover,element,rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp ((hQaVd.trans hnormal) mover.property) element).mp
      ((Subgroup.zpowers_le.mpr hu) element.property)
  · change Qa ≤ Subgroup.normalizer (conjugateClosure U Qa : Set G)
    rw [conjugateClosure,Subgroup.le_normalizer_closure_iff]
    intro mover hmover point hpoint
    obtain ⟨earlier,element,rfl⟩ := hpoint
    apply Subgroup.subset_closure
    refine ⟨⟨mover*(earlier:G),Qa.mul_mem hmover earlier.property⟩,element,?_⟩
    change mover * ((earlier:G)*(element:G)*(earlier:G)⁻¹) * mover⁻¹ =
      (mover*(earlier:G))*(element:G)*(mover*(earlier:G))⁻¹
    group

end Stellmacher.SectionNine
