module
public import Stellmacher.SectionNine.NineFourCentralCoreIntersectionCommutator
public import Stellmacher.SectionNine.NineFourRemoteCoreActionGeometry
public import Theory.GroupTheory.Commutator.RankOneFixedSupplement

/-!
# The remote-core fixed-subgroup decomposition in central (9.4)

Suppose an actual normalized/enlarged counterexample A centralizes the
initial/remote core intersection. Then A is the join of Z_a and its common
fixed subgroup under Q_remote. That fixed subgroup is larger than the
remote center in the sense that it is not equal to that center. The
centralization input is supplied by the independent central auxiliary
commutator theorem.

Enlargement puts Z_a, and hence the remote center line, inside A. The
remote core has an index-two subgroup centralizing A, while all its
commutators with A lie in the remote order-two center. It acts nontrivially
on Z_a by the transported initial-core geometry. The generic index-two
line-action theorem gives the join decomposition. If the fixed subgroup
were just the remote center, A would equal Z_a and lie in V_next,
contradicting the original counterexample.

Source: Stellmacher (9.4), printed p.52 / PDF p.42, immediately following
the central core-intersection commutator calculation, in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

public theorem nine_four_central_fixed_decomposition
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (henlarged : VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep ≤ data.subgroup)
    (hcomm : ⁅data.subgroup,QAt ctx.Γ ctx.criticalPath.a ⊓
      QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote)⁆ = ⊥) :
    data.subgroup = ZAt ctx.Γ ctx.criticalPath.a ⊔
      (data.subgroup ⊓ Subgroup.centralizer
        (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G)) ∧
    data.subgroup ⊓ Subgroup.centralizer
      (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G) ≠
        ZAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let A := data.subgroup
  let Za := ZAt Γ cp.a
  let Zd := ZAt Γ d
  let Qd := QAt Γ d
  let R0 := QAt Γ cp.a ⊓ Qd
  have hZaVn : Za ≤ VAt Γ cp.firstStep :=
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  have hZaVd : Za ≤ VAt Γ d := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote))
  have hZaA : Za ≤ A := (le_inf hZaVd hZaVn).trans henlarged
  have hZdZa : Zd ≤ Za := ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 d hremote).2
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hremote
  have hdOrbit : IsConjugateVertex Γ cp.firstStep d := ⟨mover,hmover⟩
  have hVdElementary : IsElementaryAbelian 2 (VAt Γ d) := by
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
    change Γ.act (mover : G) cp.firstStep = d at hmover
    rw [← hmover]
    change IsElementaryAbelian 2 (v Γ (Γ.act (mover : G) cp.firstStep))
    rw [v_act]
    exact IsElementaryAbelian.map (MulAut.conj ((mover : G)⁻¹)).toMonoidHom
  let _ := hVdElementary
  let _ : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext
    (congrArg (fun z : VAt Γ d => (z : G)) (mul_comm (⟨a,data.subgroup_le a.property⟩ : VAt Γ d)
      ⟨b,data.subgroup_le b.property⟩))⟩⟩
  have hdData := nine_next_center_commutator_and_kernel ctx hb d hdOrbit
  have hgeometry := nine_four_remote_core_action_geometry ctx hb d hremote
  have hdecomp : A = Za ⊔ (A ⊓ Subgroup.centralizer (Qd : Set G)) :=
    Subgroup.sup_inf_centralizer_eq_of_index_two_line_action A Za Zd Qd R0
      hZaA (hZdZa.trans hZaA) hdData.1
      ((Subgroup.commutator_mono data.subgroup_le le_rfl).trans_eq hdData.2.1)
      inf_le_right hgeometry.1 hcomm hgeometry.2
  refine ⟨hdecomp,?_⟩
  intro heq
  apply data.not_le
  have hAZa : A = Za := by
    rw [heq,sup_eq_left.mpr hZdZa] at hdecomp
    exact hdecomp
  exact hAZa.le.trans hZaVn

end Stellmacher.SectionNine
