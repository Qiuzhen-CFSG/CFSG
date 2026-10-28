module
public import Stellmacher.SectionNine.LemmaNineThree
public import Stellmacher.SectionNine.NineSevenShiftedIntersections
public import Stellmacher.SectionNine.NineSevenCenterJoin
public import Stellmacher.SectionNine.NineFourAuxiliaryCore

/-!
# Central auxiliary actors lie in the initial core

Let A lie in a remote neighbor module and contain its intersection with the
first-step module, but not lie in the first-step module. Any subgroup R of
the first-step core with [A,R] contained in the first-step center lies in
the initial vertex core. The final specialization extracts source relation
(7) from the all-central auxiliary modules and supplies their actual core
containment using the local residual-core geometry. This applies both to the literal auxiliary core
in the all-central case of (9.4) and to the final residual core.

The common initial center lies in the enlarged A, so the commutator bound
makes R normalize A. If R escapes the initial core, the cubic local action
moves the remote neighbor to the third neighbor while fixing the first step.
Thus A lies in the remote/third module intersection. The enlarged hypothesis
places the remote/first-step intersection inside that intersection. Two-arc
transitivity identifies their orders, forcing equality and then A to lie
in the first-step module, a contradiction.

The proof uses the actual ambient context and graph action; neither a
factor decomposition nor a fixed-space equality is assumed. Source:
Stellmacher (9.4), printed pp.51–52, the sentence following (7) and the
final inference using (7.6)(b), in refs/files/stellmacher-n-group.pdf.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem exists_third_neighbor
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (middle left right : Γ.Vertex)
    (hleft : Γ.adjacent middle left) (hright : Γ.adjacent middle right)
    (hdegree : Nat.card {neighbor // Γ.adjacent middle neighbor} = 3) :
    ∃ third, Γ.adjacent middle third ∧ third ≠ left ∧ third ≠ right := by
  classical
  let Points := {neighbor // Γ.adjacent middle neighbor}
  let _ : Finite Γ.Vertex := Γ.finiteVertex
  let _ : Fintype Points := Fintype.ofFinite Points
  by_contra! hnone
  have hcover : (Finset.univ : Finset Points) ⊆
      {⟨left, hleft⟩, ⟨right, hright⟩} := by
    intro point hpoint
    have hc : point.val = left ∨ point.val = right := by
      by_cases hl : point.val = left
      · exact Or.inl hl
      · exact Or.inr (hnone point point.property hl)
    rcases hc with hc | hc
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext hc))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext hc)))
  have hcard := Finset.card_le_card hcover
  have hpair : ({(⟨left,hleft⟩ : Points), ⟨right,hright⟩} : Finset Points).card ≤ 2 :=
    by
      by_cases heq : (⟨left,hleft⟩ : Points) = ⟨right,hright⟩
      · simp [heq]
      · simp [heq]
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hdegree] at hcard
  omega

public theorem nine_four_central_actor_le_initial_core
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (A R : Subgroup G)
    (hA : A ≤ VAt ctx.Γ remote)
    (hintersection : VAt ctx.Γ remote ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ≤ A)
    (hnot : ¬ A ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hR : R ≤ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hcomm : ⁅A, R⁆ ≤ ZAt ctx.Γ ctx.criticalPath.firstStep) :
    R ≤ QAt ctx.Γ ctx.criticalPath.a := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let V := VAt Γ cp.firstStep
  let D := VAt Γ remote
  let I := D ⊓ V
  have haRemote : Γ.adjacent cp.a remote := (mem_neighborhood_iff_adjacent Γ).mp hremote
  have hZaD : ZAt Γ cp.a ≤ D :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm haRemote)
  have hZaV : ZAt Γ cp.a ≤ V :=
    nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm cp.firstStep_adj)
  have hZaA : ZAt Γ cp.a ≤ A := (le_inf hZaD hZaV).trans hintersection
  have hZnZa : ZAt Γ cp.firstStep ≤ ZAt Γ cp.a :=
    ((nine_seven_center_join ctx cp.a ⟨1, Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2
  have hRA : R ≤ Subgroup.normalizer A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (hZnZa.trans hZaA))
  by_contra hRnot
  have hmodel := (lemma_nine_three_ambient ctx hb cp.a ⟨1, Γ.act_one _⟩).1
  have hcubic := cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven cp.a hmodel
  obtain ⟨third, hthird, hthirdN, hthirdD⟩ := exists_third_neighbor Γ cp.a
    cp.firstStep remote cp.firstStep_adj haRemote hcubic.degree
  have hRedge : R ≤ GAt Γ cp.a ⊓ GAt Γ cp.firstStep :=
    hR.trans ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans cp.S_le_edge_stabilizers)
  obtain ⟨mover, hmove⟩ := hcubic.punctured_transitivity cp.firstStep cp.firstStep_adj
    R hRedge hRnot ⟨hremote, hne⟩
    ⟨(mem_neighborhood_iff_adjacent Γ).mpr hthird, hthirdN⟩
  have hAthird : A ≤ VAt Γ third := by
    have hmap := Subgroup.map_mono (f := (MulAut.conj (mover : G)⁻¹).toMonoidHom) hA
    have hnormal := Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (hRA (R.inv_mem mover.property))
    change A.map (MulAut.conj (mover : G)⁻¹).toMonoidHom = A at hnormal
    rw [hnormal] at hmap
    change A ≤ (v Γ remote).map _ at hmap
    rw [← v_act, hmove] at hmap
    exact hmap
  have hIj : I ≤ D ⊓ VAt Γ third :=
    hintersection.trans (le_inf hA hAthird)
  obtain ⟨carrier, hcarrierD, _, hcarrierN⟩ := nine_seven_two_arc_transport
    ctx.sectionSeven Γ haRemote cp.firstStep_adj hne haRemote hthird hthirdD.symm
    ⟨1, Γ.act_one _⟩ hmodel
  have hcard : Nat.card I = Nat.card (D ⊓ VAt Γ third : Subgroup G) := by
    have hmap : I.map (MulAut.conj carrier⁻¹).toMonoidHom = D ⊓ VAt Γ third := by
      change ((v Γ remote) ⊓ v Γ cp.firstStep).map _ = _
      rw [Subgroup.map_inf _ _ _ (MulAut.conj carrier⁻¹).injective,
        ← v_act, ← v_act, hcarrierD, hcarrierN]
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj carrier⁻¹).injective]
  have hIe : I = D ⊓ VAt Γ third := Subgroup.eq_of_le_of_card_ge hIj hcard.ge
  exact hnot ((le_inf hA hAthird).trans (hIe.ge.trans inf_le_right))

/-- The literal all-central auxiliary subgroup lies in the initial core. -/
public theorem nine_four_all_central_core_le
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length)
    (remote : ctx.Γ.Vertex)
    (hremote : remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : remote ≠ ctx.criticalPath.firstStep)
    (actor : G) (hactor : actor ∈ GAt ctx.Γ ctx.criticalPath.firstStep)
    (A : Subgroup G)
    (hA : A ≤ VAt ctx.Γ remote)
    (hintersection : VAt ctx.Γ remote ⊓ VAt ctx.Γ ctx.criticalPath.firstStep ≤ A)
    (hnot : ¬ A ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcentral : ∀ y : G, y ∈ A →
      let F := (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
        Subgroup.zpowers actor
      let Q := twoCoreIn (twoResidualIn F)
      (⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) =
        ZAt ctx.Γ ctx.criticalPath.firstStep) :
    twoCoreIn (twoResidualIn
      ((QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
        Subgroup.zpowers actor)) ≤ QAt ctx.Γ ctx.criticalPath.a := by
  let Q := twoCoreIn (twoResidualIn
    ((QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ remote) ⊔
      Subgroup.zpowers actor))
  have hQ : Q ≤ QAt ctx.Γ ctx.criticalPath.firstStep :=
    (nine_four_auxiliary_core_geometry ctx hb remote actor hactor).2.1
  apply nine_four_central_actor_le_initial_core ctx hb remote hremote hne A Q
    hA hintersection hnot hQ
  apply Subgroup.commutator_le.mpr
  intro y hy q hq
  have hs : ⁅Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep, Q⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := le_sup_left.trans_eq (hcentral y hy)
  exact hs (Subgroup.commutator_mem_commutator
    (show y ∈ Subgroup.zpowers y ⊔ VAt ctx.Γ ctx.criticalPath.firstStep from
      Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hq)

end Stellmacher.SectionNine
