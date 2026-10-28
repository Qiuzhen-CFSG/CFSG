module
public import Stellmacher.SectionNine.NineInitialEdgeCoreProduct
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration
public import Stellmacher.SectionNine.NineNextFaithfulQuotient
public import Stellmacher.SectionNine.NineSevenNormalityObstructions

/-!
# The terminal module intersection is normalized by the middle stabilizer

At critical length greater than one, the intersection of the terminal module
and the module two steps before it contains the penultimate center, lies in
the penultimate core, and is normalized by the penultimate stabilizer.

Both neighboring cores normalize the intersection: their commutators lie in
the corresponding center lines, which belong to the intersection. The
penultimate core fixes both neighbor vertices and also normalizes the
intersection. The actual residual lies in the two neighbor-core join; the
transported initial adjacent-core product and residual/Sylow generation then
give normalization by the entire penultimate stabilizer. Core containment
follows from critical minimality at distance two and oddness of the length.

This is the invariance calculation used in Stellmacher (9.4)(6), applied to
the terminal two-arc for the centralizing-conjugator step in (9.9), printed
p.56/PDF p.46 of `refs/files/stellmacher-n-group.pdf`. No intersection
cardinality or center-containment conclusion of (9.9) is assumed here.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_terminal_intersection_core_normalized
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) :
    let penultimate := ctx.criticalPath.path ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let preterminal := ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    let I := VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ preterminal
    ZAt ctx.Γ penultimate ≤ I ∧ I ≤ QAt ctx.Γ penultimate ∧
      GAt ctx.Γ penultimate ≤ Subgroup.normalizer (I : Set G) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let P := GAt Γ penultimate
  let Qm := QAt Γ penultimate
  let Qt := QAt Γ cp.a'
  let Qr := QAt Γ preterminal
  let I := VAt Γ cp.a' ⊓ VAt Γ preterminal
  let Z := ZAt Γ penultimate
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb preterminal hpath)
  have hZI : Z ≤ I := le_inf
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hterminalAdj))
    (nine_seven_neighbor_center_le_module Γ (Γ.adjacent_symm hpreAdj))
  obtain ⟨alignment,halign,hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hmOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  have htOrbit : IsConjugateVertex Γ cp.firstStep cp.a' := ⟨alignment,hterminal⟩
  have hrOrbit : IsConjugateVertex Γ cp.firstStep preterminal :=
    nine_five_penultimate_neighbor_orbit ctx.toLocalContext preterminal hpreAdj
  have hcenters := (nine_seven_center_join ctx penultimate hmOrbit).2
  have hZt : ZAt Γ cp.a' ≤ Z :=
    (hcenters cp.a' ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj)).2
  have hZr : ZAt Γ preterminal ≤ Z :=
    (hcenters preterminal ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj)).2
  have hQtI : Qt ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono inf_le_left le_rfl).trans_eq
        (nine_next_center_commutator_and_kernel ctx hb cp.a' htOrbit).2.1).trans
          (hZt.trans hZI))
  have hQrI : Qr ≤ Subgroup.normalizer (I : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono inf_le_right le_rfl).trans_eq
        (nine_next_center_commutator_and_kernel ctx hb preterminal hrOrbit).2.1).trans
          (hZr.trans hZI))
  have hQmTerminal : Qm ≤ GAt Γ cp.a' :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate cp.a'
      ((mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj) default).2.2
  have hQmPre : Qm ≤ GAt Γ preterminal :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core penultimate preterminal
      ((mem_neighborhood_iff_adjacent Γ).mpr hpreAdj) default).2.2
  have hQmI : Qm ≤ Subgroup.normalizer (I : Set G) :=
    (le_inf (hQmTerminal.trans (stabilizer_le_normalizer_v Γ cp.a'))
      (hQmPre.trans (stabilizer_le_normalizer_v Γ preterminal))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hfour := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hEI : EAt Γ penultimate ≤ Subgroup.normalizer (I : Set G) :=
    (nine_five_penultimate_residual_le_join_of_initial_four ctx hfour hb preterminal hpath).trans
      (sup_le hQrI hQtI)
  let equiv := MulAut.conj alignment⁻¹
  have hQa : (QAt Γ cp.a).map equiv.toMonoidHom = Qm := by rw [← q_act,halign]
  have hQn : (QAt Γ cp.firstStep).map equiv.toMonoidHom = Qt := by rw [← q_act,hterminal]
  have hGa : (GAt Γ cp.a).map equiv.toMonoidHom = P := by
    change conjugateBy (stabilizer Γ cp.a) alignment⁻¹ = _
    rw [← stabilizer_act,halign]
  have hEa : (EAt Γ cp.a).map equiv.toMonoidHom = EAt Γ penultimate := by
    simp only [EAt,CosetGraphContext.e,Γ.twoResidualAt_def]
    change (twoResidualIn (GAt Γ cp.a)).map equiv.toMonoidHom = twoResidualIn P
    rw [← twoResidualIn_map_equiv,hGa]
  have hinitial := (nine_initial_edge_core_product ctx hb).1
  have hTa : QAt Γ cp.a ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hTn : QAt Γ cp.firstStep ≤ T := (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2
  have hTjoin : T = QAt Γ cp.a ⊔ QAt Γ cp.firstStep :=
    le_antisymm (cp.S_le_edge_stabilizers.trans_eq hinitial.symm) (sup_le hTa hTn)
  have hTmap : T.map equiv.toMonoidHom = Qm ⊔ Qt := by
    rw [hTjoin,Subgroup.map_sup,hQa,hQn]
  have hgenInitial : EAt Γ cp.a ⊔ T = GAt Γ cp.a := by
    change e Γ cp.a ⊔ T = stabilizer Γ cp.a
    rw [CosetGraphContext.e,Γ.twoResidualAt_def]
    exact twoResidualIn_sup_sylow (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hgen : EAt Γ penultimate ⊔ (Qm ⊔ Qt) = P := by
    have hh := congrArg (fun J : Subgroup G => J.map equiv.toMonoidHom) hgenInitial
    rw [Subgroup.map_sup,hEa,hTmap,hGa] at hh
    exact hh
  have hb2 : 2 < cp.length := by
    have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hodd
    change 1 < cp.length at hb
    obtain ⟨k,hk⟩ := hodd
    omega
  refine ⟨hZI,?_,?_⟩
  · exact inf_le_left.trans
      ((nine_seven_neighbor_module_le_neighborhood Γ hterminalAdj).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 penultimate))
  · change P ≤ Subgroup.normalizer (I : Set G)
    rw [← hgen]
    exact sup_le hEI (sup_le hQmI hQtI)

end Stellmacher.SectionNine
