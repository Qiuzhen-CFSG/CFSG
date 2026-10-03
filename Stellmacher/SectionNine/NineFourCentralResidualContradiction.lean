module
public import Stellmacher.SectionNine.NineFourCoreDisplacementIndex
public import Stellmacher.SectionNine.NineFourCentralCoreContainment
public import Stellmacher.SectionNine.NineFourNormalizedEnlarged
public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Stellmacher.ResidualCoreCommutator
public import Theory.GroupAction.SmallQuotientCentralization
public import Theory.ThreeSubgroups

/-!
# The final residual-core contradiction in central (9.4)

For a normalized and enlarged counterexample, suppose the two neighboring
modules intersect in the initial center and the next residual acts trivially
on A V_next modulo V_next. These exact source inputs contradict the
index-at-least-four intersection bound.

Put Q = O₂(E_next). Its residual-perfect commutator identity makes every
noncentral cyclic displacement module W active under E_next. The generalized
source-(3) bound gives |W| ≤ 2|W ∩ V_remote|, while a quotient of order at most
two has trivial automorphism action, forcing |W| ≥ 8. Thus W contains the
initial center, and residual spanning forces W = V_next, contrary to the
intersection bound. Every displacement is therefore central. The actual
cubic containment theorem then puts Q in the initial core, contradicting
(7.6)(b).

This is the last paragraph of Stellmacher (9.4), printed p.52 / PDF p.42 of
`refs/files/stellmacher-n-group.pdf`. The subscript in the final auxiliary
construction is O₂(E_next), as in the scan. The preceding fixed-subgroup
comparison and residual-normalization transfer are separate prerequisites.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

public theorem nine_four_central_residual_contradiction
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A0 B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A0 B)
    (hb : 1 < ctx.criticalPath.length) (data : NineFourCounterexample ctx)
    (hremote : ctx.Γ.act data.conjugator data.remote ∈ Neighborhood ctx.Γ ctx.criticalPath.a)
    (hne : ctx.Γ.act data.conjugator data.remote ≠ ctx.criticalPath.firstStep)
    (henlarged : VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓
      VAt ctx.Γ ctx.criticalPath.firstStep ≤ data.subgroup)
    (hlarge : 4 * Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Subgroup G) ≤
        Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep))
    (hintersection : VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) = ZAt ctx.Γ ctx.criticalPath.a)
    (hrescomm : ⁅data.subgroup ⊔ VAt ctx.Γ ctx.criticalPath.firstStep,
      EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  let Z := ZAt Γ cp.firstStep
  let Za := ZAt Γ cp.a
  let A := data.subgroup
  let E := EAt Γ cp.firstStep
  let Q := twoCoreIn E
  have hEP : E ≤ P := by
    change Γ.twoResidualAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hEeq : E = twoResidualIn P := by
    change Γ.twoResidualAt cp.firstStep = _
    exact Γ.twoResidualAt_def _
  have hQnext : Q ≤ QAt Γ cp.firstStep := by
    change twoCoreIn (e Γ cp.firstStep) ≤ q Γ cp.firstStep
    rw [CosetGraphContext.e,Γ.twoResidualAt_def,q,Γ.twoCoreAt_def,residual_core_eq_inter_core]
    exact inf_le_right
  have hodd : Odd (Nat.card (E ⧸ pCore 2 E)) := by
    rw [hEeq]
    exact local_residual_core_quotient_odd ctx.sectionSeven Γ cp.firstStep cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj)) P le_rfl
  have hperfect : BenderSuzuki.External.hktPResidual 2 E = ⊤ := by
    rw [hEeq]
    exact twoResidualAmbient_has_top_twoResidual P
  have hcoreComm : Q = ⁅Q,E⁆ := by
    have hh := congrArg (Subgroup.map E.subtype)
      (twoCore_eq_commutator_of_residual_perfect hperfect hodd)
    rw [Subgroup.map_commutator,← MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh
  have hEQ : E ≤ Subgroup.normalizer (Q:Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (twoCoreIn_le E)).mp (twoCoreIn_normal E)
  have hEZ : E ≤ Subgroup.normalizer (Z:Set G) :=
    hEP.trans (stabilizer_le_normalizer_z Γ cp.firstStep)
  have hVQ : ⁅V,Q⁆ ≤ Z :=
    (Subgroup.commutator_mono le_rfl hQnext).trans_eq
      (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).2.1
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_commutator_and_kernel ctx hb cp.firstStep ⟨1,Γ.act_one _⟩).1
  have hZV : Z ≤ V :=
    (((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 cp.firstStep
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)).2).trans
        (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1
  let _ : IsElementaryAbelian 2 V :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
  have hZaCard : Nat.card Za = 4 := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hdistance : Γ.distance d cp.firstStep = 2 := nine_four_moved_distance Γ cp.firstStep
    data.remote data.actor data.conjugator data.actor_mem data.conjugator_mem data.distance
  have hb2 : 2 < cp.length := by
    have hoddPath := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
    change Odd cp.length at hoddPath
    obtain ⟨k,hk⟩ := hoddPath
    change 1 < cp.length at hb
    omega
  have hQaP : QAt Γ cp.a ≤ P :=
    ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1.trans cp.S_le_edge_stabilizers).trans
      inf_le_right
  have hAP : A ≤ P := data.subgroup_le.trans
    (((nine_seven_neighbor_module_le_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mp hremote)).trans
        (nine_seven_neighborhood_le_own_core ctx.toLocalContext hb2 cp.a)).trans hQaP)
  have hVP : V ≤ P := (nine_seven_module_le_own_core ctx.toLocalContext hb cp.firstStep).trans
    (by change Γ.twoCoreAt cp.firstStep ≤ Γ.vertexStabilizer cp.firstStep
        rw [Γ.twoCoreAt_def]
        exact twoCoreIn_le _)
  have hall (y : G) (hy : y ∈ A) :
      (⁅Subgroup.zpowers y ⊔ V,Q⁆ ⊔ Z : Subgroup G) = Z := by
    let C := Subgroup.zpowers y ⊔ V
    let W := ⁅C,Q⁆ ⊔ Z
    have hCE : ⁅C,E⁆ ≤ V :=
      (Subgroup.commutator_mono (sup_le_sup (Subgroup.zpowers_le.mpr hy) le_rfl) le_rfl).trans hrescomm
    have hCQ : ⁅C,Q⁆ ≤ V := (Subgroup.commutator_mono le_rfl (twoCoreIn_le E)).trans hCE
    have hCP : C ≤ P := sup_le ((Subgroup.zpowers_le.mpr hy).trans hAP) hVP
    have hEC : E ≤ Subgroup.normalizer (C:Set G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mpr (hCE.trans le_sup_right)
    have hEW : E ≤ Subgroup.normalizer (W:Set G) := by
      intro mover hmover
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      change (⁅C,Q⁆ ⊔ Z).map (MulAut.conj mover).toMonoidHom = ⁅C,Q⁆ ⊔ Z
      have hc : C.map (MulAut.conj mover).toMonoidHom = C :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEC hmover)
      have hq : Q.map (MulAut.conj mover).toMonoidHom = Q :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEQ hmover)
      have hz : Z.map (MulAut.conj mover).toMonoidHom = Z :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEZ hmover)
      rw [Subgroup.map_sup,Subgroup.map_commutator,hc,hq,hz]
    have hWV : W ≤ V := sup_le hCQ hZV
    have hsmall : Nat.card W ≤ 2 * Nat.card (W ⊓ VAt Γ d : Subgroup G) :=
      nine_four_core_displacement_index ctx hb d hremote hdistance Q hQnext y
        (data.subgroup_le hy) hCQ
    by_contra hnoncentral
    have hactive : ¬ ⁅W,E⁆ ≤ Z := by
      intro hWE
      have htriple : ⁅⁅Q,E⁆,C⁆ ≤ Z := by
        apply Subgroup.commutator_commutator_le_of_rotate_of_le_normalizer
          ((twoCoreIn_le E).trans hEZ) hEZ
          (hCP.trans (stabilizer_le_normalizer_z Γ cp.firstStep))
        · have hECbound : ⁅E,C⁆ ≤ V := by simpa only [Subgroup.commutator_comm] using hCE
          exact (Subgroup.commutator_mono hECbound le_rfl).trans hVQ
        · exact (Subgroup.commutator_mono (show ⁅C,Q⁆ ≤ W from le_sup_left) le_rfl).trans hWE
      have hCQZ : ⁅C,Q⁆ ≤ Z := by
        rw [← hcoreComm,Subgroup.commutator_comm] at htriple
        exact htriple
      exact hnoncentral (sup_eq_right.mpr hCQZ)
    have hlargeW : 8 ≤ Nat.card W := by
      by_contra hnot
      have htwoW : IsPGroup 2 W := (IsElementaryAbelian.isPGroup 2 V).to_le hWV
      obtain ⟨n,hn⟩ := htwoW.exists_card_eq
      have hnle : n ≤ 2 := by
        by_contra! hnlarge
        have hp : 2^3 ≤ 2^n := Nat.pow_le_pow_right (by decide) hnlarge
        omega
      have hWle : Nat.card W ≤ 4 := by
        rw [hn]
        exact Nat.pow_le_pow_right (by decide) hnle
      let _ : IsMulCommutative W := ⟨⟨fun a b => Subtype.ext
        (setLike_mul_comm (s:=V) (hWV a.property) (hWV b.property))⟩⟩
      let hNW : (Z.subgroupOf W).Normal := inferInstance
      let _ := hNW
      have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf W)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show Z ≤ W from le_sup_right)).toEquiv,hZcard] at hcount
      have hquotient : Nat.card (W ⧸ Z.subgroupOf W) ≤ 2 := by omega
      exact hactive (Subgroup.commutator_le_of_normalized_quotient_card_le_two
        E W Z hEW hEZ hNW hquotient)
    have hI : W ⊓ VAt Γ d = Za := by
      apply Subgroup.eq_of_le_of_card_ge ((inf_le_inf hWV le_rfl).trans_eq hintersection)
      rw [hZaCard]
      change 4 ≤ Nat.card (W ⊓ VAt Γ d : Subgroup G)
      omega
    have hVW : V ≤ W := nine_five_neighbor_module_le_of_residual_normalizes
      ctx.toLocalContext cp.a cp.firstStep cp.firstStep_adj W
        (hI.symm.le.trans inf_le_left) hEW
    have hcardVW : Nat.card V = Nat.card W := congrArg (fun L : Subgroup G => Nat.card L) (le_antisymm hVW hWV)
    have hlarge' := hlarge
    rw [hintersection,hZaCard] at hlarge'
    rw [hI,hZaCard] at hsmall
    change 16 ≤ Nat.card V at hlarge'
    change Nat.card W ≤ 8 at hsmall
    have hboundV : Nat.card V ≤ 8 := hcardVW.le.trans hsmall
    omega
  have hAQ : ⁅A,Q⁆ ≤ Z := by
    apply Subgroup.commutator_le.mpr
    intro y hy q hq
    have hCQZ : ⁅Subgroup.zpowers y ⊔ V,Q⁆ ≤ Z := le_sup_left.trans_eq (hall y hy)
    exact hCQZ (Subgroup.commutator_mem_commutator
      (show y ∈ Subgroup.zpowers y ⊔ V from Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hq)
  exact (lemma_seven_six ctx.sectionSeven Γ cp).next_residual_core.1
    (nine_four_central_actor_le_initial_core ctx hb d hremote hne A Q data.subgroup_le
      henlarged data.not_le hQnext hAQ)

end Stellmacher.SectionNine
