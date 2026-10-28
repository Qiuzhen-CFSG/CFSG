module
public import Stellmacher.SectionNine.NineTenTwoStepClassification
public import Stellmacher.SectionNine.NineThreeCoreOmega
public import Stellmacher.SectionNine.NineThreeCenterIrreducible
public import Stellmacher.SectionNine.DistanceOneChiefSubgroup
public import Theory.GroupTheory.CentralIndexTwoCommutatorSupplement

/-!
# The second-core action on the first/third module intersection

At literal critical length five, retain the actual terminal order-thirty-two
module, wreath core quotient, and terminal/backward intersection of order
eight. For I = V_first ∩ V_third, the second core acts with centralizer of
index four and is generated modulo that centralizer by its commutators with
the second residual. Both conclusions concern the original path and ambient
subgroups.

The terminal two-step classification transports I's order, middle-core
containment, and full middle-stabilizer normalization to offsets one, two,
and three. Its middle center Z has order four and equals the omega-center
of the second core Q, so the Q-fixed part of I is exactly Z. The commutator
[I,Q] lies in Z by the index-two quotient and is nonzero. Center
irreducibility makes [I,Q]=Z. The proved initial-center residual commutator
transports to [Z,E_second]=Z. The central index-two displacement theorem
then identifies the literal action kernel with C_Q(I), computes its index,
and supplies Q=[Q,E_second] C_Q(I).

Source: Stellmacher (9.10), printed p.58, the paragraph immediately before
(10). The kernel is defined inside the second core; its index four is derived
from this action, correcting the printed first-core numerator in that
intermediate ratio. The final source (10) remains a separate consumer.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_second_core_intersection_action
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 5)
    (hcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hinter : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3) :
    let second := ctx.criticalPath.path ⟨2, by omega⟩
    let third := ctx.criticalPath.path ⟨3, by omega⟩
    let I := VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third
    let Q0 := QAt ctx.Γ second ⊓ Subgroup.centralizer (I : Set G)
    QuotientCardEq (QAt ctx.Γ second) Q0 4 ∧
      QAt ctx.Γ second = ⁅QAt ctx.Γ second,EAt ctx.Γ second⁆ ⊔ Q0 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : cp.length=5 := hb
  have hshort : 1<cp.length := by omega
  let second := cp.path ⟨2,by omega⟩
  let third := cp.path ⟨3,by omega⟩
  let P := GAt Γ second
  let Q := QAt Γ second
  let E := EAt Γ second
  let I := VAt Γ cp.firstStep ⊓ VAt Γ third
  let Z := ZAt Γ second
  have hleft : Γ.adjacent second cp.firstStep := by
    have hedge := cp.path_adj ⟨1,by omega⟩
    change Γ.adjacent (cp.path ⟨1,by omega⟩) second at hedge
    rw [cp.path_first] at hedge
    exact Γ.adjacent_symm hedge
  have hright : Γ.adjacent second third := cp.path_adj ⟨2,by omega⟩
  have hdistinct : cp.firstStep≠third := by
    have hh := nine_seven_path_vertices_ne Γ cp 1 3 (by omega) (by omega)
    rwa [cp.path_first] at hh
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.firstStep
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
    ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hleft))
  have horbit : IsConjugateVertex Γ cp.a second := ⟨mover,hmover⟩
  obtain ⟨_,_,hIcard,hZI,hIQ,hPI⟩ := nine_ten_two_step_wreath_classification ctx (by omega)
    hcard hmodel hinter horbit hleft hright hdistinct
  change Nat.card I=8 at hIcard
  change Z≤I at hZI
  change I≤Q at hIQ
  change P≤Subgroup.normalizer (I:Set G) at hPI
  let _ : IsElementaryAbelian 2 (VAt Γ cp.firstStep) :=
    ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hshort).1
  have hZcard : Nat.card Z=4 := (lemma_nine_three_ambient ctx hshort second horbit).2
  have homega : omegaOneCenter Q=Z := nine_three_core_omega_eq_center ctx hshort second horbit
  have hQP : Q≤P := by
    rw [show Q=QAt Γ second from rfl,QAt,q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hEP : E≤P := by
    change Γ.twoResidualAt second≤P
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hPQ : P≤Subgroup.normalizer (Q:Set G) := stabilizer_le_normalizer_q Γ second
  have hPE : P≤Subgroup.normalizer (E:Set G) := by
    change P≤Subgroup.normalizer (Γ.twoResidualAt second:Set G)
    rw [Γ.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le P)).mp
      (twoResidualIn_normal P)
  have hPZ : P≤Subgroup.normalizer (Z:Set G) := stabilizer_le_normalizer_z Γ second
  have hZQ : Z≤Subgroup.centralizer (Q:Set G) := by
    intro z hz
    have hzomega : z∈omegaOneCenter Q := by rwa [homega]
    exact Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff Q z).mp hzomega).2.2
  have hfixed : I⊓Subgroup.centralizer (Q:Set G)=Z := by
    apply le_antisymm
    · intro z hz
      rw [←homega]
      apply (mem_omegaOneCenterAmbient_iff Q z).mpr
      exact ⟨hIQ hz.1,elemPow_eq_one_of_isElementaryAbelian z hz.1.1,
        Subgroup.mem_centralizer_iff.mp hz.2⟩
    · exact le_inf hZI hZQ
  have hindex : Z.relIndex I=2 := by
    have hh := (Z.subgroupOf I).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZI).toEquiv,hZcard,hIcard] at hh
    change Z.relIndex I*4=8 at hh
    omega
  have hcommZ : ⁅I,Q⁆≤Z := by
    rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_le.mpr
    intro q hq i hi
    have hconj : q*i*q⁻¹∈I := (Subgroup.mem_normalizer_iff.mp (hPI (hQP hq)) i).mp hi
    have hmem : q*i*q⁻¹∈Z ↔ i⁻¹∈Z :=
      ((Subgroup.mem_normalizer_iff.mp (hPZ (hQP hq)) i).symm).trans Z.inv_mem_iff.symm
    exact (Z.subgroupOf I).mul_mem_iff_of_index_two hindex
      (a:=⟨q*i*q⁻¹,hconj⟩) (b:=⟨i⁻¹,I.inv_mem hi⟩) |>.mpr hmem
  have hnorm : P≤Subgroup.normalizer ((⁅I,Q⁆:Subgroup G):Set G) := by
    intro p hp
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPI hp),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPQ hp)]
  have hcomm : ⁅I,Q⁆=Z := by
    rcases nine_three_center_irreducible ctx hshort second horbit ⁅I,Q⁆ hcommZ hnorm with hbot|heq
    · have hIC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
      have heq : I=Z := le_antisymm ((le_inf le_rfl hIC).trans_eq hfixed) hZI
      have hh : Nat.card I=Nat.card Z := congrArg (fun J:Subgroup G => Nat.card J) heq
      omega
    · exact heq
  have hZE : ⁅Z,E⁆=Z := by
    let equiv := MulAut.conj (mover:G)⁻¹
    have hZm : (ZAt Γ cp.a).map equiv.toMonoidHom=Z := by rw [←z_act,hmover]
    have hPm : (GAt Γ cp.a).map equiv.toMonoidHom=P := by
      change conjugateBy (stabilizer Γ cp.a) (mover:G)⁻¹=P
      rw [←stabilizer_act,hmover]
    have hEm : (EAt Γ cp.a).map equiv.toMonoidHom=E := by
      change (e Γ cp.a).map equiv.toMonoidHom=e Γ second
      simp only [CosetGraphContext.e,Γ.twoResidualAt_def]
      change (twoResidualIn (GAt Γ cp.a)).map equiv.toMonoidHom=twoResidualIn P
      rw [←twoResidualIn_map_equiv,hPm]
    have hbase : ⁅ZAt Γ cp.a,EAt Γ cp.a⁆=ZAt Γ cp.a :=
      distance_one_initial_center_full_residual ctx.toLocalContext
    have hh := congrArg (fun J:Subgroup G => J.map equiv.toMonoidHom) hbase
    rwa [Subgroup.map_commutator,hZm,hEm] at hh
  obtain ⟨hcount,hsupp⟩ := Subgroup.central_index_two_commutator_supplement P Q E I Z
    hQP hEP hIQ hZI hindex hPQ hPE hPI hPZ hZQ hcomm hZE
  exact ⟨by change Nat.card Q=4*_; rwa [hZcard] at hcount,hsupp⟩

end Stellmacher.SectionNine
