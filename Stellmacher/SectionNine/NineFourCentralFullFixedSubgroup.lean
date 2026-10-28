module
public import Stellmacher.SectionNine.NineFourCentralFixedDecomposition
public import Stellmacher.SectionNine.NineNextResidualCoreFixed
public import Stellmacher.SectionNine.NineNextCenterResidualCommutator

/-!
# The full remote-core fixed subgroup in central (9.4)

For the normalized and enlarged counterexample, centralization of the
initial/remote core intersection forces C_A(Q_remote)=C_Vremote(Q_remote).
Consequently A is the initial center joined with the entire remote-module
fixed subgroup. No residual fixed-subgroup identity is assumed.

The independent residual-module fixed bound and center-in-residual theorem
identify [V_remote,E_remote] intersect C(Q_remote) with Z_remote. Residual
neighbor-module generation writes V_remote as [V_remote,E_remote] joined
with Z_a. Since Z_a has order four and Z_remote order two, the full fixed
subgroup has relative index at most two over Z_remote. The preceding fixed
decomposition supplies C_A(Q_remote) containing that line and distinct
from it. The relative-index tower therefore makes it the entire fixed
subgroup. Substitution in the decomposition gives the final equality.

Source: the fixed-subgroup comparison in Stellmacher (9.4), printed p.52 /
PDF p.42 of `refs/files/stellmacher-n-group.pdf`. This is the actual input
for the subsequent residual-normalization transfer.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped IsMulCommutative
universe u

private theorem eq_of_relIndex_le_two {G : Type*} [Group G] [Finite G]
    (Z D C : Subgroup G) (hZD : Z ≤ D) (hDC : D ≤ C)
    (hne : D ≠ Z) (hindex : Z.relIndex C ≤ 2) : D=C := by
  have htower := Subgroup.relIndex_mul_relIndex Z D C hZD hDC
  have hZDpos : 0 < Z.relIndex D := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hDCpos : 0 < D.relIndex C := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hZDne : Z.relIndex D ≠ 1 := fun hh => hne
    (le_antisymm (Subgroup.relIndex_eq_one.mp hh) hZD)
  have hZDtwo : 2 ≤ Z.relIndex D := by omega
  have hone : D.relIndex C = 1 := by nlinarith
  exact le_antisymm hDC (Subgroup.relIndex_eq_one.mp hone)

public theorem nine_four_central_full_fixed_subgroup
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
    data.subgroup ⊓ Subgroup.centralizer
      (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G) =
      VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓ Subgroup.centralizer
        (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G) ∧
    data.subgroup = ZAt ctx.Γ ctx.criticalPath.a ⊔
      (VAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) ⊓ Subgroup.centralizer
        (QAt ctx.Γ (ctx.Γ.act data.conjugator data.remote) : Set G)) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let d := Γ.act data.conjugator data.remote
  let A := data.subgroup
  let V := VAt Γ d
  let E := EAt Γ d
  let W := ⁅V,E⁆
  let Za := ZAt Γ cp.a
  let Zd := ZAt Γ d
  let Qd := QAt Γ d
  let C := V ⊓ Subgroup.centralizer (Qd : Set G)
  let D := A ⊓ Subgroup.centralizer (Qd : Set G)
  obtain ⟨conjugator,hconjugator⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hremote
  have horbit : IsConjugateVertex Γ cp.firstStep d := ⟨conjugator,hconjugator⟩
  have hfixed : W ⊓ Subgroup.centralizer (Qd : Set G) = Zd := by
    apply le_antisymm (nine_next_residual_core_fixed_le_center ctx hb d horbit)
    apply le_inf (nine_next_center_le_residual_commutator ctx hb d horbit)
    exact ((lemma_seven_three ctx.sectionSeven Γ).center_core d cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr
        (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote)))).trans
          ((omegaOneCenter_le_centerAmbient Qd).trans (centerAmbient_le_centralizer Qd))
  have hdecomp := nine_four_central_fixed_decomposition ctx hb data hremote henlarged hcomm
  have hZaV : Za ≤ V := nine_seven_neighbor_center_le_module Γ
    (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hremote))
  have hZaA : Za ≤ A := (le_inf hZaV
    (lemma_seven_four ctx.sectionSeven Γ cp).first_containment.1).trans henlarged
  have hZdZa : Zd ≤ Za := ((nine_seven_center_join ctx cp.a ⟨1,Γ.act_one _⟩).2 d hremote).2
  have hZWA : Zd ≤ W := hfixed.symm.le.trans inf_le_left
  have hZcentral : Zd ≤ Subgroup.centralizer (Qd : Set G) := hfixed.symm.le.trans inf_le_right
  have hEP : E ≤ GAt Γ d := by
    change Γ.twoResidualAt d ≤ Γ.vertexStabilizer d
    rw [Γ.twoResidualAt_def]
    exact twoResidualIn_le _
  have hWV : W ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp
    (hEP.trans (stabilizer_le_normalizer_v Γ d))
  have hcontainerV : W ⊔ Za ≤ V := sup_le hWV hZaV
  have hEnormal : E ≤ Subgroup.normalizer (W ⊔ Za : Subgroup G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hcontainerV le_rfl).trans le_sup_left)
  have hspan : V = W ⊔ Za := le_antisymm
    (nine_five_neighbor_module_le_of_residual_normalizes ctx.toLocalContext cp.a d
      ((mem_neighborhood_iff_adjacent Γ).mp hremote) _ le_sup_right hEnormal) hcontainerV
  obtain ⟨mover,hmover⟩ := (lemma_seven_one ctx.sectionSeven Γ).local_transitivity cp.a
    ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj) hremote
  have hdOrbit : IsConjugateVertex Γ cp.firstStep d := ⟨mover,hmover⟩
  have hVElementary : IsElementaryAbelian 2 V := by
    let _ := ((lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).longer_case hb).1
    change Γ.act (mover : G) cp.firstStep = d at hmover
    change IsElementaryAbelian 2 (VAt Γ d)
    rw [← hmover]
    change IsElementaryAbelian 2 (v Γ (Γ.act (mover : G) cp.firstStep))
    rw [v_act]
    exact IsElementaryAbelian.map (MulAut.conj ((mover : G)⁻¹)).toMonoidHom
  let _ := hVElementary
  have hZcard : Nat.card Zd = 2 := (nine_next_center_commutator_and_kernel ctx hb d hdOrbit).1
  have hZacard : Nat.card Za = 4 := (lemma_nine_three_ambient ctx hb cp.a ⟨1,Γ.act_one _⟩).2
  have hZaindex : Zd.relIndex Za = 2 := by
    have hh := (Zd.subgroupOf Za).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZdZa).toEquiv] at hh
    change Zd.relIndex Za * Nat.card Zd = Nat.card Za at hh
    rw [hZcard,hZacard] at hh
    omega
  have hindexW : W.relIndex V ≤ 2 := by
    have hh := Subgroup.relIndex_sup_left (Za.subgroupOf V) (W.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup hWV hZaV,← hspan,
      Subgroup.relIndex_subgroupOf le_rfl,Subgroup.relIndex_subgroupOf hZaV] at hh
    rw [hh]
    exact (Subgroup.relIndex_le_of_le_left hZWA Subgroup.index_ne_zero_of_finite).trans_eq hZaindex
  have hWC : W ⊓ C = Zd := by
    change W ⊓ (V ⊓ Subgroup.centralizer (Qd : Set G)) = Zd
    rw [← inf_assoc,inf_eq_left.mpr hWV]
    exact hfixed
  have hindexC : Zd.relIndex C ≤ 2 := by
    rw [← hWC,Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_le_of_le_right (show C ≤ V from inf_le_left)
      Subgroup.index_ne_zero_of_finite).trans hindexW
  have hDC : D ≤ C := inf_le_inf data.subgroup_le le_rfl
  have hZD : Zd ≤ D := le_inf (hZdZa.trans hZaA) hZcentral
  have hDfull : D = C := eq_of_relIndex_le_two Zd D C hZD hDC hdecomp.2 hindexC
  refine ⟨hDfull,?_⟩
  exact hdecomp.1.trans (congrArg (fun J : Subgroup G => Za ⊔ J) hDfull)

end Stellmacher.SectionNine
