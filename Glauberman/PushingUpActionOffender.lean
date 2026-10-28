module
public import Theory.Representation.AlternatingFiveOffenderRecognition
public import Glauberman.PushingUpOmegaAction
public import Theory.Representation.BinaryOffender.QuadraticImageBound
/-!
# The original quadratic offender in its faithful omega-action image

The two-core lies in the action kernel, which lies in the original normal
kernel K. The source Sylow intersection S∩K=O2(H) therefore identifies the
relative action kernel on the actual maximum abelian offender with its original
two-core intersection. Its source cardinal bound is consequently the genuine
offender bound on the unchanged faithful action image. Double commutators
also give quadraticity in the original additive coordinates.

Source: Niles, Pushing-up in finite groups (1979), Lemma2.9, p.33.
-/
set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Theory.GroupTheory
open Subgroup Representation.BinaryOffender
namespace Glauberman
variable {H J:Type*} [Group H] [Group J]

omit [Group J] in
private theorem kernel_inf_eq_of_intersection
    (S Q K A C:Subgroup H) (hSK:S⊓K=Q) (hAS:A≤S) (hQC:Q≤C) (hCK:C≤K) :
    C⊓A=Q⊓A := by
  apply le_antisymm
  · intro x hx
    exact ⟨hSK ▸ ⟨hAS hx.2,hCK hx.1⟩,hx.2⟩
  · exact inf_le_inf hQC le_rfl

theorem action_image_card_of_kernel_intersection
    (S Q K A:Subgroup H) [Q.Normal]
    (hSK:S⊓K=Q) (hAS:A≤S) (a:H→*J) (hQa:Q≤a.ker) (haK:a.ker≤K) :
    Nat.card (A.map a)=Nat.card (A.map (QuotientGroup.mk' Q)) := by
  rw [←relIndex_ker,←relIndex_ker,QuotientGroup.ker_mk']
  rw [←inf_relIndex_right a.ker A,←inf_relIndex_right Q A,
    kernel_inf_eq_of_intersection S Q K A a.ker hSK hAS hQa haK]

variable [Finite H] {F:Type*} [Field F] [Finite F]
theorem original_psl2_four_action_offender
    (hF:Nat.card F=4) (S:Sylow 2 H)
    (hu:Order.HasUniqueMaximalOver (S:Subgroup H) ⊤)
    (K:Subgroup H) [K.Normal]
    (e:(H⧸K)≃*Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf:generalizedFitting H=pCore 2 H)
    (hno:NoCharacteristicNormal (S:Subgroup H))
    (hQ:pCore 2 H≤(omegaAction H).ker) (hk:(omegaAction H).ker≤K) :
    ∃A:Subgroup H,A∈thompsonAbelianSubgroups (S:Subgroup H) ∧
      ¬A≤K ∧ ⁅⁅omegaCenterIn (pCore 2 H),A⁆,A⁆=⊥ ∧
      IsPGroup 2 (actionSubgroup (omegaAction H) A) ∧
      (Nat.card (actionSubgroup (omegaAction H) A)=2 ∨
        Nat.card (actionSubgroup (omegaAction H) A)=4) ∧
      Nat.card (actionSubgroup (omegaAction H) A)=Nat.card (A.map (QuotientGroup.mk' K)) ∧
      fixedCodim (imageRepresentation (omegaAction H)) (actionSubgroup (omegaAction H) A)≤
        Nat.log 2 (Nat.card (actionSubgroup (omegaAction H) A)) := by
  obtain ⟨A,hA,hAK,hquad,hS,hneq,hbound,hcard,hsmall⟩ :=
    original_psl2_four_nontrivial_quadratic_offender hF S hu K e hf hno
  have hSK := (Theory.SpecificGroups.SL2.original_kernel_reduction_of_psl2_four hF S hu K e).1
  have hQa:pCore 2 H≤(actionHom (omegaAction H)).ker := by rw [actionHom_ker_eq]; exact hQ
  have haK:(actionHom (omegaAction H)).ker≤K := by rw [actionHom_ker_eq]; exact hk
  have hcards : Nat.card (actionSubgroup (omegaAction H) A)=
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) :=
    action_image_card_of_kernel_intersection (S:Subgroup H) (pCore 2 H) K A hSK hA.1
      (actionHom (omegaAction H)) hQa haK
  have hp:IsPGroup 2 (actionSubgroup (omegaAction H) A) :=
    (S.isPGroup'.to_le hA.1).map (actionHom (omegaAction H))
  have hnb : actionSubgroup (omegaAction H) A≠⊥ := by
    intro he
    exact hAK (((map_eq_bot_iff A).mp he).trans haK)
  have hnot1 : Nat.card (actionSubgroup (omegaAction H) A)≠1 := by
    intro he
    exact hnb (card_eq_one.mp he)
  have hsmall' : Nat.card (actionSubgroup (omegaAction H) A)≤4 :=
    hcards.trans hcard ▸ hsmall
  have hc : Nat.card (actionSubgroup (omegaAction H) A)=2 ∨
      Nat.card (actionSubgroup (omegaAction H) A)=4 := by
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hn2:n≤2 := by
      by_contra hh
      have hd : 2^3≤2^n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [←hn] at hd
      omega
    interval_cases n <;> simp_all
  refine ⟨A,hA,hAK,hquad,hp,hc,hcards.trans hcard,?_⟩
  rw [fixedCodim_actionSubgroup]
  apply Nat.le_log_of_pow_le (by decide)
  rw [←omegaAction_fixed_index, hcards]
  exact hbound

omit [Finite H] [Group J] in
/-- Double group commutators give quadraticity on the literal omega action. -/
theorem omegaAction_quadratic_of_double_commutator (A:Subgroup H)
    (hq:⁅⁅omegaCenterIn (pCore 2 H),A⁆,A⁆=⊥) : IsQuadratic (omegaAction H) A := by
  intro a ha b hb v
  have hcentral : a∈centralizer ((⁅omegaCenterIn (pCore 2 H),A⁆:Subgroup H):Set H) := by
    rw [commutator_eq_bot_iff_le_centralizer] at hq
    exact le_centralizer_iff.mp hq ha
  apply (omegaAction_moved_centralizer H A a).mp hcentral
  exact Submodule.subset_span ⟨b,hb,v,Submodule.mem_top,rfl⟩
end Glauberman
