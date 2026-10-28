module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Inspection.Residual
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.BinaryMS

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalPlaneCentralizers.Inspection.Residual`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  [IsElementaryAbelian 2 V]

/-- The original component is O^{3′}(C_G(A)), as an embedded subgroup. -/
theorem Context.local_component_residual (s : Context T L V) (d : MarkedPlane V)
    (J : Subgroup G) (j : LocalData T L d J) :
    J = (primeToResidual 3 (centralizer (d.A : Set G))).map
      (centralizer (d.A : Set G)).subtype := by
  let N := normalizer (d.A : Set G)
  let H := centralizer (d.A : Set G)
  let HN := H.subgroupOf N
  let JN := J.subgroupOf N
  have hHN : H ≤ N := Subgroup.centralizer_le_normalizer _
  have hJN : J ≤ N := j.input.component.1.trans hHN
  let eH : H ≃* HN := (subgroupOfEquivOfLe hHN).symm
  have hm : (J.subgroupOf H).map eH.toMonoidHom = JN.subgroupOf HN := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨eH.symm x,hx,eH.apply_symm_apply x⟩
  have hc : JN.IsCComponent :=
    (IsCComponent.subgroupOf_iff (inferInstance : HN.Normal).isSubnormal
      (comap_mono j.input.component.1)).mp (hm ▸ j.input.component.2.map_equiv eH)
  let : JN.Normal := normal_subgroupOf_of_le_normalizer
    (s.local_component_normalizer d J j)
  let eJ := subgroupOfEquivOfLe hJN
  let eQ := QuotientGroup.congr (pCore 2 JN) (pCore 2 J) eJ (pCore_map_iso 2 eJ)
  obtain ⟨e⟩ := s.binary_linearThree_core_model d J j
  let b := eQ.trans e
  have hz : center (JN ⧸ pCore 2 JN) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact b.map_eq_one_iff.mp (Matrix.PSL3Two.center_eq_bot.le
      ((centerCongr b) ⟨x,hx⟩).property)
  let := j.input.quasisimple
  let : IsQuasisimple (JN ⧸ pCore 2 JN) := IsQuasisimple.of_mulEquiv eQ.symm
  let := IsQuasisimple.simple (G := JN ⧸ pCore 2 JN)
  let : IsSimpleGroup (JN ⧸ pCore 2 JN) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hd : 3 ∣ Nat.card (JN ⧸ pCore 2 JN) := by
    rw [Nat.card_congr b.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (JN ⧸ pCore 2 JN))) := by
    rw [Nat.card_congr (MulAut.outerCongr b).toEquiv,
      Matrix.PSL3Two.Automorphisms.card_outer_sl]
    decide
  have hr : primeRank 3 N ≤ 2 :=
    (s.hypothesis.qtke.twoLocal_sqtk
      ⟨d.A,d.ne_bot,IsPGroup.of_card (n := 2) d.card,rfl⟩).stronglyQuasithin
        3 Nat.prime_three (by decide)
  obtain ⟨n,hn,_,hout⟩ := s.plane_cubic_escape d
  have he := cComponent_residual_of_external_cubic JN HN hc
    (comap_mono j.input.component.1) hz hd ho hr n hn hout
  have he' := congrArg (map N.subtype) he
  have hcomp : N.subtype.comp HN.subtype = H.subtype.comp eH.symm.toMonoidHom := rfl
  rw [map_map,hcomp,←map_map,map_primeToResidual,map_subgroupOf_eq_of_le hJN] at he'
  exact he'.symm

/-- The exact original C.2.7 inspection contract, including the literal residual. -/
theorem Context.componentInspection (s : Context T L V) : ComponentInspection T L V := by
  intro d J j
  exact Or.inr (s.linearThreeRow_of_residual d J j (s.local_component_residual d J j))

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers
