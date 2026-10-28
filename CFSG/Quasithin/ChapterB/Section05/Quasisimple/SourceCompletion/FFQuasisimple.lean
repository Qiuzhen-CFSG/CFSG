module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.FFSocle
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
/-!
# Initial FF classification with a quasisimple covering component

A faithful binary FF actor with trivial two-core, a normal quasisimple
component, and two-group quotient has that component inside its actual
best-offender subgroup. The generalized Fitting subgroup is the component;
its odd central kernel cannot contain an elementary two-offender. Restricting
to the offender subgroup then supplies every hypothesis of the complete B.5.1
source classification, retaining a possible odd covering center.

Source: Aschbacher–Smith B.5.1 and Meierfrankenfeld–Stellmacher (1993), (3.2).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

omit [Finite G] in
private theorem quotient_subgroup_two (K J : Subgroup G) [K.Normal]
    (h : IsPGroup 2 (G ⧸ K)) : IsPGroup 2 (J ⧸ K.subgroupOf J) := by
  let f := (QuotientGroup.mk' K).comp J.subtype
  have hk : f.ker = K.subgroupOf J := by
    ext x
    exact QuotientGroup.eq_one_iff x.val
  let e := QuotientGroup.quotientMulEquivOfEq hk.symm
  exact h.of_injective ((QuotientGroup.kerLift f).comp e.toMonoidHom)
    ((QuotientGroup.kerLift_injective f).comp e.injective)

theorem ff_quasisimple_source_conclusion
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    [K.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (G ⧸ K)) (hcore : pCore 2 G = ⊥)
    (hsq : IsSQTK KnownSimple.IsKnownSimple K)
    (hf : Function.Injective ρ) (hff : IsFFModule ρ) :
    K ≤ offenderSubgroup ρ ∧
    Nonempty (SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      (ρ.comp (offenderSubgroup ρ).subtype) (K.subgroupOf (offenderSubgroup ρ))) := by
  let J := offenderSubgroup ρ
  let : J.Normal := offenderSubgroup_normal ρ
  have hF : generalizedFitting G = K :=
    generalizedFitting_eq_of_quasisimple_two_quotient K hquot hcore
  have hKJ : K ≤ J := by
    rcases IsComponent.normal_dichotomy
      (⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩ : IsComponent G K) J with h | h
    · exact h
    · have hJC : J ≤ centralizer (K : Set G) :=
        le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
      have hJK : J ≤ K := hJC.trans (hF ▸ centralizer_generalizedFitting_le G)
      let : IsMulCommutative J :=
        ⟨⟨fun a b => Subtype.ext (hJC a.property b (hJK b.property)).symm⟩⟩
      have hJF : J ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
      have hJO := hJF.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)
      obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ).mp hff
      let : IsElementaryAbelian 2 A := hA.1.2
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
      have hcop : Nat.Coprime (Nat.card A) (Nat.card (pPrimeCore 2 G)) := by
        rw [hn]
        exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
      exact (hA.1.1 (le_bot_iff.mp
        ((le_inf le_rfl ((hA.le_offenderSubgroup ρ).trans hJO)).trans
          (disjoint_of_coprime_natCard hcop).le_bot))).elim
  let D := K.subgroupOf J
  let e : D ≃* K := subgroupOfEquivOfLe hKJ
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have hcoreJ : pCore 2 J = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : J.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff J.subtype).mpr J.subtype_injective
  have hfit : generalizedFitting J = D :=
    generalizedFitting_eq_of_quasisimple_two_quotient D (quotient_subgroup_two K J hquot) hcoreJ
  have hh : QuasisimpleSourceHypothesis (ρ.comp J.subtype) KnownSimple.IsKnownSimple D := by
    refine ⟨inferInstance,hf.comp J.subtype_injective,inferInstance,
      (IsSQTK.equiv e).mpr hsq,?_,hcoreJ,offenderSubgroup_restrict_eq_top ρ⟩
    rw [hfit]
    exact (sup_eq_left.mpr (by
      rw [←hfit]
      exact (show center J ≤ fittingSubgroup J from le_sSup ⟨inferInstance,inferInstance⟩).trans
        (fitting_le_generalizedFitting J))).symm
  refine ⟨hKJ,?_⟩
  exact knownSimple_quasisimpleClassificationInput
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    SourceClassification.irreducibleClassification_knownSimple
    SourceInduction.nonbinaryG2RootPairInput J V (ρ.comp J.subtype) D hh
end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
