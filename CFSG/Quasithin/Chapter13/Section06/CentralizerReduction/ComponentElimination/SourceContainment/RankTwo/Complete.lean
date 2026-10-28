module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Assembly
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.ExceptionalModels
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Residual
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.Rank
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.CComponent.RankTwoResidual
public import Theory.GroupTheory.CComponent.SixCoverTheta
public import Theory.GroupTheory.CComponent.TripleSevenTheta
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import Theory.Quasithin.CoprimeRank
public import Theory.Mathieu.M22.Properties.Order
import all CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.ExceptionalModels
import all CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Intrinsic

/-!
# The rank-two containment without universal A.3.18

Classify the original component image modulo the ambient two-core by A.3.6.
In the simple case the reduced central factor has a two-group outer group,
so the original C-component is the prime-to-three residual. In the cover
case the signed families and M₂₂ are excluded by the actual reduced models;
the triple A₆ and A₇ covers have exponent-three Sylow groups and two-group
outer action. Their intrinsic cubic containment lifts through the two-core.

The two `import all` edges are an intentional internal proof split: they reuse
the rank exclusions and the reduced-model order calculation in this same
source development without expanding their public interfaces.
Source: Aschbacher--Smith, A.3.6 and A.3.18, pp.43--53; 13.6.20, p.931.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open ComponentSelection LocalApplication Chapter1.Section02 Chapter1.Section02.LocalModels
open Theory.SpecificGroups.BinaryComponentResidual

private noncomputable def quotientOfCenterless {E : Type*} [Group E]
    (hz : center E = ⊥) : (E ⧸ center E) ≃* E :=
  (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

private theorem central_factor_facts {Q R : Type*} [Group Q] [Finite Q]
    [Group R] [Finite R] (hm : ReducedModel Q) (e : R ≃* (Q ⧸ center Q))
    (hr : 2 ≤ primeRank 3 R) : Facts R := by
  cases hm with
  | linear n hn he =>
    obtain ⟨f⟩ := he
    let g := e.trans (binary_quotient_equiv (by omega : 0 < n) f)
    by_cases h3 : n = 3
    · subst n
      obtain ⟨E, _, hc⟩ := exists_elementary_nine_of_three_rank hr
      have hd := E.card_subgroup_dvd_card
      rw [hc, Nat.card_congr g.toEquiv, Matrix.PSL3Two.card_PSL] at hd
      norm_num at hd
    · exact Facts.of_equiv
        (g.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)))
        (Theory.SpecificGroups.BinaryComponentResidual.linear (by omega))
  | symplectic he =>
    obtain ⟨f⟩ := he
    let s := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    let d : commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃*
        alternatingGroup (Fin 6) := (s.subgroupMap _).trans
      (MulEquiv.subgroupCongr (by
        rw [map_commutator_eq, MonoidHom.range_eq_top.mpr s.surjective]
        exact alternatingGroup.commutator_perm_eq (by norm_num)))
    exact Facts.of_equiv (e.trans ((centerQuotientCongr (f.trans d)).trans
      (quotientOfCenterless alternatingSix.1))) alternatingSix
  | g2 he =>
    obtain ⟨f⟩ := he
    exact Facts.of_equiv (e.trans ((centerQuotientCongr f).trans
      (quotientOfCenterless g2.1))) g2
  | ahat6 he =>
    obtain ⟨f⟩ := he
    exact Facts.of_equiv (e.trans ((centerQuotientCongr f).trans
      Representation.Hexacode.even_quotient_center_equiv)) alternatingSix
  | a7 he =>
    obtain ⟨f⟩ := he
    have hs : Facts (alternatingGroup (Fin 7)) :=
      ⟨alternatingGroup.center_eq_bot (by simp),
        alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide),
        alternatingGroup.SevenComponent.outer_two⟩
    exact Facts.of_equiv (e.trans ((centerQuotientCongr f).trans
      (quotientOfCenterless hs.1))) hs

private theorem cover_congruence {R : Type*} [Group R] [Finite R]
    [Group.IsPerfect R] (hc : Nat.card (center R) = 3)
    {unitary : Bool} {q : ℕ} (hm : IsSLSign R unitary 3 q) :
    q % 3 = if unitary then 2 else 1 := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    have he : Nat.card (center SL(3,F)) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).symm.trans hc
    rw [Atlas.ExceptionalSupport.card_sl_center, hF] at he
    have hd : 3 ∣ q - 1 := he ▸ Nat.gcd_dvd_right 3 (q - 1)
    have hp : 0 < q := hF ▸ Nat.card_pos
    have := Nat.mod_eq_zero_of_dvd hd
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
    let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective J.specialToProjective_surjective
    have hz := J.specialToProjective_ker_eq_center (unitary_center_of_perfect J hF hconj)
    have he : Nat.card (center J.specialSubgroup) = 3 :=
      (Nat.card_congr (centerCongr e).toEquiv).symm.trans hc
    rw [← hz, BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.card_kernel J hF hconj] at he
    have hd : 3 ∣ q + 1 := he ▸ Nat.gcd_dvd_right 3 (q + 1)
    have := Nat.mod_eq_zero_of_dvd hd
    simp only [↓reduceIte]
    omega

private theorem reduced_not_m22 {Q R : Type*} [Group Q] [Finite Q]
    [Group R] (hm : ReducedModel Q) (e : (R ⧸ center R) ≃* (Q ⧸ center Q))
    (hR : IsM22Cover R) : False := by
  obtain ⟨f⟩ := hR.2.2
  have hd := (center Q).card_quotient_dvd_card.trans (reduced_card_dvd hm)
  rw [← Nat.card_congr e.toEquiv, Nat.card_congr f.toEquiv,
    Sporadic.Mathieu.m22_order] at hd
  norm_num at hd

private theorem normal_of_core_center_small {H : Type*} [Group H] [Finite H]
    {C : Subgroup H} (hC : C.IsCComponent) [IsQuasisimple (C ⧸ pCore 2 C)]
    (hc : Nat.card (center (C ⧸ pCore 2 C)) ≤ 3)
    (hr : 2 ≤ primeRank 3 (C ⧸ pCore 2 C)) (hH : primeRank 3 H ≤ 2) : C.Normal := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := C.map q
  let e := cComponentTwoCoreQuotientEquiv hC
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e
  have hB : IsComponent (H ⧸ pCore 2 H) B := ⟨hC.subnormal.quotient, inferInstance⟩
  have hcB : Nat.card (center B) ≤ 3 := by
    rw [← Nat.card_congr (centerCongr e).toEquiv]
    exact hc
  have hrB : 2 ≤ primeRank 3 B := by rwa [← primeRank_congr 3 e]
  have hn := ChapterA.SQTKStructure.NonnormalOuterSource.component_normal_of_three_rank
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hH)
    hB hcB hrB
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact cComponent_normal_of_quotient_normal hC (pCore 2 H) hn

private theorem cubic_closure_of_triple_seven {H : Type*} [Group H] [Finite H]
    (C : Subgroup H) [C.Normal] (hC : C.IsCComponent)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (e : (C ⧸ pCore 2 C) ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven)
    (hr : 2 ≤ primeRank 3 C)
    (hz : primeRank 3 (center (C ⧸ pCore 2 C)) ≤ 1)
    (hH : primeRank 3 H ≤ 2) : closure {x : H | orderOf x = 3} = C := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact TripleSevenTheta.order_three_mem C hC e hH hx
      (le_normalizer_of_normal (mem_top x))
  · let : Group.IsPerfect C := hC.perfect
    have he := congrArg (map C.subtype) (cubic_closure_eq_top_of_twoCore_quasisimple hr hz)
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, range_subtype] at he
    rw [← he]
    apply Subgroup.closure_mono
    rintro x ⟨y, hy, rfl⟩
    exact (C.orderOf_coe y).trans hy

universe u
variable {G : Type u} [Group G] [Finite G]

private theorem source_of_local_theta {K L : Subgroup G} {v : G}
    (h : closure {x : localActor K L v | orderOf x = 3} = localComponent K L v)
    (hcard : Nat.card (Lv L v ⧸ pCore 2 (Lv L v)) = 3) :
    closure {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} = K ∧ Lv L v ≤ K := by
  have hm := congrArg (map (localActor K L v).subtype) h
  rw [map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_closure] at hm
  have he : (localActor K L v).subtype '' {x : localActor K L v | orderOf x = 3} =
      {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, ((localActor K L v).orderOf_coe y).trans hy⟩
    · rintro ⟨hx, ho⟩
      exact ⟨⟨x, hx⟩, ((localActor K L v).orderOf_coe ⟨x, hx⟩).symm.trans ho, rfl⟩
  rw [he] at hm
  exact ⟨hm, (Lv_le_cubic_closure_sup K L v hcard).trans_eq hm⟩

/-- The source rank-two branch of 13.6.20, with the A.3.18 application
proved for every surviving concrete model. Only genuine earlier A.3.6 and
A.3.12 classification inputs remain. -/
theorem source_rank_two_without_A318
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
        ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
        ∀ (S : Sylow 2 X) (B : Subgroup X), B ∈ ChapterA.Section03.localCComponents S →
          ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    {T : Sylow 2 G} {K L : Subgroup G} {z v : G} (d : SourceInputs T K L z v) :
    closure {x : G | x ∈ K ⊔ Lv L v ∧ orderOf x = 3} = K ∧ Lv L v ≤ K := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a := source_application hA36 hA312 d
  let H := localActor K L v
  let C := localComponent K L v
  let Q := C ⧸ pCore 2 C
  let B := C.map (QuotientGroup.mk' (pCore 2 H))
  let eQ : Q ≃* B := cComponentTwoCoreQuotientEquiv a.component
  let : IsQuasisimple Q := a.local_quasisimple
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv eQ
  have hR := plus_twoCore_eq_bot_of_reduced K L (T : Subgroup G) z v
    d.normalizes_residual d.centralizes_z d.reduced_module
  let : IsQuasisimple (plusImage K L (T : Subgroup G) z v
      d.normalizes_residual d.centralizes_z K) :=
    plusImage_K_quasisimple K L (T : Subgroup G) z v
      d.normalizes_residual d.centralizes_z d.selected hR
  let ecQ : (Q ⧸ center Q) ≃* (plusImage K L (T : Subgroup G) z v
      d.normalizes_residual d.centralizes_z K ⧸
      center (plusImage K L (T : Subgroup G) z v
        d.normalizes_residual d.centralizes_z K)) :=
    (centerQuotientCongr (localTwoCoreEquiv K L v)).trans
      (intrinsicPlusCentralQuotientEquiv d.standing.qtke hA36 K L (T : Subgroup G)
        z v d.involution d.selected d.rank_two d.normalizes_residual d.centralizes_z hR)
  let ecB := (centerQuotientCongr eQ.symm).trans ecQ
  have hrH : primeRank 3 H ≤ 2 :=
    a.actor_sqtk.stronglyQuasithin 3 Nat.prime_three (by decide)
  have hrQ : 2 ≤ primeRank 3 Q := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup, a.component_rank]
  have hrB : 2 ≤ primeRank 3 B := by rwa [← primeRank_congr 3 eQ]
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_, a.actor_sqtk.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (a.actor_sqtk.stronglyQuasithin p hp ho)
  have ha : A36Conclusion B :=
    proposition_1_2_1_four_earlier_conclusion hA36 hsqQ a.component
  cases ha.1 with
  | simple hcomponent hsimple _ =>
    let := hsimple
    have hzB : center B = ⊥ := by
      rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
    have hfB := central_factor_facts d.reduced_model
      ((quotientOfCenterless hzB).symm.trans ecB) hrB
    have hfQ := Facts.of_equiv eQ hfB
    have hres := a.component.eq_primeToResidual_three_of_rank_outer_two
      hfQ.1 hfQ.2.1 hrH hfQ.2.2
    exact source_residual_case K L (T : Subgroup G) z v d.selected d.rank_two
      a.intrinsic_quasisimple a.intrinsic_center_rank hres d.cubic_quotient
  | cover hcomponent hcenter hmodel =>
    obtain ⟨ez⟩ := hcenter
    have hcB : Nat.card (center B) = 3 := by rw [Nat.card_congr ez.toEquiv]; simp
    have hcQ : Nat.card (center Q) = 3 :=
      (Nat.card_congr (centerCongr eQ).toEquiv).trans hcB
    let : C.Normal := normal_of_core_center_small a.component hcQ.le hrQ hrH
    apply source_of_local_theta (hcard := d.cubic_quotient)
    cases hmodel with
    | classical unitary q _ hm =>
      exact (common_factor_not_signed d.reduced_model ecB unitary q
        (cover_congruence hcB hm) (Or.inr hm)).elim
    | alternating_six hm =>
      obtain ⟨e⟩ := hm.2.2
      exact SixCComponentTheta.cubic_closure_eq_of_central_quotient_six
        C a.component ((centerQuotientCongr eQ).trans e) hrH
    | alternating_seven hm =>
      obtain ⟨e⟩ := hm.2.2
      obtain ⟨f⟩ := GLS3.Chapter5.OddCentralCovers.triple_seven_equiv
        ((centerQuotientCongr eQ).trans e) hcQ
      exact cubic_closure_of_triple_seven C a.component f
        (by rw [a.component_rank]) a.local_center_rank hrH
    | mathieu hm => exact (reduced_not_m22 d.reduced_model ecB hm).elim
  | natural h => have := rank_natural h; omega
  | nilpotent h => have := rank_nilpotent h; omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
