module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Parabolic
public import Theory.GroupTheory.CComponent.ThreeResidual
public import Theory.GroupTheory.PResidual.PrimeToMonotone
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.SpecificGroups.BinaryLinear.OuterTwo
public import Theory.Mathieu.M24.Properties.Sylow3
public import Theory.Mathieu.M24.Properties.OuterRestriction
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.SpecificGroups.Janko4.Model.Center

/-!
# The first-node residual lies in each large point component

The actual quotients L₅(2), M₂₄ and J₄ are centerless, have cubic rank at
least two and have outer automorphism groups of two-power order. Relative
normality and the SQTK rank bound therefore make the original point
component have index prime to three in G₁. The cubic residual of G₁ lies
in that component. Since the literal Y = O²(P) also equals O³′(P),
functoriality proves Y ≤ K₁ with the original embedding unchanged.

Thus each of the three allowed large quotient models supplies the full
large alternative of 12.5.3, including its previously missing residual
containment. PointCore.PointModels applies it to the original component,
point-core, point-control and generation-one consumers. The remaining
quasisimple model sieve and normalizer arguments belong to qt-d-1251-local;
final exterior assembly belongs to qt-d-1251-source.

Source: Aschbacher--Smith, 12.5.3, printed pp.817--818, using the
centerless rank-two argument of A.3.18, printed pp.51--52.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02

private theorem nonabelian_three_subgroup_rank
    {A : Type*} [Group A] [Finite A] (P : Subgroup A)
    (hc : Nat.card P = 3^3) (hna : ¬IsMulCommutative P) :
    2 ≤ primeRank 3 A := by
  have hP : IsPGroup 3 P := IsPGroup.of_card hc
  have hr : 2 ≤ primeRank 3 P := by
    by_contra hn
    have hone : primeRank 3 P ≤ 1 := by omega
    let : IsCyclic P := hP.isCyclic_of_odd_of_elementary_card_le (by decide)
      (fun E hE => by
        let : IsElementaryAbelian 3 E := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hone E)
    exact hna inferInstance
  exact hr.trans (primeRank_subgroup_le 3 P)

private theorem transport_point_residual_inputs
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) (hz : center B = ⊥) (hr : 2 ≤ primeRank 3 B)
    (ho : IsPGroup 2 (MulAut.Outer B)) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  refine ⟨?_,by rwa [primeRank_congr 3 e],ho.of_equiv (MulAut.outerCongr e).symm⟩
  apply le_bot_iff.mp
  intro x hx
  have he : e x = 1 := hz.le ((centerCongr e) ⟨x,hx⟩).property
  exact e.map_eq_one_iff.mp he

private theorem large_point_residual_inputs
    {A : Type*} [Group A] [Finite A]
    (hm : ClassicalGroup.IsPSL A 5 2 ∨ Nonempty (A ≃* Sporadic.Mathieu.M24) ∨
      Nonempty (A ≃* Janko4.Model)) :
    center A = ⊥ ∧ 2 ≤ primeRank 3 A ∧ IsPGroup 2 (MulAut.Outer A) := by
  rcases hm with hm | hm | hm
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    have hc : Fintype.card F = Fintype.card (ZMod 2) := by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF
    let a := (e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))
    exact transport_point_residual_inputs a
      (BinaryLinear.OuterCyclic.binary_center_eq_bot (by decide)) BinaryLinear.SmallCubicRank.five
      (BinaryLinear.OuterCyclic.sl_outer_isTwoGroup (.inr rfl))
  · exact transport_point_residual_inputs hm.some
      Sporadic.Mathieu.M24InvolutionCentralizers.center_eq_bot
      (nonabelian_three_subgroup_rank Sporadic.Mathieu.m24Sylow3Subgroup
        Sporadic.Mathieu.m24Sylow3Subgroup_card Sporadic.Mathieu.m24Sylow3Subgroup_isNonabelian)
      Sporadic.Mathieu.M24OuterRestriction.outer_isPGroup_two
  · exact transport_point_residual_inputs hm.some Janko4.model_center_eq_bot
      (nonabelian_three_subgroup_rank
        (Janko4.Simplicity.threeLocalSubgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
        (Janko4.Simplicity.threeLocal_card _ _) (Janko4.Simplicity.threeLocal_not_isMulCommutative _ _))
      Janko4.AdequateLocal.outer_isPGroup_two

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- Each allowed large point quotient makes the actual relative component index prime to three. -/
theorem point_component_index_coprime_three_of_large_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    Nat.Coprime 3 (K.subgroupOf (s.marking.Gi 1)).index := by
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  let a := subgroupOfEquivOfLe hK.1
  let e := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  obtain ⟨hz,hr,ho⟩ := large_point_residual_inputs hm
  obtain ⟨hzC,hrC,hoC⟩ := transport_point_residual_inputs e hz hr ho
  let : C.Normal := hN
  apply cComponent_index_coprime_three_of_quotient C hK.2 hzC hrC
    ((h.simpleQTKE.twoLocal_sqtk (s.marking.Gi_twoLocal 1 (.inl rfl))).stronglyQuasithin
      3 (by decide) (by decide))
  obtain ⟨n,hn⟩ := hoC.exists_card_dvd_pow
  exact ((show Nat.Coprime 3 2 by decide).pow_right n).coprime_dvd_right hn

/-- The actual first-node two-residual lies in the point component in all three large rows. -/
theorem Y_le_point_component_of_large_model
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) : s.Y ≤ K := by
  let H := s.marking.Gi 1
  let C := K.subgroupOf H
  let : C.Normal := hN
  have hc : primeToResidual 3 H ≤ C := primeToResidual_le C
    (s.point_component_index_coprime_three_of_large_model h hK hN hm)
  rw [s.Y_eq_primeToThree]
  exact (embedded_primeToResidual_mono 3 (s.P_le_M₁.trans inf_le_right)).trans
    ((map_mono (f := H.subtype) hc).trans_eq (map_subgroupOf_eq_of_le hK.1))

/-- The full large source alternative, with its residual containment proved from the model. -/
theorem local_point_component_large_alternative
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 5 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) :
    LocalComponentAlternative s 1 K :=
  .large rfl hm (s.Y_le_point_component_of_large_model h hK hN hm)

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
