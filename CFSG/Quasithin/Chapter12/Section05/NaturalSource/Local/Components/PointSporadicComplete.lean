module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Components.PointSporadic
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.Mathieu.M22.Properties.ThreeRank
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.Mathieu.TwentyTwoReduction
public import Theory.Mathieu.M22.Properties.AutomorphismCoverage
public import Theory.Mathieu.M23.Properties.OuterRestriction
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.PointParabolic
public import Theory.SpecificGroups.Held.ComponentFacts
public import Theory.SpecificGroups.Held.TwoLocalCandidates.OrderObstruction
public import Theory.SpecificGroups.Held.TwoPartDivisibility
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.SL2.BinaryThreeSection

/-!
# Completing the sporadic point-component sieve

The original M1* has two-core quotient of order 1008. Its intersection with
K1* therefore has nontrivial two-core whenever the component Sylow has order
divisible by 32: otherwise that Sylow would embed in the order-1008 quotient.
Cubic rank and the outer two-group first put the actual Y inside K1, so the
intersection has the original Sylow index 63. Its core normalizer contradicts
the native M22 and Held two-local order bounds and the M23 index obstruction.
J1 is excluded separately by its elementary Sylow subgroups and the original
SL3(2) section. All transports preserve the original embeddings and quotients.

Combined with PointSporadic, this leaves only the allowed M24 and J4 models
in the complete sporadic part of the source catalogue. PointCore.PointSporadicComplete
constructs LocalComponents and feeds the original point-core, point-control
and generation-one consumers. The odd ternary and central-cover point rows,
general normalizers and quasisimple escape remain with qt-d-1251-local;
qt-d-1251-source owns final exterior assembly.
Source: Aschbacher--Smith 12.5.3, pp.817--818, using A.3.12 and A.3.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)

/-- The unchanged two-block quotient forces a nontrivial core in a large Sylow intersection. -/
theorem pointComponentParabolic_core_ne_bot {K : Subgroup G}
    (S : Sylow 2 (s.pointCoreImage K))
    (hS : (S : Subgroup _) ≤ s.pointComponentParabolic K)
    (h32 : 32 ∣ Nat.card S) : pCore 2 (s.pointComponentParabolic K) ≠ ⊥ := by
  let A := s.pointCoreImage (s.marking.Mi 1)
  let J := s.pointComponentParabolic K
  let f : J →* A := {
    toFun x := ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : A => z.val) hxy
  let q := (QuotientGroup.mk' (pCore 2 A)).comp f
  have hq : IsPGroup 2 q.ker := by
    have hk : q.ker = (pCore 2 A).comap f := by
      ext x
      exact QuotientGroup.eq_one_iff (f x)
    rw [hk]
    exact pCore_isPGroup.comap_of_injective f hf
  intro he
  have hker : q.ker = ⊥ := bot_unique
    ((le_sSup ⟨inferInstance,hq⟩ : q.ker ≤ pCore 2 J).trans_eq he)
  let g := q.comp (inclusion hS)
  have hg : Function.Injective g :=
    ((MonoidHom.ker_eq_bot_iff q).mp hker).comp (inclusion_injective hS)
  have hd := h32.trans (card_dvd_of_injective g hg)
  rw [show Nat.card (A ⧸ pCore 2 A) = 1008 from s.pointCoreImage_M₁_core_card] at hd
  norm_num at hd

/-- The actual J1 quotient cannot support the original binary-three section. -/
theorem point_component_not_jankoOne {K : Subgroup G}
    (hLK : s.marking.Li 1 ≤ K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model) := by
  rintro ⟨e⟩
  let B := s.marking.Li 1
  let π := (s.marking.LiCoreEquiv 1 (.inl rfl)).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 B))
  let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hLK))
  have hf : IsPGroup 2 f.ker := by
    have he : f.ker = (pCore 2 K).comap (inclusion hLK) := by
      ext x
      change e (QuotientGroup.mk' (pCore 2 K) (inclusion hLK x)) = 1 ↔ _
      rw [e.map_eq_one_iff]
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hLK)
  apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_subgroup_exponent
    (X := Janko1.Model) _ π
    ((s.marking.LiCoreEquiv 1 (.inl rfl)).surjective.comp (QuotientGroup.mk'_surjective _)) f hf
  intro P hP x
  obtain ⟨S,hS⟩ := hP.exists_le_sylow
  let := Janko1.SylowTwo.elementary S
  exact (inclusion_injective hS) (by
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S) _)

private theorem point_component_impossible_of_twoLocal_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    {X : Type*} [Group X] [Finite X] (e : (K ⧸ pCore 2 K) ≃* X)
    (hz : center X = ⊥) (hr : 2 ≤ primeRank 3 X) (ho : IsPGroup 2 (MulAut.Outer X))
    (h32 : 32 ∣ Nat.card X)
    (hn : ∀ (S : Sylow 2 X) (J : Subgroup X), (S : Subgroup X) ≤ J →
      pCore 2 J ≠ ⊥ → (S : Subgroup X).relIndex J = 63 → False) : False := by
  have hY := s.Y_le_point_component_of_model h hK hN e hz hr ho
  obtain ⟨S,hS,hi⟩ := s.pointComponentParabolic_sylow_index hK.1 hN hLK hY
  let a := (s.pointComponentCoreEquivImage hK.1 hN).symm.trans e
  let R := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let J := (s.pointComponentParabolic K).map a.toMonoidHom
  have hSJ : (R : Subgroup X) ≤ J := map_mono hS
  have hidx : (R : Subgroup X).relIndex J = 63 := by
    change ((S : Subgroup _).map a.toMonoidHom).relIndex
      ((s.pointComponentParabolic K).map a.toMonoidHom) = 63
    rw [relIndex_map_map_of_injective _ _ a.injective]
    exact hi
  have h32S : 32 ∣ Nat.card S := by
    apply S.pow_dvd_card_of_pow_dvd_card (n := 5)
    rwa [Nat.card_congr a.toEquiv]
  have hc := s.pointComponentParabolic_core_ne_bot S hS h32S
  have hcJ : pCore 2 J ≠ ⊥ := by
    intro he
    let b := a.subgroupMap (s.pointComponentParabolic K)
    have hb := pCore_map_iso 2 b
    change (pCore 2 (s.pointComponentParabolic K)).map b.toMonoidHom = pCore 2 J at hb
    rw [he] at hb
    exact hc ((map_eq_bot_iff_of_injective _ b.injective).mp hb)
  exact hn R J hSJ hcJ hidx

private theorem twoLocal_normalizer_of_core {X : Type*} [Group X] [Finite X]
    (J : Subgroup X) (hc : pCore 2 J ≠ ⊥) :
    IsTwoLocal (normalizer (J.pCoreIn 2 : Set X)) := by
  refine ⟨J.pCoreIn 2,?_,pCore_isPGroup.map J.subtype,rfl⟩
  intro he
  exact hc ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)

/-- The original point parabolic is incompatible with a Mathieu22 quotient. -/
theorem point_component_not_mathieuTwentyTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨e⟩
  refine s.point_component_impossible_of_twoLocal_index h hK hLK hN e
    Sporadic.Mathieu.m22_center_eq_bot
    (by rw [Sporadic.Mathieu.m22_primeRank_three])
    (Chapter1.XiEmbedding.OuterModels.m22_outer_isPGroup_two_of_coverage
      Sporadic.Mathieu.m22DesignAutToAut_surjective)
    (by rw [Sporadic.Mathieu.m22_order]; decide) ?_
  intro S J hSJ hc hi
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set Sporadic.Mathieu.M22) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  apply Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal S _
    (twoLocal_normalizer_of_core J hc) (hSJ.trans hJN)
  have hd : 63 ∣ Nat.card J := by
    simpa only [hi] using relIndex_dvd_card (S : Subgroup _) J
  exact ((by decide : 7 ∣ 63).trans hd).trans (card_dvd_of_le hJN)

/-- The original point parabolic is incompatible with a Held quotient. -/
theorem point_component_not_held
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Held.He) := by
  rintro ⟨e⟩
  refine s.point_component_impossible_of_twoLocal_index h hK hLK hN e
    Held.LocalPairs.center_eq_bot Held.three_rank_ge_two Held.outer_isPGroup_two
    (by exact (by decide : 32 ∣ 2^10).trans Held.two_pow_ten_dvd_card) ?_
  intro S J hSJ hc hi
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set Held.He) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  apply Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal S _
    (twoLocal_normalizer_of_core J hc) (hSJ.trans hJN)
  have hd : 63 ∣ Nat.card J := by
    simpa only [hi] using relIndex_dvd_card (S : Subgroup _) J
  exact hd.trans (card_dvd_of_le hJN)

/-- The actual M23 quotient is excluded by its native two-local catalogue. -/
theorem point_component_not_mathieuTwentyThree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) := by
  rintro ⟨e⟩
  have hr : 2 ≤ primeRank 3 Sporadic.Mathieu.M23 := by
    let f := (MulAction.stabilizer Sporadic.Mathieu.M23 (9 : Fin 23)).subtype.comp
      Sporadic.Mathieu.m23EquivM22PointStabilizer.toMonoidHom
    have hf : Function.Injective f := Subtype.val_injective.comp
      Sporadic.Mathieu.m23EquivM22PointStabilizer.injective
    have hh := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
    rwa [Sporadic.Mathieu.m22_primeRank_three] at hh
  exact s.point_component_impossible_of_twoLocal_index h hK hLK hN e
    Sporadic.Mathieu.M23Geometry.m23_center_eq_bot hr Sporadic.Mathieu.m23_outer_isTwoGroup
    (by rw [Sporadic.Mathieu.m23_order]; decide)
    Sporadic.Mathieu.M23Geometry.SylowTwoLocals.no_sixtyThree_index_of_core_ne_bot

/-- Only the two permitted large sporadic models survive the original point sieve. -/
theorem point_sporadic_model_large
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) : name = .m24 ∨ name = .j4 := by
  rcases s.point_sporadic_model_remaining h hK hLK hN name hj hm with he | he | he | he | he
  · subst name
    exact (s.point_component_not_mathieuTwentyTwo h hK hLK hN hm).elim
  · subst name
    exact (s.point_component_not_mathieuTwentyThree h hK hLK hN hm).elim
  · exact .inl he
  · exact .inr he
  · subst name
    exact (s.point_component_not_held h hK hLK hN hm).elim

/-- The complete sporadic point-model family gives the source component alternative,
including the original first-node residual containment. -/
theorem local_point_component_alternative_of_sporadic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (name : ClassificationModels.SporadicName) (hj : name ≠ .j3)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) :
    LocalComponentAlternative s 1 K := by
  rcases s.point_sporadic_model_large h hK hLK hN name hj hm with he | he
  · subst name
    exact s.local_point_component_large_alternative h hK hN (.inr (.inl hm))
  · subst name
    exact s.local_point_component_large_alternative h hK hN (.inr (.inr hm))

/-- The separate J1 catalogue constructor and every permitted sporadic tag
are handled on the same original component quotient. -/
theorem local_point_component_alternative_of_sporadic_or_jankoOne
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (hm : (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko1.Model)) : LocalComponentAlternative s 1 K := by
  rcases hm with ⟨name,hj,hm⟩ | hm
  · exact s.local_point_component_alternative_of_sporadic h hK hLK hN name hj hm
  · exact (s.point_component_not_jankoOne hLK hm).elim

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
