module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.EightPathAction.SecondKernel
public import Theory.GroupTheory.CentralBinarySelfCentralizer
public import Theory.GroupTheory.BinaryCentralCommutatorQuotient

/-!
# The original quintic core action and its middle path kernel

Let Q=O₂(H), U=⟨Vᴴ⟩ and Z=Ω₁Z(T). The source relation [Q,U]≤Z
makes commutation a binary pairing. Its two radicals are the literal
centralizers C_Q(U) and C_U(Q), so their relative indices agree.
Since Z≤C_U(Q), |U|≤64 and the earlier faithful-action bound gives
|Q:C_Q(U)|≥16, this index is 16 or32. Every square in Q centralizes U,
so Q/C_H(U) is elementary abelian, with the normality in Q explicit.

The identified second-ball kernel is C_H(U). In the Suzuki quotient row
it consequently has order |T|/64 or |T|/128 at every quintic vertex.
The four-path consumer in `EightPathAction` makes the middle second-ball
kernel a normal subgroup of index four or eight in the actual path fixer.
This does not yet construct the local order-four endpoint actor.

Source: Aschbacher--Smith F.9.7, p.321;14.2.6 and14.2.20--21,
pp.982,988--989. Both original quotient alternatives are retained in the
pairing and elementary-quotient results. Final path assembly, including
D₁₀ exclusion, remains with qt-e-quintic-sylow-lower.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The two radicals of the original central commutator pairing have equal indices. -/
theorem source_quintic_core_centralizer_duality
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    (centralizer (U : Set G)).relIndex Q =
      (centralizer (Q : Set G)).relIndex U := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let Z := centralInvolutions T
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_,hlocal,_,_,_,_⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hcomm : ⁅Q,U⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H,H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule,hp,commutator_comm] using hh
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  let UQ := U.subgroupOf Q
  let ZQ := Z.subgroupOf Q
  let : IsElementaryAbelian 2 UQ := IsElementaryAbelian.subgroupOf hUQ
  let : UQ.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  have hZc : ZQ ≤ center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext ((mem_centralizer_iff.mp (hQZ q.property) _ hz).symm)
  have hZcard : Nat.card ZQ = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hZU.trans hUQ)).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hcommQ : ⁅(⊤ : Subgroup Q),UQ⁆ ≤ ZQ := by
    apply commutator_le.mpr
    intro q _ u hu
    change ⁅(q:G),(u:G)⁆ ∈ Z
    exact hcomm (commutator_mem_commutator q.property hu)
  have hpair := centralizer_relIndex_eq_of_central_binary_commutators
    (⊤ : Subgroup Q) UQ ZQ le_top hZc hcommQ hZcard
  have hCQ : centralizer (UQ : Set Q) = (centralizer (U : Set G)).subgroupOf Q := by
    ext q
    constructor
    · intro hq u hu
      exact congrArg Q.subtype (hq ⟨u,hUQ hu⟩ hu)
    · intro hq u hu
      exact Subtype.ext (hq u hu)
  have hRQ : centralizer ((⊤ : Subgroup Q) : Set Q) =
      (centralizer (Q : Set G)).subgroupOf Q := by
    ext q
    constructor
    · intro hq x hx
      exact congrArg Q.subtype (hq ⟨x,hx⟩ (mem_top _))
    · intro hq x _
      exact Subtype.ext (hq x x.property)
  rw [hCQ,relIndex_top_right,hRQ] at hpair
  have hright : ((centralizer (Q : Set G)).subgroupOf Q).relIndex UQ =
      (centralizer (Q : Set G)).relIndex U := by
    exact relIndex_subgroupOf hUQ
  exact hpair.trans hright

/-- The actual action of the quintic core on its elementary span has order sixteen or thirty-two. -/
theorem source_quintic_core_action_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    (centralizer (U : Set G)).relIndex (H.pCoreIn 2) = 16 ∨
      (centralizer (U : Set G)).relIndex (H.pCoreIn 2) = 32 := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let Z := centralInvolutions T
  let r := (centralizer (U : Set G)).relIndex Q
  have hpair := source_quintic_core_centralizer_duality hG T hempty hM hu hmany hcard e H hH hi
  have hCQ : C ≤ Q := by
    have hh := (show ((Q ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H).normalCore.map H.subtype ≤ Q from
        (map_mono (f := H.subtype)
          ((Q ⊓ (sourceResidual M Mc ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf H).normalCore_le).trans (by
            rw [map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 H))]
            exact inf_le_left))
    rw [source_quintic_crossing_core_normalCore hG T hempty hM hu hmany hcard e H hH] at hh
    exact hh
  have hQC : Q ⊓ centralizer (U : Set G) = C :=
    le_antisymm (inf_le_inf_right _ (pCoreIn_le 2 H)) (le_inf hCQ inf_le_right)
  have hcount : r * Nat.card C = Nat.card Q := by
    have hh := (C.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv] at hh
    have hir : C.relIndex Q = r := by rw [←hQC,inf_relIndex_left]
    change C.relIndex Q * Nat.card C = Nat.card Q at hh
    rwa [hir] at hh
  have hlow : 16 ≤ r := by
    have hh := source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
    have hqcard : Nat.card Q = Nat.card (pCore 2 H) := card_map_of_injective H.subtype_injective
    have hcpos : 0 < Nat.card C := Nat.card_pos
    change 16 * Nat.card C ≤ Nat.card (pCore 2 H) at hh
    rw [←hqcard,←hcount] at hh
    exact Nat.le_of_mul_le_mul_right hh hcpos
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZC : Z ≤ U ⊓ centralizer (Q : Set G) := le_inf hZU
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2))
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hrad : 2 ≤ Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) := by
    rw [←hZcard]
    exact card_le_of_le hZC
  have hUcard := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).2
  change Nat.card U = 32 ∨ Nat.card U = 64 at hUcard
  have hupp : Nat.card U ≤ 64 := by omega
  have hradcount : r * Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = Nat.card U := by
    have hh := ((centralizer (Q : Set G)).subgroupOf U).index_mul_card
    rw [←inf_subgroupOf_left,Nat.card_congr (subgroupOfEquivOfLe
      (show U ⊓ centralizer (Q : Set G) ≤ U from inf_le_left)).toEquiv] at hh
    rw [show r = (centralizer (Q : Set G)).relIndex U from hpair]
    change (U ⊓ centralizer (Q : Set G)).relIndex U * _ = _ at hh
    rwa [inf_relIndex_left] at hh
  have huppR : r ≤ 32 := by nlinarith
  have hdiv : r ∣ Nat.card Q := by exact relIndex_dvd_card _ _
  have hQp : IsPGroup 2 Q := isPGroup_pCoreIn 2 H
  obtain ⟨n,hn⟩ := hQp.exists_card_eq
  rw [hn] at hdiv
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  have hklo : 4 ≤ k := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show k ≤ 3 by omega)
    omega
  have hkhi : k ≤ 5 := by
    by_contra! h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 6 ≤ k by omega)
    omega
  change r = 16 ∨ r = 32
  rcases (show k = 4 ∨ k = 5 by omega) with h | h <;> simp_all

/-- Every square in the original quintic core centralizes the full neighbor span. -/
theorem source_quintic_core_square_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    ∀ q ∈ H.pCoreIn 2,
      q ^ 2 ∈ H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let Z := centralInvolutions T
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 Z := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (setLike_mul_comm (hZU x.property) (hZU y.property))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) z (hZU z.property)) }
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_,hlocal,_,_,_,_⟩ := hloc H hH.1
  have hc : ⁅Q,U⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H,H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule,hp,commutator_comm] using hh
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  intro q hq
  exact ⟨H.pow_mem (pCoreIn_le 2 H hq) 2,
    sq_mem_centralizer_of_central_commutators Q U Z hQZ hc hq⟩

/-- The exact centralizer index gives the two possible second-kernel orders in the Suzuki row. -/
theorem source_quintic_second_kernel_exact_card_of_suzuki
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (eH : (H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let F := ChapterF.Section07.Geometry.family X H
    ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true →
      64 * Nat.card (Subgroup.CosetGeometry.RankTwo.ballKernel F v 2) = Nat.card (T : Subgroup G) ∨
      128 * Nat.card (Subgroup.CosetGeometry.RankTwo.ballKernel F v 2) = Nat.card (T : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let F := ChapterF.Section07.Geometry.family X H
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  have hCQ : C ≤ Q := by
    change H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) ≤ Q
    rw [←source_quintic_crossing_core_normalCore hG T hempty hM hu hmany hcard e H hH]
    exact (map_mono (f := H.subtype)
      ((Q ⊓ X.pCoreIn 2).subgroupOf H).normalCore_le).trans (by
        rw [map_subgroupOf_eq_of_le (inf_le_left.trans (pCoreIn_le 2 H))]
        exact inf_le_left)
  have hQC : Q ⊓ centralizer (U : Set G) = C :=
    le_antisymm (inf_le_inf_right _ (pCoreIn_le 2 H)) (le_inf hCQ inf_le_right)
  have hcount := (C.subgroupOf Q).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hCQ).toEquiv] at hcount
  change C.relIndex Q * Nat.card C = Nat.card Q at hcount
  have hiC : C.relIndex Q = (centralizer (U : Set G)).relIndex Q := by
    rw [←hQC,inf_relIndex_left]
  rw [hiC] at hcount
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eH.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hc := (pCore 2 H).index_mul_card
  change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
  rw [hquot] at hc
  have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
  rw [hi] at ht
  have hQc : Nat.card Q = Nat.card (pCore 2 H) := card_map_of_injective H.subtype_injective
  rw [hQc] at hcount
  have hbase : Nat.card (Subgroup.CosetGeometry.RankTwo.ballKernel F
      (Subgroup.CosetGeometry.base F true) 2) = Nat.card C := by
    dsimp only [C,U]
    rw [←source_quintic_second_ball_kernel hG T hempty hM hu hmany hcard e H hH hi,
      card_map_of_injective (X ⊔ H).subtype_injective]
  change ∀ v : Subgroup.CosetGeometry.Vertex F, v.type = true → _
  intro v hv
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  rw [←hg,Subgroup.CosetGeometry.RankTwo.ballKernel_translate,
    card_map_of_injective (MulAut.conj g).injective,hbase]
  have hidx := source_quintic_core_action_index hG T hempty hM hu hmany hcard e H hH hi
  change (centralizer (U : Set G)).relIndex Q = 16 ∨
    (centralizer (U : Set G)).relIndex Q = 32 at hidx
  rcases hidx with hidx | hidx <;> rw [hidx] at hcount <;> omega

/-- The quotient of the quintic core by its action kernel is elementary abelian. -/
theorem source_quintic_core_action_elementary
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    ∃ hC : (C.subgroupOf Q).Normal,
      let _ := hC
      IsElementaryAbelian 2 (Q ⧸ C.subgroupOf Q) := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  have hn : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer U))).trans inf_normalizer_le_normalizer_inf
  let hC : (C.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans hn)
  let _ := hC
  refine ⟨hC,?_⟩
  have hsquare : ∀ x : Q ⧸ C.subgroupOf Q, x ^ 2 = 1 := by
    intro x
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf Q) x
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact source_quintic_core_square_centralizes hG T hempty hM hu hmany hcard e H hH hi q q.property
  exact {
    is_comm := ⟨fun x y => (Commute.of_orderOf_dvd_two
      (fun a => orderOf_dvd_of_pow_eq_one (hsquare a)) x y).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
