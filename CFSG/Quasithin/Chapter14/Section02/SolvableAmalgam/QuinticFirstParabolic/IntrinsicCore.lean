module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.LowerBound
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.CoreClass

/-!
# Intrinsic structure from an upper bound on the original quintic core

Under the original source hypotheses, an upper bound |O₂(H)|≤512 combines
with the proved Sylow lower bound to force the Suzuki quotient, |T|=2048,
|O₂(H)|=512 and |U|=32, where U is the original conjugate closure.
The action bound makes U self-centralizing in H. Binary commutator duality
then identifies the core center with the original central involution.
The unconditional cubic conjugate-intersection theorem excludes class two, and the
order-five action fixes exactly that central involution in the core.

The local arguments are adapted from `SmallCore`, replacing its excluded
premise |T|<2048 by the actual two-core upper bound. In the class-three
argument the cubic vertex now has order 6144; the required strict inequality
512² > 32·6144 still holds. The upper bound itself remains to be proved;
no whole-parabolic equivalence or generating tuple is used here.

Source: Aschbacher--Smith 14.2.6 and 14.2.20--21, pp.982,988--989;
Parrott (1972), Lemma 1, p.672. The actual centralizer consumer is
`IntrinsicCentralizer`; final discharge stays with qt-e-quintic-first-parabolic.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- An upper bound of 512 on the original two-core forces equality, the
Suzuki quotient, the order-2048 Sylow and the order-32 elementary closure.
The dihedral quotient is excluded by the proved original Sylow lower bound. -/
theorem source_core512_orders
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∧
      Nat.card (T : Subgroup G) = 2048 ∧ Nat.card (pCore 2 H) = 512 ∧
      Nat.card (conjugateSpanBy (localModule T M) H) = 32 := by
  have hb := source_quintic_core_lower hG T hempty hM hu hmany hcard e H hH hi
  have hU := (source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).2
  have hUcard : Nat.card (conjugateSpanBy (localModule T M) H) = 32 := by
    rcases hU with hU | hU
    · exact hU
    · rw [hU] at hb
      omega
  have hQcard : Nat.card (pCore 2 H) = 512 := by
    rw [hUcard] at hb
    omega
  have hlower := source_quintic_sylow_lower hG T hempty hM hu hmany hcard e H hH hi
  have hc := (pCore 2 H).index_mul_card
  change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
  rw [hQcard] at hc
  have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
  rw [hi] at ht
  rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hD | hS
  · obtain ⟨eD⟩ := hD
    have hquot : Nat.card (H ⧸ pCore 2 H) = 10 :=
      (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
    rw [hquot] at hc
    omega
  · have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
      (Nat.card_congr hS.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
    rw [hquot] at hc
    exact ⟨hS, by omega, hQcard, hUcard⟩

/-- Equality in the direct core bound forces the literal action kernel to be U. -/
private theorem source_core512_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) =
      conjugateSpanBy (localModule T M) H := by
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨_, _, hQ, hUcard⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hlower := source_quintic_action_core_lower
    hG T hempty hM hu hmany hcard e H hH hi
  rw [hQ] at hlower
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ H.pCoreIn 2 := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  apply Eq.symm
  apply eq_of_le_of_card_ge (le_inf (hUQ.trans (pCoreIn_le 2 H)) (le_centralizer U))
  change Nat.card (H ⊓ centralizer (U : Set G) : Subgroup G) ≤ Nat.card U
  change Nat.card U = 32 at hUcard
  change 16 * Nat.card (H ⊓ centralizer (U : Set G) : Subgroup G) ≤ 512 at hlower
  omega

/-- Intrinsic Frattini, commutator, and exponent restrictions on the original order-512 core. -/
private theorem source_core512_core_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    let Q := H.pCoreIn 2
    let U := conjugateSpanBy (localModule T M) H
    (frattini Q).map Q.subtype ≤ U ∧
      ⁅Q,Q⁆ ≤ U ∧ ⁅⁅Q,Q⁆,Q⁆ ≤ centralInvolutions T ∧
      ⁅⁅⁅Q,Q⁆,Q⁆,Q⁆ = ⊥ ∧ Monoid.exponent Q ∣ 4 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  change (frattini Q).map Q.subtype ≤ U ∧ ⁅Q,Q⁆ ≤ U ∧
    ⁅⁅Q,Q⁆,Q⁆ ≤ Z ∧ ⁅⁅⁅Q,Q⁆,Q⁆,Q⁆ = ⊥ ∧ Monoid.exponent Q ∣ 4
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hc : ⁅U,Q⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H, H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule, hp] using hh
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans hHZ
  have hcentralizer : Q ⊓ centralizer (U : Set G) ≤ U := by
    have heq : H ⊓ centralizer (U : Set G) = U :=
      source_core512_centralizer hG T hempty hM hu hmany hcard e H hH hi hQupper
    exact (inf_le_inf_right _ (pCoreIn_le 2 H)).trans heq.le
  let : (U.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 Z := {
    toIsMulCommutative := ⟨⟨fun x y => Subtype.ext
      (setLike_mul_comm (hZU x.property) (hZU y.property))⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) z (hZU z.property)) }
  have hQelem := elementary_quotient_of_central_commutators Q U Z hQZ
    (by simpa only [commutator_comm] using hc) hcentralizer
  have hfrat := frattini_le_of_elementary_quotient (isPGroup_pCoreIn 2 H)
    (U.subgroupOf Q) hQelem
  have hfratG : (frattini Q).map Q.subtype ≤ U := by
    rintro x ⟨a,ha,rfl⟩
    exact hfrat ha
  have hder : ⁅Q,Q⁆ ≤ U := by
    let : Fact (IsPGroup 2 Q) := ⟨isPGroup_pCoreIn 2 H⟩
    have hh := map_mono (f := Q.subtype) (commutator_le_frattini_of_isPGroup (p := 2))
    rw [map_subtype_commutator] at hh
    exact hh.trans hfratG
  have hthree : ⁅⁅Q,Q⁆,Q⁆ ≤ Z := (commutator_mono hder le_rfl).trans hc
  refine ⟨hfratG,hder,hthree,?_,?_⟩
  · apply bot_unique
    apply (commutator_mono hthree le_rfl).trans
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp hQZ)).le
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro q
    apply Subtype.ext
    change (q:G) ^ 4 = 1
    have hsq : (q:G) ^ 2 ∈ U := hcentralizer
      ⟨Q.pow_mem q.property 2,
        sq_mem_centralizer_of_central_commutators Q U Z hQZ
          (by simpa only [commutator_comm] using hc) q.property⟩
    simpa only [← pow_mul] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) _ hsq

/-- The original core of order512 has exactly the original central point as its center. -/
theorem source_core512_core_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype = centralInvolutions T := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  change (center Q).map Q.subtype = Z
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hc : ⁅U,Q⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H, H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule, hp] using hh
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans hHZ
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZQ := hZU.trans hUQ
  let UQ := U.subgroupOf Q
  let ZQ := Z.subgroupOf Q
  let : IsElementaryAbelian 2 UQ := IsElementaryAbelian.subgroupOf hUQ
  let : UQ.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  have hcentralizer : centralizer (UQ : Set Q) = UQ := by
    apply le_antisymm
    · intro q hq
      have heq : H ⊓ centralizer (U : Set G) = U :=
        source_core512_centralizer hG T hempty hM hu hmany hcard e H hH hi hQupper
      apply heq.le
      refine ⟨pCoreIn_le 2 H q.property, ?_⟩
      intro u hu
      exact congrArg Q.subtype (hq ⟨u,hUQ hu⟩ hu)
    · exact le_centralizer UQ
  have hZc : ZQ ≤ center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hQZ q.property) _ hz).symm
  have hZcard : Nat.card ZQ = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hcomm : ⁅(⊤ : Subgroup Q), UQ⁆ ≤ ZQ := by
    apply commutator_le.mpr
    intro q _ u hu
    change ⁅(q:G),(u:G)⁆ ∈ Z
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator q.property hu)
  have hcount := card_sq_eq_card_mul_center_of_central_binary_selfCentralizer
    UQ ZQ hZc hZcard hcomm hcentralizer
  obtain ⟨_, _, hQcard, hUcard⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hQcard' : Nat.card Q = 512 :=
    (card_map_of_injective H.subtype_injective).trans hQcard
  have hUcard' : Nat.card UQ = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv).trans hUcard
  rw [hQcard',hUcard'] at hcount
  have hcCard : Nat.card (center Q) = 2 := by omega
  have heq : ZQ = center Q := eq_of_le_of_card_ge hZc (by rw [hZcard,hcCard])
  rw [←heq]
  exact map_subgroupOf_eq_of_le hZQ

/-- Every abelian subgroup of the original core of order512 has order at most32. -/
private theorem source_core512_core_abelian_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512)
    (A : Subgroup G) [IsMulCommutative A] (hAQ : A ≤ H.pCoreIn 2) :
    Nat.card A ≤ 32 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hc : ⁅U,Q⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H, H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule, hp] using hh
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hQZ : Q ≤ centralizer (Z : Set G) := (pCoreIn_le 2 H).trans hHZ
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZQ := hZU.trans hUQ
  let UQ := U.subgroupOf Q
  let ZQ := Z.subgroupOf Q
  let : IsElementaryAbelian 2 UQ := IsElementaryAbelian.subgroupOf hUQ
  let : UQ.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  have hcentralizer : centralizer (UQ : Set Q) = UQ := by
    apply le_antisymm
    · intro q hq
      have heq : H ⊓ centralizer (U : Set G) = U :=
        source_core512_centralizer hG T hempty hM hu hmany hcard e H hH hi hQupper
      apply heq.le
      refine ⟨pCoreIn_le 2 H q.property, ?_⟩
      intro u hu
      exact congrArg Q.subtype (hq ⟨u,hUQ hu⟩ hu)
    · exact le_centralizer UQ
  have hZc : ZQ ≤ center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hQZ q.property) _ hz).symm
  have hZcard : Nat.card ZQ = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hcomm : ⁅(⊤ : Subgroup Q), UQ⁆ ≤ ZQ := by
    apply commutator_le.mpr
    intro q _ u hu
    change ⁅(q:G),(u:G)⁆ ∈ Z
    rw [commutator_comm] at hc
    exact hc (commutator_mem_commutator q.property hu)
  have hb := card_abelian_le_of_central_binary_selfCentralizer UQ ZQ (A.subgroupOf Q)
    hZc hZcard hcomm hcentralizer
  rw [Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv] at hb
  have hUcard := (source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper).2.2.2
  exact hb.trans_eq hUcard

/-- The original cubic geometry excludes class two and identifies the third commutator. -/
private theorem source_core512_core_third_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    ⁅⁅H.pCoreIn 2,H.pCoreIn 2⁆,H.pCoreIn 2⁆ = centralInvolutions T := by
  let Q := H.pCoreIn 2
  let Z := centralInvolutions T
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hthree : ⁅⁅Q,Q⁆,Q⁆ ≤ Z := (source_core512_core_structure
    hG T hempty hM hu hmany hcard e H hH hi hQupper).2.2.1
  have hne : ⁅⁅Q,Q⁆,Q⁆ ≠ ⊥ :=
    source_core_third_commutator_ne_bot hG T hempty hM hu hmany hcard e H hH hi
  apply eq_of_le_of_card_ge hthree
  rw [hZcard]
  have hp := Nat.card_pos (α := (⁅⁅Q,Q⁆,Q⁆ : Subgroup G))
  have hn : Nat.card (⁅⁅Q,Q⁆,Q⁆ : Subgroup G) ≠ 1 :=
    fun hc => hne (card_eq_one.mp hc)
  omega

/-- The original order-512 core has class exactly three and exponent exactly four. -/
theorem source_core512_core_class_and_exponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    Group.nilpotencyClass (H.pCoreIn 2) = 3 ∧ Monoid.exponent (H.pCoreIn 2) = 4 := by
  let Q := H.pCoreIn 2
  let : Group.IsNilpotent Q := (isPGroup_pCoreIn 2 H).isNilpotent
  have hstructure := source_core512_core_structure
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hL3 : (⊤ : Subgroup Q).lowerCentralSeries 3 = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ (f := Q.subtype) Q.subtype_injective).mp
    rw [map_lowerCentralSeries,← MonoidHom.range_eq_map,range_subtype]
    exact hstructure.2.2.2.1
  have hc : Group.nilpotencyClass Q = 3 := by
    have hle := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hL3
    have hlo : 3 ≤ Group.nilpotencyClass Q :=
      source_core_nilpotencyClass_lower hG T hempty hM hu hmany hcard e H hH hi
    omega
  refine ⟨hc,?_⟩
  have hn : ¬ Monoid.exponent Q ∣ 2 := by
    intro hd
    have hab : IsMulCommutative Q := ⟨⟨fun a b =>
      (Commute.of_orderOf_dvd_two (fun q => (Monoid.order_dvd_exponent q).trans hd) a b).eq⟩⟩
    have hle := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hab
    omega
  obtain ⟨n,hnle,heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Monoid.exponent Q ∣ 2^2 from hstructure.2.2.2.2)
  interval_cases n
  · exact (hn (by rw [heq]; decide)).elim
  · exact (hn (by rw [heq]; decide)).elim
  · exact heq

/-- Under the core upper bound, every order-five subgroup of H fixes
exactly the original central point inside O₂(H). The fixed subgroup in U
has order two by orbit counting and is already generated by that point.
Source: Aschbacher--Smith 14.2.6 and 14.2.21, pp.982 and 989; Parrott VI,
p.630. -/
theorem source_core512_five_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    H.pCoreIn 2 ⊓ centralizer (A : Set G) = centralInvolutions T := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let D := Q ⊓ centralizer (A : Set G)
  obtain ⟨_, _, _, hUcard⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hC : H ⊓ centralizer (U : Set G) = U :=
    source_core512_centralizer hG T hempty hM hu hmany hcard e H hH hi hQupper
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_,hlocal,_,_,_,_⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hUH := hUQ.trans (pCoreIn_le 2 H)
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  let : MulDistribMulAction H U :=
    conjMulDistribMulActionOfLeNormalizer H U (le_normalizer_conjugateSpanBy _ _)
  let f : H →* MulAut U := MulDistribMulAction.toMulAut H U
  have hk : f.ker = U.subgroupOf H := by
    ext h
    constructor
    · intro hh
      apply hC.le
      refine ⟨h.property,?_⟩
      intro u hu
      have hx := congrArg U.subtype (DFunLike.congr_fun (show f h = 1 from hh) ⟨u,hu⟩)
      change (h:G)*u*(h:G)⁻¹=u at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    · intro hh
      change f h = 1
      ext u
      change (h:G)*(u:G)*(h:G)⁻¹=(u:G)
      rw [setLike_mul_comm (show (h:G) ∈ U from hh) u.property,mul_inv_cancel_right]
  have hkQ : f.ker ≤ pCore 2 H := by
    rw [hk]
    intro h hh
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp (hUQ hh)
  have hDH : D ≤ H := inf_le_left.trans (pCoreIn_le 2 H)
  have hDQ : D.subgroupOf H ≤ pCore 2 H := by
    intro d hd
    exact (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp hd.1
  have hDU : D ≤ U := by
    have hh := two_subgroup_le_kernel_of_centralizes_five_on_thirtyTwo f
      (pCore_isPGroup.to_le hkQ) hUcard (A.subgroupOf H) (D.subgroupOf H)
      ((Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA)
      (pCore_isPGroup.to_le hDQ) (by
        intro d hd a ha
        exact Subtype.ext (hd.2 a ha))
    rw [hk] at hh
    intro d hd
    exact hh (show (⟨d,hDH hd⟩ : H) ∈ D.subgroupOf H from hd)
  let : MulDistribMulAction A U :=
    conjMulDistribMulActionOfLeNormalizer A U
      (hAH.trans (le_normalizer_conjugateSpanBy _ _))
  let C := FixedPoints.subgroup A U
  have hCne : C ≠ ⊤ := by
    intro ht
    have hAU : A ≤ U := by
      intro a ha
      apply hC.le
      refine ⟨hAH ha,?_⟩
      intro u hu
      have hh := congrArg U.subtype ((show (⟨u,hu⟩ : U) ∈ C from ht ▸ mem_top _) ⟨a,ha⟩)
      change a*u*a⁻¹=u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hd := card_dvd_of_le hAU
    rw [hA,hUcard] at hd
    norm_num at hd
  have hCcard : Nat.card C = 2 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hmod := (IsPGroup.of_card (p := 5) (G := A) (n := 1)
      (by simpa using hA)).card_modEq_card_fixedPoints U
    change Nat.card U % 5 = Nat.card C % 5 at hmod
    rw [hUcard] at hmod
    have hdiv : Nat.card C ∣ 32 := hUcard ▸ C.card_subgroup_dvd_card
    have hmem := Nat.mem_divisors.mpr ⟨hdiv,by decide⟩
    rw [show (32 : ℕ).divisors = {1,2,4,8,16,32} by decide] at hmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    have hn : Nat.card C ≠ 32 := fun hh =>
      hCne (C.eq_top_of_card_eq (hh.trans hUcard.symm))
    omega
  have hZC : Z.subgroupOf U ≤ C := by
    intro z hz a
    apply Subtype.ext
    change (a:G)*(z:G)*(a:G)⁻¹=(z:G)
    rw [←mem_centralizer_iff.mp (hHZ (hAH a.property)) z hz,mul_inv_cancel_right]
  have hZcard : Nat.card (Z.subgroupOf U) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZeq : Z.subgroupOf U = C := eq_of_le_of_card_ge hZC (by rw [hZcard,hCcard])
  change D = Z
  apply le_antisymm
  · intro d hd
    have hc : (⟨d,hDU hd⟩ : U) ∈ C := by
      intro a
      apply Subtype.ext
      change (a:G)*d*(a:G)⁻¹=d
      rw [mem_centralizer_iff.mp hd.2 a a.property,mul_inv_cancel_right]
    exact hZeq.ge hc
  · apply le_inf (hZU.trans hUQ)
    exact le_centralizer_iff.mp (hAH.trans hHZ)

/-- The closure U is the derived, Frattini and second upper-central layer of
the order-512 core, by Parrott's order-512 theorem with the literal
order-five conjugation action. Source: Parrott (1972), Lemma 1, p.672. -/
theorem source_core512_characteristic_layers
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    let Q := H.pCoreIn 2
    let U := conjugateSpanBy (localModule T M) H
    ⁅Q,Q⁆ = U ∧ (frattini Q).map Q.subtype = U ∧
      (Subgroup.upperCentralSeries Q 2).map Q.subtype = U ∧
      Nat.card (Q ⧸ frattini Q) = 16 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨_,_,hQcard,hUcard⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hQcard' : Nat.card Q = 512 :=
    (card_map_of_injective H.subtype_injective).trans hQcard
  have hclass := (source_core512_core_class_and_exponent
    hG T hempty hM hu hmany hcard e H hH hi hQupper).1
  have hcenter := source_core512_core_center
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hfive : 5 ∣ Nat.card H := by
    have hh := ((T : Subgroup G).subgroupOf H).index_dvd_card
    change (T : Subgroup G).relIndex H ∣ Nat.card H at hh
    rwa [hi] at hh
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let A := (zpowers a).map H.subtype
  have hAH : A ≤ H := map_subtype_le _
  have hA : Nat.card A = 5 := by
    rw [card_map_of_injective H.subtype_injective,Nat.card_zpowers,ha]
  have hnQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  let : MulDistribMulAction A Q := conjMulDistribMulActionOfLeNormalizer A Q hnQ
  have hfix : FixedPoints.subgroup A Q ≤ center Q := by
    intro q hq
    have hc : (q:G) ∈ centralizer (A : Set G) := by
      intro a ha
      have hh := congrArg Q.subtype (hq ⟨a,ha⟩)
      change a*(q:G)*a⁻¹=(q:G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    have hz : (q:G) ∈ centralInvolutions T :=
      (source_core512_five_centralizer
        hG T hempty hM hu hmany hcard e H hH hi hQupper A hAH hA).le ⟨q.property,hc⟩
    rw [←hcenter] at hz
    exact (mem_map_iff_mem (f := Q.subtype) Q.subtype_injective).mp hz
  obtain ⟨_,_,hPhi,hUpper,_,hDcard⟩ := Theory.GroupAction.parrott_twoGroup_structure
    (isPGroup_pCoreIn 2 H) hQcard' (by rw [hclass]) hA hfix
  have hDle : ⁅Q,Q⁆ ≤ U := (source_core512_core_structure
    hG T hempty hM hu hmany hcard e H hH hi hQupper).2.1
  have hDmap : (_root_.commutator Q).map Q.subtype = U := by
    apply eq_of_le_of_card_ge
    · simpa only [map_subtype_commutator] using hDle
    · rw [card_map_of_injective Q.subtype_injective,hDcard,hUcard]
  have hD : ⁅Q,Q⁆ = U := by simpa only [map_subtype_commutator] using hDmap
  have hPhiMap : (frattini Q).map Q.subtype = U := by rw [←hPhi,hDmap]
  have hUpperMap : (Subgroup.upperCentralSeries Q 2).map Q.subtype = U := by rw [←hUpper,hDmap]
  refine ⟨hD,hPhiMap,hUpperMap,?_⟩
  have hc := (frattini Q).index_mul_card
  have hpc : Nat.card (frattini Q) = 32 := hPhi ▸ hDcard
  change Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) = Nat.card Q at hc
  rw [hpc,hQcard'] at hc
  change Nat.card (Q ⧸ frattini Q) = 16
  omega

/-- The actual action on the four-dimensional Frattini quotient cannot have
order fifteen, by the invariant third-commutator obstruction. Source:
Parrott, *A characterization of the Tits' simple group* (1972), Lemma 1. -/
theorem source_core512_no_fifteen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512)
    (a : MulAut (H.pCoreIn 2)) :
    orderOf (quotientAut (frattini (H.pCoreIn 2)) a) ≠ 15 := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨_,_,hQcard,hUcard⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hQcard' : Nat.card Q = 512 :=
    (card_map_of_injective H.subtype_injective).trans hQcard
  obtain ⟨hD,hPhi,_,_⟩ := source_core512_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hDPhi : _root_.commutator Q = frattini Q := by
    apply map_injective Q.subtype_injective
    rw [map_subtype_commutator,hD,hPhi]
  have hDcard : Nat.card (_root_.commutator Q) = 32 := by
    rw [←card_map_of_injective (K := _root_.commutator Q) Q.subtype_injective,
      map_subtype_commutator,hD]
    exact hUcard
  have hZcard : Nat.card (center Q) = 2 := by
    rw [←card_map_of_injective (K := center Q) Q.subtype_injective,
      source_core512_core_center hG T hempty hM hu hmany hcard e H hH hi hQupper]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  exact ThirdCommutator.frattini_action_order_ne_fifteen
    (isPGroup_pCoreIn 2 H) hQcard'
    (source_core512_core_class_and_exponent
      hG T hempty hM hu hmany hcard e H hH hi hQupper).1 hZcard hDPhi hDcard a

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
