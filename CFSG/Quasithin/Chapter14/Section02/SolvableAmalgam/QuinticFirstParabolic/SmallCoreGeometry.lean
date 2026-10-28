module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.SmallCore
public import Theory.GroupTheory.CentralBinaryLargeSubgroups
public import Theory.GroupAction.Order512FiveCentralizer
/-!
# Excluding the small original quintic core

If the original Sylow has order below 2048, earlier reductions give
Q=O₂(H) of order 512 and U=⟨Vᴴ⟩ of order 32, with derived subgroup U
and third commutator the central line Z. Parrott's order-five action
calculation supplies the two-coset centralizer property in Q. Binary
commutator duality then forces every class-two subgroup of Q of order
at least 128 containing Z to contain U.

Choose x in the cubic parabolic X which moves Z. The intersection
A=Q∩Qˣ has order at least 128, contains Z and Zˣ, and has class at most
two because its third commutator lies in Z∩Zˣ=1. Applying the preceding
lemma on both sides gives U,Uˣ≤A. These two elementary subgroups commute;
the abelian-subgroup bound in Q forces U=Uˣ. The prime index |X:T|=3
then makes U normal in X as well as H, contrary to the trivial common
core. This proves the Sylow lower bound with all original source
hypotheses and no path-transitivity or presentation premise.

The actual numerical consumer is `QuinticFirstParabolic.LowerBound`.
The remaining path extensions and general D₁₀ exclusion stay with
qt-e-quintic-sylow-lower; first-parabolic recognition stays with
qt-e-quintic-first-parabolic.

Sources: Aschbacher--Smith 14.2.6 and 14.2.20--21, printed pp.982,
988--989; the commutator duality of F.9.7, p.321; Parrott,
*A characterization of the Tits' simple group* (1972), pp.672--674,678.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]
/-- The intrinsic five-action calculation controls every commuting derived coset. -/
theorem source_quintic_small_commuting_cosets
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hsmall : Nat.card (T : Subgroup G) < 2048) :
    let Q := H.pCoreIn 2
    let U := conjugateSpanBy (localModule T M) H
    ∀ b x : Q, (b:G) ∉ U → Commute b x → (x:G) ∈ U ∨ (b:G)*(x:G) ∈ U := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨_,_,hQcard,_⟩ := source_quintic_small_sylow_configuration
    hG T hempty hM hu hmany hcard e H hH hi hsmall
  have hQcard' : Nat.card Q = 512 :=
    (card_map_of_injective H.subtype_injective).trans hQcard
  have hclass := (source_quintic_small_core_class_and_exponent
    hG T hempty hM hu hmany hcard e H hH hi hsmall).1
  have hcenter := source_quintic_small_core_center
    hG T hempty hM hu hmany hcard e H hH hi hsmall
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
      (source_quintic_small_five_centralizer
        hG T hempty hM hu hmany hcard e H hH hi hsmall A hAH hA).le ⟨q.property,hc⟩
    rw [←hcenter] at hz
    exact (mem_map_iff_mem (f := Q.subtype) Q.subtype_injective).mp hz
  have hD : (_root_.commutator Q).map Q.subtype = U := by
    rw [map_subtype_commutator]
    exact (source_quintic_small_core_characteristic_layers
      hG T hempty hM hu hmany hcard e H hH hi hsmall).1
  change ∀ b x : Q, (b:G) ∉ U → Commute b x → (x:G) ∈ U ∨ (b:G)*(x:G) ∈ U
  intro b x hb hc
  have hbD : b ∉ _root_.commutator Q := fun hh => hb (hD ▸ mem_map_of_mem Q.subtype hh)
  rcases Theory.GroupAction.parrott_commuting_derived_cosets
    (isPGroup_pCoreIn 2 H) hQcard' (by rw [hclass]) hA hfix b x hbD hc with hx | hx
  · exact Or.inl (hD ▸ mem_map_of_mem Q.subtype hx)
  · exact Or.inr (hD ▸ mem_map_of_mem Q.subtype hx)

/-- A large class-two subgroup of the small core contains the original closure. -/
theorem source_quintic_small_class_two_contains_closure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hsmall : Nat.card (T : Subgroup G) < 2048)
    (A : Subgroup G) (hAQ : A ≤ H.pCoreIn 2)
    (hZA : centralInvolutions T ≤ A)
    (hclass : ⁅⁅A,A⁆,A⁆ = ⊥) (hAcard : 128 ≤ Nat.card A) :
    conjugateSpanBy (localModule T M) H ≤ A := by
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
        source_quintic_small_centralizer hG T hempty hM hu hmany hcard e H hH hi hsmall
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

  have hD : ⁅Q,Q⁆ = U := (source_quintic_small_core_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hsmall).1
  have hderived : _root_.commutator Q ≤ UQ := by
    intro q hq
    change (q:G) ∈ U
    rw [←hD]
    exact (show (_root_.commutator Q).map Q.subtype = ⁅Q,Q⁆ from map_subtype_commutator Q) ▸
      mem_map_of_mem Q.subtype hq
  have hUcard := (source_quintic_small_sylow_configuration
    hG T hempty hM hu hmany hcard e H hH hi hsmall).2.2.2
  have hcosets (b x : Q) (hb : b ∉ UQ) (hx : ⁅b,x⁆ ∈ ZQ) :
      x ∈ UQ ∨ b*x ∈ UQ :=
    central_commutator_cosets UQ ZQ hZc hZcard hcomm hcentralizer
      (source_quintic_small_commuting_cosets hG T hempty hM hu hmany hcard e H hH hi hsmall)
      b x hb hx
  have hclassQ : ⁅⁅A.subgroupOf Q,A.subgroupOf Q⁆,A.subgroupOf Q⁆ = ⊥ := by
    apply (map_eq_bot_iff_of_injective _ Q.subtype_injective).mp
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hAQ,hclass]
  have hh := large_class_two_contains_selfCentralizer UQ ZQ (A.subgroupOf Q)
    (fun z hz => hZU hz) (fun z hz => hZA hz) hZc hZcard
    ((Nat.card_congr (subgroupOfEquivOfLe hUQ).toEquiv).trans hUcard)
    hcomm hderived hcentralizer hcosets hclassQ
    (by rwa [Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv])
  intro u hu
  exact hh (show (⟨u,hUQ hu⟩ : Q) ∈ UQ from hu)
/-- Cubic conjugates exclude the sole configuration below the required Sylow order. -/
theorem source_quintic_sylow_lower_via_small_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    : 2048 ≤ Nat.card (T : Subgroup G) := by

  by_contra! hsmall
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let V := localModule T M
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hQX := hQT.trans hTX
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hD : ⁅Q,Q⁆ = U := (source_quintic_small_core_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hsmall).1
  have hUQ : U ≤ Q := by
    rw [←hD,←map_subtype_commutator]
    exact map_subtype_le _
  have hZV : Z ≤ V := le_conjugateSpanBy _ _
  have hVU : V ≤ U := le_conjugateSpanBy _ _
  have hZQ := hZV.trans (hVU.trans hUQ)
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hnU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hnV : X ≤ normalizer (V : Set G) := hXM.trans (le_normalizer_conjugateSpanBy _ _)
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hTcard,hQcard,hUcard⟩ := source_quintic_small_sylow_configuration
    hG T hempty hM hu hmany hcard e H hH hi hsmall
  have hQcard' : Nat.card Q = 512 :=
    (card_map_of_injective H.subtype_injective).trans hQcard
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hiX : (T : Subgroup G).relIndex X = 3 :=
    SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
  have hXcard : Nat.card X = 3072 := by
    have hc := ((T : Subgroup G).subgroupOf X).index_mul_card
    change (T : Subgroup G).relIndex X * Nat.card ((T : Subgroup G).subgroupOf X) = _ at hc
    rw [hiX,Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv,hTcard] at hc
    omega
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hcX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hXH)
  have hcore : pCore 2 (X ⊔ H : Subgroup G) = ⊥ := by
    let d : (X ⊔ H : Subgroup G) ≃* (H ⊔ X : Subgroup G) :=
      MulEquiv.subgroupCongr (sup_comm X H)
    apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
    rw [pCore_map_iso]
    exact source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2
  have hnot : ¬ X ≤ normalizer (Z : Set G) := by
    intro hnX
    have hb := AmalgamLocalCores.common_normal_eq_bot X H Z
      (le_inf (hZQ.trans hQX) (hZQ.trans (pCoreIn_le 2 H)))
      hnX (hHZ.trans (_root_.centralizer_le_normalizer _)) hcore hcX
    rw [hb,card_bot] at hZcard
    omega
  obtain ⟨x,hxX,hxZ⟩ : ∃ x ∈ X, x ∉ normalizer (Z : Set G) := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hnot
  let d := MulAut.conj x
  let Qx := Q.map d.toMonoidHom
  let Ux := U.map d.toMonoidHom
  let Zx := Z.map d.toMonoidHom
  let A := Q ⊓ Qx
  have hdis : Z ⊓ Zx = ⊥ := by
    have hd := card_dvd_of_le (show Z ⊓ Zx ≤ Z from inf_le_left)
    rw [hZcard] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · exact card_eq_one.mp hc
    · have hleft : Z ⊓ Zx = Z := eq_of_le_of_card_ge inf_le_left (by rw [hc,hZcard])
      have hright : Z ⊓ Zx = Zx := eq_of_le_of_card_ge inf_le_right (by
        rw [card_map_of_injective d.injective,hc,hZcard])
      exact (hxZ (mem_normalizer_iff_map_conj_eq.mpr (hright.symm.trans hleft))).elim
  have hVd : V.map d.toMonoidHom = V := mem_normalizer_iff_map_conj_eq.mp (hnV hxX)
  have hZA : Z ≤ A := le_inf hZQ (hZV.trans (by
    rw [←hVd]
    exact map_mono (hVU.trans hUQ)))
  have hZxA : Zx ≤ A := le_inf (by
    exact (map_mono hZV).trans (hVd.le.trans (hVU.trans hUQ))) (map_mono hZQ)
  have hQxX : Qx ≤ X := (map_mono hQX).trans
    (mem_normalizer_iff_map_conj_eq.mp (X.le_normalizer hxX)).le
  have hQxcard : Nat.card Qx = 512 :=
    (card_map_of_injective d.injective).trans hQcard'
  have hAcard : 128 ≤ Nat.card A := by
    have hix : Qx.relIndex X = 6 := by
      have hm := (Qx.subgroupOf X).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hQxX).toEquiv] at hm
      change Qx.relIndex X * Nat.card Qx = Nat.card X at hm
      rw [hQxcard,hXcard] at hm
      omega
    have hr : A.relIndex Q ≤ 6 := by
      change (Q ⊓ Qx).relIndex Q ≤ 6
      rw [inf_relIndex_left]
      simpa only [hix] using relIndex_le_of_le_right (H := Qx) hQX (by rw [hix]; decide)
    have hd : A.relIndex Q ∣ 512 := by
      have hd := (A.subgroupOf Q).index_dvd_card
      rwa [hQcard'] at hd
    have hr4 : A.relIndex Q ≤ 4 := by
      by_contra! hn
      have hh : A.relIndex Q = 5 ∨ A.relIndex Q = 6 := by omega
      rcases hh with hh | hh <;> norm_num [hh] at hd
    have hm := (A.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ≤ Q from inf_le_left)).toEquiv] at hm
    change A.relIndex Q * Nat.card A = Nat.card Q at hm
    rw [hQcard'] at hm
    nlinarith
  have hthree : ⁅⁅Q,Q⁆,Q⁆ ≤ Z := (source_quintic_small_core_structure
    hG T hempty hM hu hmany hcard e H hH hi hsmall).2.2.1
  have hclass : ⁅⁅A,A⁆,A⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    rw [←hdis]
    apply le_inf ((commutator_mono (commutator_mono inf_le_left inf_le_left) inf_le_left).trans hthree)
    have hh := map_mono (f := d.toMonoidHom) hthree
    rw [map_commutator,map_commutator] at hh
    exact (commutator_mono (commutator_mono inf_le_right inf_le_right) inf_le_right).trans hh
  have hUA : U ≤ A := source_quintic_small_class_two_contains_closure
    hG T hempty hM hu hmany hcard e H hH hi hsmall A inf_le_left hZA hclass hAcard
  have hUxA : Ux ≤ A := by
    have hbQ : A.map d.symm.toMonoidHom ≤ Q := by
      have hh := map_mono (f := d.symm.toMonoidHom) (show A ≤ Qx from inf_le_right)
      simpa [Qx, map_map] using hh
    have hZb : Z ≤ A.map d.symm.toMonoidHom := by
      have hh := map_mono (f := d.symm.toMonoidHom) hZxA
      simpa [Zx,map_map] using hh
    have hbc : ⁅⁅A.map d.symm.toMonoidHom,A.map d.symm.toMonoidHom⁆,A.map d.symm.toMonoidHom⁆ = ⊥ := by
      rw [←map_commutator,←map_commutator,hclass,Subgroup.map_bot]
    have hb := source_quintic_small_class_two_contains_closure
      hG T hempty hM hu hmany hcard e H hH hi hsmall
      (A.map d.symm.toMonoidHom) hbQ hZb hbc
      (by rwa [card_map_of_injective d.symm.injective])
    have hh := map_mono (f := d.toMonoidHom) hb
    simpa [U,Ux,map_map] using hh
  have hcUQ : ⁅U,Q⁆ ≤ Z := by rwa [hD] at hthree
  have hcUxQx : ⁅Ux,Qx⁆ ≤ Zx := by
    have hh := map_mono (f := d.toMonoidHom) hcUQ
    rwa [map_commutator] at hh
  have hcUUx : ⁅U,Ux⁆ = ⊥ := by
    apply eq_bot_iff.mpr
    rw [←hdis]
    refine le_inf ((commutator_mono le_rfl (hUxA.trans inf_le_left)).trans hcUQ) ?_
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hUA.trans inf_le_right)).trans hcUxQx
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsMulCommutative Ux := (show IsMulCommutative (U.map d.toMonoidHom) from inferInstance)
  have hSup : IsMulCommutative (U ⊔ Ux : Subgroup G) := by
    have hUC := commutator_eq_bot_iff_le_centralizer.mp hcUUx
    apply le_centralizer_iff_isMulCommutative.mp
    apply sup_le
    · exact le_centralizer_iff.mpr (sup_le U.le_centralizer (le_centralizer_iff.mp hUC))
    · exact le_centralizer_iff.mpr (sup_le hUC Ux.le_centralizer)
  let := hSup
  have hSupcard := source_quintic_small_core_abelian_bound
    hG T hempty hM hu hmany hcard e H hH hi hsmall (U ⊔ Ux)
    (sup_le hUQ (hUxA.trans inf_le_left))
  have hSupU : U = U ⊔ Ux := eq_of_le_of_card_ge le_sup_left (by rwa [hUcard])
  have heU : Ux = U := eq_of_le_of_card_ge (hSupU.symm ▸ le_sup_right)
    (by rw [card_map_of_injective d.injective])
  have hxU : x ∈ normalizer (U : Set G) := mem_normalizer_iff_map_conj_eq.mpr heU
  have hTN : (T : Subgroup G) ≤ X ⊓ normalizer (U : Set G) := le_inf hTX (hTH.trans hnU)
  have hnX : X ≤ normalizer (U : Set G) := by
    have hm := relIndex_mul_relIndex (T : Subgroup G)
      (X ⊓ normalizer (U : Set G)) X hTN inf_le_left
    rw [hiX] at hm
    rcases Nat.prime_mul_iff.mp (hm ▸ (by decide : Nat.Prime 3)) with hp | hp
    · exact (relIndex_eq_one.mp hp.2).trans inf_le_right
    · have hxT := relIndex_eq_one.mp hp.2 (show x ∈ X ⊓ normalizer (U : Set G) from ⟨hxX,hxU⟩)
      exact (hxZ (_root_.centralizer_le_normalizer _ (hHZ (hTH hxT)))).elim
  have hb := AmalgamLocalCores.common_normal_eq_bot X H U
    (le_inf (hUQ.trans hQX) (hUQ.trans (pCoreIn_le 2 H))) hnX hnU hcore hcX
  change Nat.card U = 32 at hUcard
  rw [hb,card_bot] at hUcard
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
