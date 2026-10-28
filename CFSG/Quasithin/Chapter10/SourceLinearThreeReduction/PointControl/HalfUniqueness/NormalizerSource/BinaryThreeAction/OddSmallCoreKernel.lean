module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreAction
public import Theory.GroupTheory.SmallTwoSectionActions
public import Theory.GroupTheory.ConjugateSpanSimpleImage
public import Theory.GroupTheory.ConjugateSpanSylow
public import GorensteinWalter.PSL2Cardinality

/-!
# The common core kernel normally generates the containing core

Write J=L₀T, X=O²(H), K=<Xᴱ>, Q=O₂(K), and R=O₂(J).
In the collapsed odd-prime case the original action kernel N=Q∩R
has index sixteen in Q. The perfect components of K have simple
PSL₂(p) quotients with p at least eleven. Their orders force every
action of K on a group of order dividing sixteen to be trivial.

Consequently every K-invariant subgroup containing N contains [Q,P],
which is the original O₂(X). The original parabolic-core decomposition
gives Q=O₂(X)N, so the K-normal closure of N is exactly Q. Moreover N
itself is not K-invariant: otherwise O₂(X) would centralize the original
natural module, contradicting its proved noncentral action.

The final applications retain the original source guards, cubic complement,
containing components and literal intersections for both source contracts.
These statements do not exclude the collapsed configuration. Its ambient
exclusion and assembly of StabilizerNormalizerAt and HalfSylowUniqueAt
remain with qt-d-10-nona5-half-sylow-unique. ModuleChoiceAt is the only
external premise, with its final discharge retained by
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

private theorem model_prime_dvd {A : Type*} [Group A] {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hm : ClassicalGroup.IsPSL A 2 p) : p ∣ Nat.card A := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
    ⟨p,1,hp,ho,by decide,by simpa using hF⟩,hF]
  have heven : 2 ∣ p * (p ^ 2 - 1) := by
    apply dvd_mul_of_dvd_right
    apply Nat.dvd_of_mod_eq_zero
    have hm : p % 2 = 1 := by obtain ⟨k,hk⟩ := ho; omega
    have hh := Nat.pow_mod p 2 2
    rw [hm] at hh
    norm_num at hh
    have := hp.two_le
    have hpow : 1 ≤ p ^ 2 := one_le_pow₀ (by omega : 1 ≤ p)
    omega
  apply ho.coprime_two_right.dvd_of_dvd_mul_left
  rw [Nat.mul_div_cancel' heven]
  exact dvd_mul_right p _

private theorem Data.hom_to_small_two_aut_eq_one (_h : Data D H)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    {A : Type*} [Group A] [Finite A] (hA : Nat.card A ∣ 16)
    (f : enlargedResidual T L H →* MulAut A) : f = 1 := by
  let := hs.component.2.perfect
  let eI := subgroupOfEquivOfLe hs.component.1
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective (f := eI.toMonoidHom) eI.surjective
  let : IsSimpleGroup (XiQuotient I) := SwappedFactorsProof.quotient_simple hs.toSwappedInput
    (.linear_prime p hp ho hm)
  let q := QuotientGroup.mk' (pCore 2 I)
  have hsol : Group.IsSolvable q.ker := by
    dsimp only [q]
    rw [QuotientGroup.ker_mk']
    let := pCore_isNilpotent (p := 2) (G := I)
    infer_instance
  let := hsol
  have hI : ∀ f : I →* MulAut A, f = 1 :=
    hom_eq_one_of_simple_quotient_card_dvd q (QuotientGroup.mk'_surjective _)
      (model_prime_dvd hp ho hm) (prime_not_dvd_aut_of_card_dvd_sixteen hp hlarge hA)
  have hgen : enlargedResidual T L H = conjugateSpanBy I (T : Subgroup G) :=
    hK.trans (conjugateSpanBy_eq_iSup_conj I (T : Subgroup G)).symm
  let e := MulEquiv.subgroupCongr hgen
  have hf := conjugateSpanBy_hom_eq_one I (T : Subgroup G) hI (f.comp e.symm.toMonoidHom)
  apply MonoidHom.ext
  intro x
  have he := DFunLike.congr_fun hf (e x)
  simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply,
    MonoidHom.one_apply] using he

/-- The original common core kernel cannot be normal in the containing orbit. -/
theorem Data.collapsed_core_kernel_not_normalized (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    ¬ enlargedResidual T L H ≤ normalizer
      ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 : Set G) := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  let N := Q ⊓ (localJoin T L).pCoreIn 2
  intro hKN
  have hKQ : K ≤ normalizer (Q : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  let : (N.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 K).trans hKN)
  have hcard : Nat.card (Q ⧸ N.subgroupOf Q) = 16 := by
    change N.relIndex Q = 16
    have hh := h.collapsed_core_centralizer_relIndex f hs.toLocalInput hP hc
    rwa [h.core_action_kernel_eq_intersection f] at hh
  have hcomm : ⁅Q,K⁆ ≤ N := commutator_le_of_section_hom_trivial K Q N hKQ hKN
    (fun a => h.hom_to_small_two_aut_eq_one hs hK hp ho hm hlarge (hcard ▸ dvd_rfl) a)
  have hC : (residual H).pCoreIn 2 ≤ (localJoin T L).pCoreIn 2 := by
    rw [←h.collapsed_core_commutator hs.toLocalInput hc]
    exact ((commutator_mono le_rfl
      (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)).trans hcomm).trans inf_le_right
  apply h.residual_core_moves_fullModule hn hmodel
  intro x hx
  have hxQ := hC hx
  have hk : ((localJoin T L).pCoreIn 2).subgroupOf (localJoin T L) = (joinAction D).ker := by
    rw [←f.kernel_eq_action_kernel,f.kernel_eq_join_core]
    exact comap_map_eq_self_of_injective (localJoin T L).subtype_injective _
  have hx' : (⟨x,pCoreIn_le 2 _ hxQ⟩ : localJoin T L) ∈ (joinAction D).ker :=
    hk ▸ hxQ
  rwa [joinAction_ker] at hx'

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

private theorem Data.collapsed_core_eq_residual_core_sup_kernel (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (enlargedResidual T L H).pCoreIn 2 = (residual H).pCoreIn 2 ⊔
      ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2) := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let C := (residual H).pCoreIn 2
  let R := (localJoin T L).pCoreIn 2
  have hRQ : R ≤ H := (join_core_le_stabilizer D).trans (inf_le_left.trans h.sylow_le)
  have hRC : R ≤ normalizer (C : Set G) :=
    (hRQ.trans (le_normalizer_embedded_pResidual 2 H)).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hQH : Q ≤ H.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes h.enlargedResidual_le_enlargement
      (le_normalizer_conjugateSpanBy _ _)).trans h.enlargement_core_le_parabolic_core
  apply le_antisymm
  · intro q hq
    have hq' : q ∈ (C : Set G) * (R : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left C R hRC]
      exact h.parabolic_core_eq_residual_core_join_core f hi hP ▸ hQH hq
    obtain ⟨c,hc',r,hr,he⟩ := hq'
    have hrQ : r ∈ Q := by
      have hh := Q.mul_mem (Q.inv_mem (hc hc')) hq
      rwa [←he,inv_mul_cancel_left] at hh
    rw [←he]
    exact mul_mem_sup hc' ⟨hrQ,hr⟩
  · exact sup_le hc inf_le_left

/-- Every K-normal subgroup containing the original common kernel already
contains the entire containing two-core. -/
theorem Data.collapsed_core_le_of_kernel_normalized (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2)
    (N : Subgroup G)
    (hN : (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ≤ N)
    (hKN : enlargedResidual T L H ≤ normalizer (N : Set G)) :
    (enlargedResidual T L H).pCoreIn 2 ≤ N := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  have hKQ : K ≤ normalizer (Q : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  let : (N.subgroupOf Q).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 K).trans hKN)
  have hcard : Nat.card (Q ⧸ N.subgroupOf Q) ∣ 16 := by
    change N.relIndex Q ∣ 16
    have hh := h.collapsed_core_centralizer_relIndex f hs.toLocalInput hP hc
    rw [h.core_action_kernel_eq_intersection f] at hh
    exact hh ▸ relIndex_dvd_of_le_left Q hN
  have hcomm : ⁅Q,K⁆ ≤ N := commutator_le_of_section_hom_trivial K Q N hKQ hKN
    (fun a => h.hom_to_small_two_aut_eq_one hs hK hp ho hm hlarge hcard a)
  have hCN : (residual H).pCoreIn 2 ≤ N := by
    rw [←h.collapsed_core_commutator hs.toLocalInput hc]
    exact (commutator_mono le_rfl
      (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)).trans hcomm
  rw [h.collapsed_core_eq_residual_core_sup_kernel f hs.toLocalInput hP hc]
  exact sup_le hCN hN

/-- Conjugating the original common kernel by the containing component orbit
generates precisely its two-core. -/
theorem Data.collapsed_kernel_normalClosure (h : Data D H)
    {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}
    (f : LiftData s hz)
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    conjugateSpanBy
      ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2)
      (enlargedResidual T L H) = (enlargedResidual T L H).pCoreIn 2 := by
  apply le_antisymm
  · exact conjugateSpanBy_le inf_le_left
      ((enlargedResidual T L H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  · exact h.collapsed_core_le_of_kernel_normalized f hs hK hp ho hm hlarge hP hc _
      (le_conjugateSpanBy _ _) (le_normalizer_conjugateSpanBy _ _)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The remaining source configuration has a proper action kernel whose
normal closure under the same containing orbit is the entire containing core. -/
theorem SourceCubicNormalizerEnlargement.exists_core_kernel_closure
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
      SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
        (residual H) P (enlargement T L H) I ∧
      enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
      p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
      (p % 24 = 11 ∨ p % 24 = 13) ∧
      (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2 ∧
      (¬ enlargedResidual T L H ≤ normalizer
        ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 : Set G)) ∧
      conjugateSpanBy
        ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2)
        (enlargedResidual T L H) = (enlargedResidual T L H).pCoreIn 2 := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  exact ⟨H,P,I,p,h,hs,hK,hp,ho,hm,h24,hcollapse,
    h.collapsed_core_kernel_not_normalized f hn hmodel hs hK hp ho hm hlarge hP hcollapse,
    h.collapsed_kernel_normalClosure f hs hK hp ho hm hlarge hP hcollapse⟩

/-- Both original contracts reduce to the same source configuration with
its nonnormal common kernel and exact containing-core normal closure. -/
theorem sourceContracts_or_cubicCoreKernelClosure (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          (¬ enlargedResidual T L H ≤ normalizer
            ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 : Set G)) ∧
          conjugateSpanBy
            ((enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2)
            (enlargedResidual T L H) = (enlargedResidual T L H).pCoreIn 2 := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,_,_,h,_,_,_,_,_,_,_,hN,hclosure⟩ := hc.exists_core_kernel_closure
    exact Or.inr ⟨L,D,hc,H,h,hN,hclosure⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
