module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCoreKernel
public import Theory.SpecificGroups.PSL3Two.WreathCubicRadical

/-!
# The elementary action section and the strict Frattini interval

Write J=L₀T, K=<O²(H)^E>, Q=O₂(K), and N=Q∩O₂(J). The original
wreath lift sends Q into the factor-preserving base, normalized by the
original cubic complement. The concrete cubic-plane calculation proves
that its image is elementary abelian. The lift and the module conjugation
action have identical kernels, so the literal section Q/N is elementary
abelian of order sixteen in the collapsed branch.

Consequently Φ(Q) lies in N. This containment is strict: Φ(Q) is
characteristic in Q and hence K-invariant, whereas the common kernel has
already been proved not K-invariant. Also N<Q. The final consumer carries
the literal quotient, its relative normality, the action cardinality and
both strict containments on the same original source witnesses.

These are structural constraints, not the exclusion of the collapsed
configuration. Its ambient exclusion and assembly of StabilizerNormalizerAt
and HalfSylowUniqueAt remain with qt-d-10-nona5-half-sylow-unique.
ModuleChoiceAt is the sole external premise, finally discharged by
qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.4--6, printed pp.747--749.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P : Subgroup G}
  {s : NaturalData D} {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

private theorem Data.core_lift_elementary (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    IsElementaryAbelian 2
      ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map f.hom) := by
  let J := localJoin T L
  let Q := (enlargedResidual T L H).pCoreIn 2
  let A := P.subgroupOf J
  let U := (Q.subgroupOf J).map f.hom
  have hPJ : P ≤ J := hi.complement_le.trans ((map_subtype_le _).trans h.le_join)
  have ha : IsPGroup 3 A := hi.odd_complement.isPGroup.of_equiv
    (subgroupOfEquivOfLe hPJ).symm
  have hd := ha.disjoint_of_coprime f.kernel_two (by decide : Nat.Coprime 3 2)
  have hinj : Function.Injective (f.hom.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    change f.hom.subgroupMap A x = 1 at hx
    exact Subtype.ext (hd.le_bot ⟨x.property,congrArg Subtype.val hx⟩)
  have hcard : Nat.card (A.map f.hom) = 9 := by
    rw [←Nat.card_congr (MulEquiv.ofBijective (f.hom.subgroupMap A)
      ⟨hinj,f.hom.subgroupMap_surjective A⟩).toEquiv]
    exact (Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv).trans hP
  have hPQ : P ≤ normalizer (Q : Set G) :=
    (hi.complement_le.trans h.residual_le_enlargedResidual).trans
      ((enlargedResidual T L H).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hQJ : Q ≤ J := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  have hn : A ≤ normalizer (Q.subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq hQJ]
    exact subgroupOf_mono J hPQ
  apply Matrix.PSL3Two.WreathPair.two_base_normalized_cubic_plane_elementary
    (A.map f.hom) U hcard ((isPGroup_pCoreIn 2 _).comap_subtype.map f.hom)
  · rintro _ ⟨q,hq,rfl⟩
    exact f.right_eq_one_of_normalizes q (h.enlargedResidual_core_le_intersection hq).1.2
  · exact (map_mono hn).trans (le_normalizer_map f.hom)

/-- The containing core acts through an elementary abelian two-group on the original module. -/
theorem Data.core_action_elementary (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    IsElementaryAbelian 2
      ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D)) := by
  let A := ((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)
  let : IsElementaryAbelian 2 (A.map f.hom) := h.core_lift_elementary f hi hP
  let U := A.map (joinAction D)
  have hsquare (u : U) : u ^ 2 = 1 := by
    obtain ⟨x,hx,he⟩ := u.property
    have hx2 : x ^ 2 ∈ f.hom.ker := by
      change f.hom (x ^ 2) = 1
      rw [map_pow]
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ (mem_map_of_mem f.hom hx)
    rw [f.kernel_eq_action_kernel] at hx2
    apply Subtype.ext
    change (u : MulAut D.fullModule) ^ 2 = 1
    rw [←he,←map_pow]
    exact hx2
  exact {
    toIsMulCommutative := ⟨⟨fun u v => Commute.of_orderOf_dvd_two
      (fun w => orderOf_dvd_of_pow_eq_one (hsquare w)) u v⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }

/-- The literal quotient by the common core kernel is elementary abelian
of order sixteen; its relative normality is constructed here. -/
theorem Data.collapsed_core_quotient_elementary (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    let Q := (enlargedResidual T L H).pCoreIn 2
    let N := (Q ⊓ (localJoin T L).pCoreIn 2).subgroupOf Q
    ∃ _ : N.Normal, IsElementaryAbelian 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N) = 16 := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let J := localJoin T L
  let N := (Q ⊓ J.pCoreIn 2).subgroupOf Q
  have hQJ : Q ≤ J := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  let a := (joinAction D).comp (inclusion hQJ)
  have hrange : a.range = (Q.subgroupOf J).map (joinAction D) := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨inclusion hQJ q,q.property,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩,rfl⟩
  have hk : a.ker = N := by
    have hk' : (centralizer (D.fullModule : Set G)).subgroupOf J =
        (J.pCoreIn 2).subgroupOf J := by
      rw [←joinAction_ker,←f.kernel_eq_action_kernel,f.kernel_eq_join_core]
      exact (comap_map_eq_self_of_injective J.subtype_injective _).symm
    ext q
    change joinAction D (inclusion hQJ q) = 1 ↔ _
    change inclusion hQJ q ∈ (joinAction D).ker ↔ _
    rw [joinAction_ker,hk']
    change (q : G) ∈ J.pCoreIn 2 ↔ (q : G) ∈ Q ⊓ J.pCoreIn 2
    exact (and_iff_right q.property).symm
  let hN : N.Normal := hk ▸ (inferInstance : a.ker.Normal)
  let : N.Normal := hN
  let e : (Q ⧸ N) ≃* a.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange a)
  let : IsElementaryAbelian 2 a.range := hrange.symm ▸ h.core_action_elementary f hi hP
  refine ⟨hN,IsElementaryAbelian.of_injective e.toMonoidHom e.injective,?_⟩
  rw [Nat.card_congr e.toEquiv,hrange]
  exact h.collapsed_core_action_card f hi hP hc

/-- The Frattini subgroup of the containing core lies in the literal common core kernel. -/
theorem Data.core_frattini_le_common_kernel (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9) :
    (frattini ((enlargedResidual T L H).pCoreIn 2)).map
      ((enlargedResidual T L H).pCoreIn 2).subtype ≤
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 := by
  let Q := (enlargedResidual T L H).pCoreIn 2
  let J := localJoin T L
  have hQJ : Q ≤ J := h.enlargedResidual_core_le_intersection.trans
    (inf_le_left.trans (inf_le_left.trans le_sup_right))
  let a : Q →* SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Actor :=
    f.hom.comp (inclusion hQJ)
  have hrange : a.range = (Q.subgroupOf J).map f.hom := by
    ext x
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨inclusion hQJ q,q.property,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩,rfl⟩
  let : IsElementaryAbelian 2 a.range := hrange.symm ▸ h.core_lift_elementary f hi hP
  let : Fact (IsPGroup 2 a.range) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  have hzero : frattini a.range = ⊥ := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mpr inferInstance
  have hphi := frattini_le_comap_frattini_of_surjective a.rangeRestrict_surjective
  rw [hzero] at hphi
  rintro _ ⟨q,hq,rfl⟩
  refine ⟨q.property,?_⟩
  have he : a q = 1 := congrArg Subtype.val (hphi hq)
  have hk : inclusion hQJ q ∈ f.hom.ker := he
  rw [f.kernel_eq_join_core] at hk
  exact mem_map_of_mem J.subtype hk

/-- In the remaining prime-field branch, the common kernel is strictly above
Frattini and strictly below the containing core. -/
theorem Data.collapsed_frattini_interval (h : Data D H) (f : LiftData s hz)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hmodel : Selection.BinaryThreeNatural D)
    {I : Subgroup G}
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p) (hlarge : 11 ≤ p)
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    (frattini ((enlargedResidual T L H).pCoreIn 2)).map
      ((enlargedResidual T L H).pCoreIn 2).subtype <
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ∧
    (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 <
      (enlargedResidual T L H).pCoreIn 2 := by
  let K := enlargedResidual T L H
  let Q := K.pCoreIn 2
  have hKQ : K ≤ normalizer (Q : Set G) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hnot := h.collapsed_core_kernel_not_normalized f hn hmodel hs hK hp ho hm hlarge hP hc
  change ¬ K ≤ normalizer ((Q ⊓ (localJoin T L).pCoreIn 2 : Subgroup G) : Set G) at hnot
  constructor
  · apply lt_of_le_of_ne (h.core_frattini_le_common_kernel f hs.toLocalInput hP)
    intro he
    apply hnot
    rw [←he]
    exact hKQ.trans (normalizer_le_normalizer_characteristic_image Q (frattini Q))
  · apply lt_of_le_of_ne inf_le_left
    intro he
    apply hnot
    rw [he]
    exact hKQ

/-- The collapsed common-core section is the original elementary sixteen action. -/
theorem Data.collapsed_core_elementary_section (h : Data D H) (f : LiftData s hz)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hP : Nat.card P = 9)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    IsElementaryAbelian 2
      ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D)) ∧
    Nat.card ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map
      (joinAction D)) = 16 ∧
    (frattini ((enlargedResidual T L H).pCoreIn 2)).map
      ((enlargedResidual T L H).pCoreIn 2).subtype ≤
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 :=
  ⟨h.core_action_elementary f hi hP,h.collapsed_core_action_card f hi hP hc,
    h.core_frattini_le_common_kernel f hi hP⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual remaining source configuration has an elementary sixteen action
and a strict Frattini interval, on the same containing-core witnesses. -/
theorem SourceCubicNormalizerEnlargement.exists_core_elementary_section
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCubicNormalizerEnlargement D) :
    ∃ H P : Subgroup G, Data D H ∧
      LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H) ∧
      IsElementaryAbelian 2
        ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D)) ∧
      Nat.card ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map
        (joinAction D)) = 16 ∧
      (frattini ((enlargedResidual T L H).pCoreIn 2)).map
        ((enlargedResidual T L H).pCoreIn 2).subtype <
        (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ∧
      (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 <
        (enlargedResidual T L H).pCoreIn 2 ∧
      (let Q := (enlargedResidual T L H).pCoreIn 2
       let N := (Q ⊓ (localJoin T L).pCoreIn 2).subgroupOf Q
       ∃ _ : N.Normal, IsElementaryAbelian 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N) = 16) := by
  obtain ⟨_,_,hfull,hn,_,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,_,h24,_,_,_,hcollapse⟩ := hc
  obtain ⟨t,ht,htn,_,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hcross := Selection.ModuleChoice.crossed_of_local_thompson D (hfull ▸ hJ) ht htn
  obtain ⟨s,_⟩ := exists_naturalData D hmodel hzero hfull ht htn hcross
  let f := originalLift s s.fixed_zero
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  have hP := (hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))).2
  have hlarge : 11 ≤ p := by have := Nat.mod_le p 24; omega
  obtain ⟨hel,hcard,_⟩ := h.collapsed_core_elementary_section f hs.toLocalInput hP hcollapse
  have hinterval := h.collapsed_frattini_interval f hn hmodel hs hK hp ho hm hlarge hP hcollapse
  exact ⟨H,P,h,hs.toLocalInput,hel,hcard,hinterval.1,hinterval.2,
    h.collapsed_core_quotient_elementary f hs.toLocalInput hP hcollapse⟩

/-- Both original contracts retain the same obstruction with its exact elementary
core action and strict Frattini interval. No further source premise is introduced. -/
theorem sourceContracts_or_cubicCoreElementarySection (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D ∧
        ∃ H : Subgroup G, Data D H ∧
          IsElementaryAbelian 2
            ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map (joinAction D)) ∧
          Nat.card ((((enlargedResidual T L H).pCoreIn 2).subgroupOf (localJoin T L)).map
            (joinAction D)) = 16 ∧
          (frattini ((enlargedResidual T L H).pCoreIn 2)).map
            ((enlargedResidual T L H).pCoreIn 2).subtype <
            (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 ∧
          (enlargedResidual T L H).pCoreIn 2 ⊓ (localJoin T L).pCoreIn 2 <
            (enlargedResidual T L H).pCoreIn 2 ∧
          (let Q := (enlargedResidual T L H).pCoreIn 2
           let N := (Q ⊓ (localJoin T L).pCoreIn 2).subgroupOf Q
           ∃ _ : N.Normal, IsElementaryAbelian 2 (Q ⧸ N) ∧ Nat.card (Q ⧸ N) = 16) := by
  rcases sourceContracts_or_cubicNormalizerEnlargement hchoice with hh | ⟨L,D,hc⟩
  · exact Or.inl hh
  · obtain ⟨H,_,h,_,he⟩ := hc.exists_core_elementary_section
    exact Or.inr ⟨L,D,hc,H,h,he⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
