module
public import CFSG.Quasithin.ChapterA.Section04.ReducedWitness.Intrinsic
public import Theory.GroupTheory.CentralPChiefFactors.Coprime
public import Theory.GroupTheory.ReducedNormal.Basic
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.Residual
/-!
# The selected odd residual survives on the original reduced module

The odd quotient P/O₂(P) has no two-chief factor, so A.4.11 detects its
nontrivial intrinsic signalizer module on R₂(PT). Normality kills O₂(P)
in the literal centralizer quotient. This constructs a nontrivial odd
image and an actual surjection from the original intrinsic quotient,
with the original projection formula preserved.

The last application uses P=O²(the preimage of D in H/O₂(H)), embedded
in the original ambient group. It needs only the already selected odd
normal subgroup and faithful-signalizer conclusion. The subsequent
quaternion argument will prove this surjection injective when D=E₉.
Source: Aschbacher--Smith, 13.3.14(d), printed p.892; A.4.11, pp.60--61.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

theorem reduced_moves_of_odd_core_quotient
    (P : Subgroup G) (hsub : P.IsSubnormal) (hP : IsPPerfect 2 P)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hodd : IsPGroup p (P ⧸ pCore 2 P))
    (hne : intrinsicSignalizerModule P ≠ ⊥) :
    ⁅reducedTwoSubgroup G,P⁆ ≠ ⊥ := by
  apply ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot P hsub hP _ hne
  apply (hasCentralPChiefFactorsAbove_iff_quotient (pCore 2 P)).mpr
  exact HasCentralPChiefFactors.of_isPGroup_of_ne (by obtain ⟨n,hn⟩ := hp; omega) hodd

theorem reduced_quotient_odd_image
    (P : Subgroup G) [P.Normal] (hP : IsPPerfect 2 P)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hodd : IsPGroup p (P ⧸ pCore 2 P))
    (hne : intrinsicSignalizerModule P ≠ ⊥) :
    let W := reducedTwoSubgroup G
    let C := centralizer (W : Set G)
    let q := QuotientGroup.mk' C
    P.map q ≠ ⊥ ∧ IsPGroup p (P.map q) ∧ pCore 2 (G ⧸ C) = ⊥ ∧
      ∃ f : (P ⧸ pCore 2 P) →* P.map q, Function.Surjective f ∧
        ∀ x : P, (f (QuotientGroup.mk' (pCore 2 P) x) : G ⧸ C) = q (x : G) := by
  let W := reducedTwoSubgroup G
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  have hm := reduced_moves_of_odd_core_quotient P (inferInstance : P.Normal).isSubnormal
    hP hp hodd hne
  have hnot : P.map q ≠ ⊥ := by
    intro h
    have hPC : P ≤ C := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff P).mp h
    exact hm (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hPC))
  let f : P →* P.map q := q.subgroupMap P
  have hf : Function.Surjective f := q.subgroupMap_surjective P
  have hk : pCore 2 P ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change q (x : G) = 1
    apply (QuotientGroup.eq_one_iff _).mpr
    exact normal_pCore_le_centralizer_reducedPSubgroup 2 P
      (mem_map.mpr ⟨x,hx,rfl⟩)
  let fbar := QuotientGroup.lift (pCore 2 P) f hk
  have hfbar : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective _ _ hf _
  exact ⟨hnot,hodd.of_surjective fbar hfbar,
    (isPReduced_reducedPSubgroup (p := 2) (G := G)).quotient_pCore_eq_bot,
    fbar,hfbar,fun _ => rfl⟩

theorem reduced_join_odd_image
    (P T : Subgroup G) (hTP : T ≤ normalizer (P : Set G)) (hP : IsPPerfect 2 P)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hodd : IsPGroup p (P ⧸ pCore 2 P))
    (hne : intrinsicSignalizerModule P ≠ ⊥) :
    let J := P ⊔ T
    let P' := P.subgroupOf J
    let W := reducedTwoSubgroup J
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    P'.map q ≠ ⊥ ∧ IsPGroup p (P'.map q) ∧ pCore 2 (J ⧸ C) = ⊥ ∧
      ∃ f : (P' ⧸ pCore 2 P') →* P'.map q, Function.Surjective f ∧
        ∀ x : P', (f (QuotientGroup.mk' (pCore 2 P') x) : J ⧸ C) = q (x : J) := by
  let J := P ⊔ T
  let P' := P.subgroupOf J
  let : P'.Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hTP)
  let e : P' ≃* P := subgroupOfEquivOfLe (show P ≤ J from le_sup_left)
  have hP' : IsPPerfect 2 P' := hP.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hodd' : IsPGroup p (P' ⧸ pCore 2 P') := hodd.of_equiv
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hne' : intrinsicSignalizerModule P' ≠ ⊥ := by
    intro hz
    have he := intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective P'
    rw [show P'.map J.subtype = P from map_subgroupOf_eq_of_le le_sup_left,hz,Subgroup.map_bot] at he
    exact hne he
  exact reduced_quotient_odd_image P' hP' hp hodd' hne'

theorem star_reduced_join_odd_image
    (H T : Subgroup G) (hTH : T ≤ H) (D : Subgroup (Star H)) [D.Normal]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hD : IsPGroup p D)
    (hfaith : IsFaithfulSignalizerType ((starResidual H D).map H.subtype)) :
    let P := (starResidual H D).map H.subtype
    let J := P ⊔ T
    let P' := P.subgroupOf J
    let W := reducedTwoSubgroup J
    let C := centralizer (W : Set J)
    let q := QuotientGroup.mk' C
    P'.map q ≠ ⊥ ∧ IsPGroup p (P'.map q) ∧ pCore 2 (J ⧸ C) = ⊥ ∧
      ∃ f : (P' ⧸ pCore 2 P') →* P'.map q, Function.Surjective f ∧
        ∀ x : P', (f (QuotientGroup.mk' (pCore 2 P') x) : J ⧸ C) = q (x : J) := by
  let R := starResidual H D
  let P := R.map H.subtype
  have hR : R.Normal := starResidual_normal H D
  let := hR
  have hP : (P.subgroupOf H).Normal := by
    change ((R.map H.subtype).comap H.subtype).Normal
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hn : H ≤ normalizer (P : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show P ≤ H from map_subtype_le _)).mp hP
  let e : R ≃* P := R.equivMapOfInjective H.subtype H.subtype_injective
  have ho : IsPGroup p (P ⧸ pCore 2 P) :=
    (hD.of_equiv (oddStarResidualCoreEquiv H D hp hD).symm).of_equiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
  exact reduced_join_odd_image P T (hTH.trans hn) hfaith.1.2.1 hp ho hfaith.2
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
