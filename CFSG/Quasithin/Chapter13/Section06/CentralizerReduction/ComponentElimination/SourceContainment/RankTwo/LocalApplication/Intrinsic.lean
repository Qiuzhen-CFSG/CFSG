module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Maps
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Structure
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.Quasithin.Rank

/-!
# Intrinsic quasisimplicity in the three-rank-two branch

Apply the full universal A.3.6 contract to the actual C-component of KTᵥ
after removing its two-core. In the natural and nilpotent alternatives the
Fitting subgroup has order prime to three. The quotient is SL₂ over a
prime field, whose odd Sylow subgroups are cyclic. Injecting a Sylow
three-subgroup through this quotient forces three-rank at most one.
Thus rank two leaves exactly the simple and central-three-cover cases.
Their centers have three-rank at most one.

The argument uses Yz's C-component in KTᵥ and genuine group isomorphisms
for both changes of carrier. It does not assume a C-component in KLᵥ.
The ambient SQTK and two-core quotient hypotheses of A.3.6 are derived
from the simple-QTKE hypothesis and the involution v. The universal A.3.6
classification remains an explicit earlier-source input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.6,
pp.43–45; 1.2.1(4), p.504; 13.6.20, p.931. No use is made of the
stronger center–Frattini assertion in 1.2.1(4d).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open scoped MatrixGroups

private theorem rank_le_of_coprime_kernel {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] (f : A →* B) (hc : Nat.Coprime 3 (Nat.card f.ker)) :
    primeRank 3 A ≤ primeRank 3 B := by
  let P : Sylow 3 A := Classical.choice inferInstance
  rw [P.primeRank_eq]
  exact Theory.GroupTheory.primeRank_le_of_injective 3 (f.comp (P : Subgroup A).subtype)
    (injective_comp_subtype_of_coprime_ker f hc (P : Subgroup A) P.isPGroup')

private theorem rank_sl_two_prime {B : Type*} [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime) (h : IsSL B 2 p) : primeRank 3 B ≤ 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let c : F ≃+* ZMod p :=
    (ZMod.ringEquivOfPrime F hp (by simpa only [← Nat.card_eq_fintype_card] using hF)).symm
  let m := Matrix.SpecialLinearGroup.map (n := Fin 2) c.toRingHom
  have hm : Function.Injective m := by
    intro x y he
    apply Subtype.ext
    ext i j
    apply c.injective
    exact congrArg (fun a : SL(2, ZMod p) => a.val i j) he
  let P : Sylow 3 B := Classical.choice inferInstance
  apply P.primeRank_le_one_of_isCyclic
  exact Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
    P.isPGroup' (by decide) (m.comp (e.toMonoidHom.comp (P : Subgroup B).subtype))
    (hm.comp (e.injective.comp (P : Subgroup B).subtype_injective))

private theorem rank_natural {B : Type*} [Group B] [Finite B]
    (h : A36Natural B) : primeRank 3 B ≤ 1 := by
  obtain ⟨p, hp, hlarge, F, _, _, hc, e, f, _⟩ := h.2
  have hn : Nat.Coprime 3 (Nat.card (generalizedFitting B)) := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.Coprime 3 (Nat.card (Fin 2 → F))
    rw [Nat.card_fun, Nat.card_fin, hc]
    exact (Nat.prime_three.coprime_iff_not_dvd.mpr
      (fun hd => (hp.eq_one_or_self_of_dvd 3 hd).elim (by decide) (by omega))).pow_right 2
  have hb := rank_le_of_coprime_kernel (QuotientGroup.mk' (generalizedFitting B))
    (by rwa [QuotientGroup.ker_mk'])
  exact hb.trans (rank_sl_two_prime hp ⟨F, inferInstance, inferInstance, hc, ⟨f⟩⟩)

private theorem rank_nilpotent {B : Type*} [Group B] [Finite B]
    (h : A36Nilpotent B) : primeRank 3 B ≤ 1 := by
  have hn : Nat.Coprime 3 (Nat.card (generalizedFitting B)) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have hh := (h.2.2.2 3 (by decide) hd).1
    norm_num at hh
  exact (rank_le_of_coprime_kernel (QuotientGroup.mk' (generalizedFitting B))
    (by rwa [QuotientGroup.ker_mk'])).trans (rank_sl_two_prime (by decide) h.2.2.1)

private theorem classified_intrinsic {X : Type*} [Group X] [Finite X]
    (B : Subgroup X) (h : A36Alternative B) (hr : 2 ≤ primeRank 3 B) :
    IsQuasisimple B ∧ primeRank 3 (center B) ≤ 1 := by
  cases h with
  | simple hc hs _ =>
    refine ⟨hc.2, ?_⟩
    let := hs
    let := hc.2
    have hz : center B = ⊥ := by
      rcases (inferInstance : (center B).Normal).eq_bot_or_eq_top with hz | hz
      · exact hz
      · exact (Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp hz)).elim
    have hz0 : primeRank 3 (center B) = 0 := by
      apply PrimeRank.eq_zero_iff_not_dvd_card.mpr
      simp [hz]
    omega
  | cover hc he _ =>
    refine ⟨hc.2, ?_⟩
    obtain ⟨e⟩ := he
    let : IsCyclic (center B) := isCyclic_of_injective e.toMonoidHom e.injective
    let P : Sylow 3 (center B) := Classical.choice inferInstance
    exact P.primeRank_le_one_of_isCyclic inferInstance
  | natural h => have := rank_natural h; omega
  | nilpotent h => have := rank_nilpotent h; omega

universe u
/-- Rank two excludes both nonquasisimple alternatives of A.3.6, so the intrinsic
two-core quotient is quasisimple and its center has three-rank at most one. -/
theorem cComponent_twoCore_quasisimple_of_three_rank {X : Type u} [Group X] [Finite X]
    {κ : GroupClass.{u}}
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (hsq : IsSQTK κ X) (B : Subgroup X) (hB : B.IsCComponent)
    (hr : 2 ≤ primeRank 3 B) :
    IsQuasisimple (B ⧸ pCore 2 B) ∧ primeRank 3 (center (B ⧸ pCore 2 B)) ≤ 1 := by
  have hsqQ : IsSQTK κ (X ⧸ pCore 2 X) := by
    refine ⟨?_, hsq.isKGroup.quotient (pCore 2 X)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have ha := proposition_1_2_1_four_earlier_conclusion hA36 hsqQ hB
  let e := cComponentTwoCoreQuotientEquiv hB
  have hrQ : 2 ≤ primeRank 3 (B ⧸ pCore 2 B) := by
    apply hr.trans
    apply rank_le_of_coprime_kernel (QuotientGroup.mk' (pCore 2 B))
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrI : 2 ≤ primeRank 3 (B.map (QuotientGroup.mk' (pCore 2 X))) := by
    rwa [← primeRank_equiv 3 e]
  obtain ⟨hq, hz⟩ := classified_intrinsic _ ha.1 hrI
  let := hq
  refine ⟨IsQuasisimple.of_mulEquiv e.symm, ?_⟩
  rwa [primeRank_equiv 3 (centerCongr e)]

open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection

/-- Apply the universal A.3.6 classification in KTᵥ, the overgroup actually
supplied by Yz. No C-component assertion in KLᵥ is needed for this deduction. -/
theorem source_intrinsic_quasisimple {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 K = 2) :
    IsQuasisimple (K ⧸ pCore 2 K) ∧ primeRank 3 (center (K ⧸ pCore 2 K)) ≤ 1 := by
  let D := K ⊔ Tv T v
  let B := K.subgroupOf D
  have hle : D ≤ Gv v := sup_le hK.1.1 inf_le_right
  have hsq : IsSQTK κ D := (IsSQTK.equiv (subgroupOfEquivOfLe hle)).mp
    ((hG.involution_centralizer_sqtk hv).subgroup (D.subgroupOf (Gv v)))
  let e : B ≃* K := subgroupOfEquivOfLe le_sup_left
  let eQ := QuotientGroup.congr (pCore 2 B) (pCore 2 K) e (pCore_map_iso 2 e)
  have hrB : 2 ≤ primeRank 3 B := by rw [primeRank_equiv 3 e, hr]
  obtain ⟨hq, hz⟩ := cComponent_twoCore_quasisimple_of_three_rank hA36 hsq B hK.1.2.1 hrB
  let := hq
  refine ⟨IsQuasisimple.of_mulEquiv eQ, ?_⟩
  rwa [← primeRank_equiv 3 (centerCongr eQ)]

/-- The actual three hypotheses available before the remaining localization
step: SQTK for H, rank two for C, and the intrinsic quasisimple quotient. -/
theorem source_local_intrinsic {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hr : primeRank 3 K = 2) :
    IsSQTK κ (localActor K L v) ∧ primeRank 3 (localComponent K L v) = 2 ∧
      IsQuasisimple (localComponent K L v ⧸ pCore 2 (localComponent K L v)) ∧
      primeRank 3 (center (localComponent K L v ⧸ pCore 2 (localComponent K L v))) ≤ 1 := by
  obtain ⟨hq, hz⟩ := source_intrinsic_quasisimple hG hA36 K L T z v hv hK hr
  let := hq
  exact ⟨localActor_sqtk hG K L T z v hv hK, (localComponent_rank K L v).trans hr,
    IsQuasisimple.of_mulEquiv (localTwoCoreEquiv K L v).symm,
    (localTwoCore_center_rank K L v).trans_le hz⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication
