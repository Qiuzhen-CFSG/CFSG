module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzuki
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionComponentRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# The five-divisor sieve for moved Suzuki support

Three commuting components whose orders are divisible by five exceed the
five-rank bound on the semisimple layer. Hence a Suzuki component orbit
centralizing a five-divisible component consists of one component. The
Suzuki endpoint can then be applied without an invariance assumption.

Every marked D.3.10 constituent except odd-degree natural SL₃ has order
divisible by five. The proof uses the SL₂ block in SL₃, the actual Sp₄
order and the binary linear and alternating orders, preserving all five
constituent branches, including A₇.

A commuting component of three-rank one likewise forces three-rank at
most one in the distinguished component: its perfect cyclic-Sylow cover
has center prime to three, so the layer ranks add.

The component comparison adapts the proof in Chapter11's
`Multiplicity/SuzukiInvariant`. The actual chosen-seed application is in
`SeedAlternativesMovedExhaustionSuzukiFive`. The remaining odd-degree
Suzuki, rank-one component and FF-section cases, and final Source325
assembly, remain with qt-baumann-fsu.
Source: Aschbacher--Smith A.1.31, Theorem A and D.3.9--14,
printed pp.29,33--41,200--202; application3.2.5, p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource

private theorem linearThree_five_dvd_of_even (F : BinaryField) (he : Even F.degree) :
    5 ∣ Nat.card SL(3,F.Carrier) := by
  have hd : 5 ∣ Nat.card SL(2,F.Carrier) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,F.card_eq]
    apply dvd_mul_of_dvd_right
    rw [←pow_mul]
    apply (by decide : 5 ∣ 2 ^ 4 - 1).trans
    apply Nat.pow_sub_one_dvd_pow_sub_one
    obtain ⟨k,hk⟩ := he
    exact ⟨k,by omega⟩
  exact hd.trans (card_dvd_of_injective
    ((Matrix.SL3.blockEmbedding F.Carrier).comp Matrix.SpecialLinearGroup.toGL)
    ((Matrix.SL3.blockEmbedding_injective F.Carrier).comp Matrix.SpecialLinearGroup.toGL_injective))

private theorem symplecticFour_five_dvd (F : BinaryField) :
    5 ∣ Nat.card (Matrix.symplecticGroup (Fin 2) F.Carrier) := by
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,F.card_eq]
  apply dvd_mul_of_dvd_right
  rw [←pow_mul, Nat.mul_comm F.degree 4]
  exact (by decide : 5 ∣ 2 ^ 4 - 1).trans
    (by apply Nat.pow_sub_one_dvd_pow_sub_one; exact dvd_mul_right 4 F.degree)

private theorem binaryHigher_five_dvd (n : ℕ) (hn : n = 4 ∨ n = 5) :
    5 ∣ Nat.card SL(n,ZMod 2) := by
  rw [BinaryLinear.card_SL]
  rcases hn with rfl | rfl <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ]

/-- Among the literal marked constituent models, order prime to five
leaves only the natural SL₃ representation in odd field degree. -/
theorem constituentModel_linearThree_of_five_free
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (hm : ConstituentModel ρ)
    (hfive : ¬ 5 ∣ Nat.card A) :
    ∃ F : BinaryField, Odd F.degree ∧ Nonempty (ActionEquiv ρ (linearNatural F 3)) := by
  rcases hm with hm | hm | hm | hm | hm
  · obtain ⟨F,⟨e⟩⟩ := hm
    refine ⟨F,Nat.not_even_iff_odd.mp (fun he => hfive ?_),⟨e⟩⟩
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact linearThree_five_dvd_of_even F he
  · obtain ⟨F,_,⟨e⟩⟩ := hm
    apply (hfive ?_).elim
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact symplecticFour_five_dvd F
  · obtain ⟨e⟩ := hm
    apply (hfive ?_).elim
    rw [Nat.card_congr e.groupEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num
  · obtain ⟨n,hn,⟨e⟩⟩ := hm
    apply (hfive ?_).elim
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact binaryHigher_five_dvd n hn
  · obtain ⟨σ,_,⟨e⟩⟩ := hm
    apply (hfive ?_).elim
    rw [Nat.card_congr e.groupEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num

private theorem components_eq_of_five_rank {H : Type*} [Group H] [Finite H]
    (K P Q : Subgroup H) (hK : IsComponent H K) (hP : IsComponent H P)
    (hQ : IsComponent H Q) (hr : primeRank 5 (componentLayer H) ≤ 2)
    (hPK : P ≤ centralizer (K : Set H)) (hQK : Q ≤ centralizer (K : Set H))
    (hPz : Nat.Coprime 5 (Nat.card (center P)))
    (hQz : Nat.Coprime 5 (Nat.card (center Q)))
    (hdK : 5 ∣ Nat.card K) (hdP : 5 ∣ Nat.card P) (hdQ : 5 ∣ Nat.card Q) : P = Q := by
  by_contra hn
  have hPQ : P ≤ centralizer (Q : Set H) :=
    commutator_eq_bot_iff_le_centralizer.mp (hP.commutator_eq_bot_of_ne hQ hn)
  let E := componentLayer H
  have hk : K ≤ E := le_sSup hK
  have hp : P ≤ E := le_sSup hP
  have hq : Q ≤ E := le_sSup hQ
  let eK := subgroupOfEquivOfLe hk
  let eP := subgroupOfEquivOfLe hp
  let eQ := subgroupOfEquivOfLe hq
  have hh := primeRank_three_of_commuting_of_centers_coprime (p := 5)
    (P.subgroupOf E) (Q.subgroupOf E) (K.subgroupOf E)
    (fun p hp q hq => Subtype.ext (hPQ hp q hq))
    (fun k hk p hp => Subtype.ext ((hPK hp k hk).symm))
    (fun k hk q hq => Subtype.ext ((hQK hq k hk).symm))
    (by rwa [Nat.card_congr (centerCongr eP).toEquiv])
    (by rwa [Nat.card_congr (centerCongr eQ).toEquiv])
    (by rwa [Nat.card_congr eP.toEquiv])
    (by rwa [Nat.card_congr eQ.toEquiv])
    (by rwa [Nat.card_congr eK.toEquiv])
  change 3 ≤ primeRank 5 (componentLayer H) at hh
  omega

private theorem suzuki_five_dvd (m : ℕ) (hm : 0 < m) :
    5 ∣ Nat.card (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  rw [BenderSuzuki.MatrixGroups.suzukiMatrixGroup_card m hm]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_left
  rw [Nat.dvd_iff_mod_eq_zero]
  have he : (2 ^ (2 * m + 1)) ^ 2 = 4 * 16 ^ m := by
    rw [←pow_mul]
    have he : (2 * m + 1) * 2 = 2 + 4 * m := by omega
    rw [he,pow_add,pow_mul]
    norm_num
  rw [he,Nat.add_mod,Nat.mul_mod]
  have h16 : 16 ^ m % 5 = 1 := by
    change Nat.ModEq 5 (16 ^ m) 1
    simpa using (show Nat.ModEq 5 16 1 by decide).pow m
  rw [h16]

/-- Five-rank on the actual semisimple layer forces a Suzuki orbit in the
centralizer of a five-divisible component to be a singleton. -/
theorem suzuki_orbit_singleton_of_component_five_dvd
    {H : Type*} [Group H] [Finite H]
    (K J A : Subgroup H) (hK : IsComponent H K) (hJ : IsComponent H J)
    (hr : primeRank 5 (componentLayer H) ≤ 2)
    (hfive : 5 ∣ Nat.card K) (ho : componentOrbit J A ≤ centralizer (K : Set H))
    {r : ℕ} (hrpos : 0 < r)
    (e : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    A ≤ normalizer (J : Set H) ∧ componentOrbit J A = J := by
  let := hJ.2
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :=
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 r hrpos).1
  let : IsSimpleGroup J := e.isSimpleGroup
  have hz : center J = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hh))
  have hPz : Nat.Coprime 5 (Nat.card (center J)) := by simp [hz]
  have hdJ : 5 ∣ Nat.card J := by
    rw [Nat.card_congr e.toEquiv]
    exact suzuki_five_dvd r hrpos
  have hn : A ≤ normalizer (J : Set H) := by
    intro a ha
    apply mem_normalizer_iff_map_conj_eq.mpr
    let Q := J.map (MulAut.conj a).toMonoidHom
    let eJ : J ≃* Q := J.equivMapOfInjective _ (MulAut.conj a).injective
    have hQle : Q ≤ componentOrbit J A :=
      le_iSup (fun a : A => J.map (MulAut.conj (a : H)).toMonoidHom) ⟨a,ha⟩
    exact (components_eq_of_five_rank K J Q hK hJ (hJ.map_conj a) hr
      ((le_componentOrbit J A).trans ho) (hQle.trans ho) hPz
      (by rwa [←Nat.card_congr (centerCongr eJ).toEquiv]) hfive hdJ
      (by rwa [←Nat.card_congr eJ.toEquiv])).symm
  exact ⟨hn,le_antisymm (iSup_conjugates_le_of_le_normalizer J A J le_rfl hn)
    (le_componentOrbit J A)⟩

/-- A rank-one component commuting with K leaves at most one ternary rank
for K in the actual semisimple layer. Perfectness removes the ternary
center of the rank-one component before adding the two contributions. -/
theorem component_three_rank_le_one_of_commuting_rank_one
    {H : Type*} [Group H] [Finite H]
    (K J : Subgroup H) (hK : IsComponent H K) (hJ : IsComponent H J)
    (hr : primeRank 3 (componentLayer H) ≤ 2)
    (hJK : J ≤ centralizer (K : Set H)) (hrJ : primeRank 3 J = 1) :
    primeRank 3 K ≤ 1 := by
  let := hJ.2
  let P : Sylow 3 J := default
  let := P.isCyclic_of_odd_of_primeRank_le_one (by decide : Odd 3) hrJ.le
  have hn := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow
    (QuotientGroup.mk' (center J)) (by rw [QuotientGroup.ker_mk']) P inferInstance
  rw [QuotientGroup.ker_mk'] at hn
  have hcop : Nat.Coprime 3 (Nat.card (center J)) :=
    Nat.prime_three.coprime_iff_not_dvd.mpr hn
  let E := componentLayer H
  have hKE : K ≤ E := le_sSup hK
  have hJE : J ≤ E := le_sSup hJ
  have hcomm : K.subgroupOf E ≤ centralizer (J.subgroupOf E : Set E) := by
    intro k hk j hj
    exact Subtype.ext ((hJK hj k hk).symm)
  have hs := (ResidualCentralizerRank.primeRank_add_le_of_center_coprime
    (K.subgroupOf E) (J.subgroupOf E) hcomm (by
      rwa [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hJE)).toEquiv])).trans hr
  rw [primeRank_congr 3 (subgroupOfEquivOfLe hKE),
    primeRank_congr 3 (subgroupOfEquivOfLe hJE),hrJ] at hs
  omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
