module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSourceRankOne.Selection
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.CoprimeGeneration
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration

/-!
# The four-group branch of Lemma 16.3

If a four-subgroup of D centralizes the marked pair, the three centralizer
circles cannot all be solvable. Otherwise Corollary 7.14 and the singleton
trace conclusion force its three fixed subgroups in O₂′(D) to centralize z.
Coprime fixed-point generation then centralizes the whole odd core. The
actual odd-core orbit of z contradicts its nontrivial M-class.

Source: GLS4, Chapter 2, Lemma 16.3, second half of the proof.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem odd_le_of_four_fixed
    (N W H : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hN : Odd (Nat.card N)) (hn : W ≤ normalizer N)
    (hc : ∀ w : W, (w : G) ≠ 1 → N ⊓ centralizer ({(w : G)} : Set G) ≤ H) : N ≤ H := by
  let : CommGroup W := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 W) := ⟨IsElementaryAbelian.isPGroup 2 W⟩
  let : MulDistribMulAction W N := conjMulDistribMulActionOfLeNormalizer W N hn
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := N) (A := W) 2 hN.coprime_two_left
  have htop : (⊤ : Subgroup N) ≤ H.comap N.subtype := by
    rw [← hgen]
    refine iSup₂_le fun Y hY => ?_
    have hquot : Nat.card (W ⧸ Y) ≤ 2 := by
      apply Nat.le_of_dvd (by decide)
      rw [← hY.exponent_eq_card]
      exact (Group.exponent_quotient_dvd Y).trans (IsElementaryAbelian.exponent_dvd_p 2 W)
    have hprod := card_eq_card_quotient_mul_card_subgroup Y
    rw [hW] at hprod
    let : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp (by nlinarith)
    obtain ⟨w, hw⟩ := exists_ne (1 : Y)
    have hne : (((w : W) : G)) ≠ 1 := by
      intro he
      exact hw (Subtype.ext (Subtype.ext he))
    intro x hx
    apply hc (w : W) hne
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he := congrArg Subtype.val (hx w)
    change ((w : W) : G) * (x : G) * ((w : W) : G)⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  intro x hx
  exact htop (mem_top (⟨x,hx⟩ : N))

omit [Finite G] in
/-- A singleton distinguished trace makes the full local centralizer in M
centralize its unique distinguished involution. -/
public theorem centralizerInM_le_of_singleton_trace
    (h : IsProductDisconnected Z M) {z w : G}
    (hz : z ∈ residualCentralizerTrace Z M w)
    (htrace : (residualCentralizerTrace Z M w).ncard = 1) :
    M ⊓ centralizer ({w} : Set G) ≤ centralizer ({z} : Set G) := by
  have huniq : ∀ y ∈ residualCentralizerTrace Z M w, y = z := by
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp htrace
    have hzy : z = y := by simpa only [hy, Set.mem_singleton_iff] using hz
    intro v hv
    exact (show v = y by simpa only [hy, Set.mem_singleton_iff] using hv).trans hzy.symm
  intro x hx
  have hxc : Commute x w := mem_centralizer_singleton_iff.mp hx.2
  have hfixed : MulAut.conj x w = w := by
    change x * w * x⁻¹ = w
    rw [hxc.eq, mul_inv_cancel_right]
  have hconj : Commute (MulAut.conj x z) w := by
    have hc := hz.2.2.map (MulAut.conj x).toMonoidHom
    change Commute (MulAut.conj x z) (MulAut.conj x w) at hc
    rwa [hfixed] at hc
  have he := huniq (MulAut.conj x z)
    ⟨h.invariant _ _ hz.1, M.mul_mem (M.mul_mem hx.1 hz.2.1) (M.inv_mem hx.1), hconj⟩
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- In the four-group branch, a solvable escaping centralizer forces the
entire actual odd core of D to centralize the marked z. The next source
step uses the odd-core orbit to contradict the nontrivial M-class of z. -/
public theorem residualOddCore_centralizes_of_solvable_circle_of_four
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t z u : G} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z) (hzM : z ∈ M)
    (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (huC : ¬ centralizer ({u} : Set G) ≤ M)
    (hsol : Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))))
    (W : Subgroup G) [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hWD : W ≤ residualPairStabilizer M t)
    (hWz : W ≤ centralizer ({z} : Set G)) :
    residualOddCore M t ≤ centralizer ({z} : Set G) := by
  apply odd_le_of_four_fixed (residualOddCore M t) W _ hW residualOddCore_odd
    (hWD.trans (le_sup_left.trans (pair_sup_zpowers_le_normalizer_residualOddCore
      (h.disconnected.involutions t ht))))
  intro w hw
  have hwi : PFAppendixIII.IsInvolution (w : G) := by
    refine ⟨hw, ?_⟩
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w)
  have hwM : (w : G) ∈ M := (hWD w.property).1
  have hwC := residualInvolution_centralizer_not_le h.disconnected r ht htM hwi (hWD w.property)
  have hwsol := (centralizerCircle_solvable_iff h r ha hu huM huC hwi hwM hwC).mp hsol
  have htrace := residualCentralizerTrace_ncard_eq_one_of_solvable
    h.disconnected r ha hwi hwM hwC hwsol
  apply le_trans (inf_le_inf (residualOddCore_le_pair.trans inf_le_left) le_rfl)
  exact centralizerInM_le_of_singleton_trace h.disconnected
    ⟨hz, hzM, (mem_centralizer_singleton_iff.mp (hWz w.property)).symm⟩ htrace

/-- The odd core cannot centralize a distinguished involution in M: the
literal odd inverted representatives move it over its nontrivial M-class. -/
public theorem residualOddCore_not_le_distinguished_centralizer
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t z : G} (ht : t ∈ Z) (htM : t ∉ M) (hz : z ∈ Z) (hzM : z ∈ M) :
    ¬ residualOddCore M t ≤ centralizer ({z} : Set G) := by
  intro hc
  have huniq : ∀ y ∈ Z, y ∈ M → y = z := by
    intro y hy hyM
    obtain ⟨k, hk, he⟩ := distinguished_exists_inverted_oddCore_conjugator h hz hzM ht htM hy hyM
    have hkz := mem_centralizer_singleton_iff.mp (hc hk.1)
    rw [← he]
    rw [rightConjugateElem, mul_assoc, ← hkz, inv_mul_cancel_left]
  have hMC : M ≤ centralizer ({z} : Set G) := by
    intro m hm
    have he := huniq (MulAut.conj m z) (h.invariant _ _ hz)
      (M.mul_mem (M.mul_mem hm hzM) (M.inv_mem hm))
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)
  have htop : (M ⊓ centralizer ({z} : Set G)).subgroupOf M = ⊤ :=
    subgroupOf_eq_top.mpr (le_inf le_rfl hMC)
  have hgt := action_one_lt_m h r hz hzM
  change 1 < ((M ⊓ centralizer ({z} : Set G)).subgroupOf M).index at hgt
  rw [htop, index_top] at hgt
  omega

/-- The rank-greater-than-one branch of Lemma 16.3: every escaping
involution centralizer in M has nonsolvable distinguished circle. -/
public theorem involutionCentralizer_circle_nonsolvable_of_pair_twoRank
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    {t u : G} (ht : t ∈ Z) (htM : t ∉ M)
    (hrank : TwoRankAtLeastTwo (residualPairStabilizer M t))
    (hu : PFAppendixIII.IsInvolution u) (huM : u ∈ M)
    (huC : ¬ centralizer ({u} : Set G) ≤ M) :
    ¬ Group.IsSolvable (localCircle Z (centralizer ({u} : Set G))) := by
  intro hsol
  obtain ⟨E, hE, hE2⟩ := hrank
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := isMulCommutative_of_forall_sq_one hE2
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hE2 }
  let D := residualPairStabilizer M t
  let W := E.map D.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map D.subtype
  have hW : Nat.card W = 4 := by
    rw [card_map_of_injective D.subtype_injective]
    exact hE
  have hWD : W ≤ D := map_subtype_le E
  obtain ⟨z, hz, hzM, hWz⟩ := twoSubgroup_exists_distinguished_centralizer h.disconnected r
    W (IsElementaryAbelian.isPGroup 2 W) (hWD.trans inf_le_left)
  exact residualOddCore_not_le_distinguished_centralizer h.disconnected r ht htM hz hzM
    (residualOddCore_centralizes_of_solvable_circle_of_four h r ha ht htM hz hzM hu huM huC hsol
      W hW hWD hWz)

end BenderSuzuki.ZD
