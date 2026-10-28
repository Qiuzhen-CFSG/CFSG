module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupAction.FixedLineCoreSize
public import Theory.SpecificGroups.DihedralSolvable

/-!
# Direct order bounds for the original quintic parabolic

Let U=⟨Vᴴ⟩. The original source gives an elementary U, an action kernel
contained in O₂(H), and a unique Sylow-fixed point Z of order two which H
centralizes. The faithful action image has trivial odd core by coprime
splitting and the fixed-line argument. Its two-core therefore admits a
nontrivial five-action and has order at least sixteen. Since U centralizes
itself, core lifting gives |O₂(H)|≥16|U|≥512.

The genuine Sz(2) quotient now gives |T|≥2048 and |H|≥10240 without path
transitivity, an endpoint model, or generating relations. Both source
quotient alternatives give |T|≥1024. Failure of the desired 2048 bound
forces the D₁₀ quotient and the exact orders |T|=1024, |O₂(H)|=512, |U|=32.
That configuration is not excluded here. Its exclusion and the remaining
eight-path actors stay with the consolidated source owner.

Source: Aschbacher--Smith 14.2.6,14.2.20--21, printed pp.982,988--989;
the original U/Z kernel is12.8.4, p.850. The elementary five-action
cardinality argument is Parrott (1972), p.672.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The original two-core has at least sixteen times the order of the
kernel of its action on the elementary closure. Both quotient rows are retained. -/
theorem source_quintic_action_core_lower
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    16 * Nat.card (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) : Subgroup G) ≤
      Nat.card (pCore 2 H) := by
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨hel, _⟩ := source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 U := hel
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨hHF, hlocal, _, _, _, hk⟩ := hloc H hH.1
  have hUQ : U ≤ H.pCoreIn 2 := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hUH : U ≤ H := hUQ.trans (pCoreIn_le 2 H)
  have hUT : U ≤ (T : Subgroup G) := hUQ.trans (by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH))
  let : MulDistribMulAction H U :=
    conjMulDistribMulActionOfLeNormalizer H U (le_normalizer_conjugateSpanBy _ _)
  let f : H →* MulAut U := MulDistribMulAction.toMulAut H U
  let S := T.subtype hTH
  have hker : f.ker ≤ pCore 2 H := by
    intro a ha
    rw [←hk]
    apply (F.mem_localTildeAction_ker_iff H hHF a).mpr
    intro u hu
    have huU : u ∈ U := by
      change u ∈ conjugateSpanBy (rankTwoSeed T M) H at hu
      simpa only [rankTwoSeed_eq_localModule] using hu
    have hh := DFunLike.congr_fun (show f a = 1 from ha) (⟨u,huU⟩ : U)
    have heq := congrArg U.subtype hh
    change (a:G)*u*(a:G)⁻¹=u at heq
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mul_inv_eq_iff_eq_mul.mp heq)]
    exact one_mem _
  let Z := (centralInvolutions T).subgroupOf U
  have hZU : centralInvolutions T ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZcard : Nat.card Z = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hfix : FixedPoints.subgroup S U = Z := by
    apply le_antisymm
    · intro u hu
      apply (mem_omegaOneCenterAmbient_iff _ _).mpr
      refine ⟨hUT u.property, elemPow_eq_one_of_isElementaryAbelian (u:G) u.property, ?_⟩
      intro t ht
      have hh := congrArg U.subtype (hu ⟨⟨t,hTH ht⟩,ht⟩)
      change t*(u:G)*t⁻¹=(u:G) at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro u hu s
      apply Subtype.ext
      change (s:H).val*(u:G)*(s:H).val⁻¹=(u:G)
      have hh := (mem_omegaOneCenterAmbient_iff _ _).mp hu
      exact mul_inv_eq_iff_eq_mul.mpr (hh.2.2 _ s.property)
  have hHZ := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hline : ∀ h : H, ∀ u ∈ FixedPoints.subgroup S U, h • u = u := by
    intro h u hu
    rw [hfix] at hu
    apply Subtype.ext
    change (h:G)*(u:G)*(h:G)⁻¹=(u:G)
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp (hHZ h.property) _ hu).symm
  have hsolv : Group.IsSolvable H := by
    have hQsolv : Group.IsSolvable (pCore 2 H) := by
      let := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
      infer_instance
    apply (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr
    refine ⟨hQsolv, ?_⟩
    rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hD | hS
    · obtain ⟨eD⟩ := hD
      let := GLS3.Chapter5.dihedralGroup_isSolvable 5
      exact Group.isSolvable_of_isSolvable_injective (f := eD.toMonoidHom) eD.injective
    · obtain ⟨eH⟩ := hS
      let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
      exact Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
  have hfive : 5 ∣ Nat.card H := by
    have hh := ((T : Subgroup G).subgroupOf H).index_dvd_card
    change (T : Subgroup G).relIndex H ∣ Nat.card H at hh
    rwa [hi] at hh
  have hb := Theory.GroupAction.core_lower_of_fixed_line hsolv S
    (by rw [hfix, hZcard]) hline (pCore_isPGroup.to_le hker) hfive
  have hkEq : f.ker = (centralizer (U : Set G)).subgroupOf H := by
    ext h
    constructor
    · intro hh
      apply mem_centralizer_iff.mpr
      intro u hu
      have he := congrArg U.subtype (DFunLike.congr_fun (show f h = 1 from hh) ⟨u, hu⟩)
      change (h:G) * u * (h:G)⁻¹ = u at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hh
      change f h = 1
      ext u
      change (h:G) * (u:G) * (h:G)⁻¹ = (u:G)
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hh u u.property).symm
  rw [hkEq, ← inf_subgroupOf_left,
    Nat.card_congr (subgroupOfEquivOfLe (show H ⊓ centralizer (U : Set G) ≤ H from inf_le_left)).toEquiv] at hb
  exact hb

/-- The original quintic core has at least sixteen times as many elements as
its elementary closure. Both original quotient alternatives are retained. -/
theorem source_quintic_core_lower
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    16 * Nat.card (conjugateSpanBy (localModule T M) H) ≤ Nat.card (pCore 2 H) := by
  have hb := source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
  let U := conjugateSpanBy (localModule T M) H
  have hel := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  let : IsElementaryAbelian 2 U := hel
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  obtain ⟨he, F, hp, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨hHF, hlocal, _, _, _, hk⟩ := hloc H hH.1
  have hUQ : U ≤ H.pCoreIn 2 := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hUH : U ≤ H := hUQ.trans (pCoreIn_le 2 H)
  have hUk : U ≤ H ⊓ centralizer (U : Set G) := le_inf hUH (le_centralizer U)
  exact (Nat.mul_le_mul_left 16 (card_le_of_le hUk)).trans hb

/-- A direct bound under the genuine Suzuki quotient, before path or model recognition. -/
theorem source_quintic_sylow_lower_of_suzuki
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
    2048 ≤ Nat.card (T : Subgroup G) := by
  have hb := source_quintic_core_lower hG T hempty hM hu hmany hcard e H hH hi
  have hU := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).2
  have hQ : 512 ≤ Nat.card (pCore 2 H) := by rcases hU with hU | hU <;> rw [hU] at hb <;> omega
  have hquot : Nat.card (H ⧸ pCore 2 H) = 20 :=
    (Nat.card_congr eH.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hc := (pCore 2 H).index_mul_card
  change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
  rw [hquot] at hc
  have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
  rw [hi] at ht
  omega

/-- Both original quotient branches give a direct Sylow bound of 1024. -/
theorem source_quintic_sylow_lower_1024
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    1024 ≤ Nat.card (T : Subgroup G) := by
  rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hD | hS
  · obtain ⟨eD⟩ := hD
    have hb := source_quintic_core_lower hG T hempty hM hu hmany hcard e H hH hi
    have hU := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).2
    have hQ : 512 ≤ Nat.card (pCore 2 H) := by rcases hU with hU | hU <;> rw [hU] at hb <;> omega
    have hquot : Nat.card (H ⧸ pCore 2 H) = 10 :=
      (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
    have hc := (pCore 2 H).index_mul_card
    change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
    rw [hquot] at hc
    have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
    change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
    rw [hi] at ht
    omega
  · obtain ⟨eH⟩ := hS
    exact (by decide : 1024 ≤ 2048).trans
      (source_quintic_sylow_lower_of_suzuki hG T hempty hM hu hmany hcard e H hH hi eH)

/-- The direct Suzuki branch supplies the literal parabolic-order premise. -/
theorem source_quintic_first_lower_of_suzuki
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
    10240 ≤ Nat.card H := by
  have h := source_quintic_sylow_lower_of_suzuki hG T hempty hM hu hmany hcard e H hH hi eH
  have hc := ((T : Subgroup G).subgroupOf H).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hc
  change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at hc
  rw [hi] at hc
  omega

/-- Failure of the desired Sylow bound leaves exactly the dihedral row with
Sylow order 1024, core order 512 and elementary closure order 32. -/
theorem source_quintic_small_sylow_configuration
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
    Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∧
      Nat.card (T : Subgroup G) = 1024 ∧ Nat.card (pCore 2 H) = 512 ∧
      Nat.card (conjugateSpanBy (localModule T M) H) = 32 := by
  have hb := source_quintic_sylow_lower_1024 hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hnlo : 10 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [hn, show 2^10=1024 from rfl] using hb)
  have hnhi : n < 11 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [hn, show 2^11=2048 from rfl] using hsmall)
  have hT : Nat.card (T : Subgroup G) = 1024 := by rw [hn, show n=10 by omega]; rfl
  rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hD | hS
  · obtain ⟨eD⟩ := hD
    have hquot : Nat.card (H ⧸ pCore 2 H) = 10 :=
      (Nat.card_congr eD.toEquiv).trans DihedralGroup.nat_card
    have hc := (pCore 2 H).index_mul_card
    change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
    rw [hquot] at hc
    have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at ht
    change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
    rw [hi,hT] at ht
    have hQ : Nat.card (pCore 2 H) = 512 := by omega
    refine ⟨⟨eD⟩,hT,hQ,?_⟩
    have hU := (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).2
    have hl := source_quintic_core_lower hG T hempty hM hu hmany hcard e H hH hi
    rw [hQ] at hl
    omega
  · obtain ⟨eH⟩ := hS
    have hl := source_quintic_sylow_lower_of_suzuki hG T hempty hM hu hmany hcard e H hH hi eH
    omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
