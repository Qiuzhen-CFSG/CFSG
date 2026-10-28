module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveStructure
public import CFSG.Quasithin.Chapter14.Section02.RankTwoLocal
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.GroupAction.CyclicImageFixedBound

/-!
# Core movement and the first quintic four-cycle

In the Sz(2) quotient case, suppose the quintic two-core centralizes the
original plane V. Normality makes it centralize U=⟨Vᴴ⟩. The Sylow action
on U then factors through a cyclic group of order four, while its fixed
subgroup lies in the original central point of order two. The fourth-power
fixed-point bound gives |U| ≤ 16, contradicting |U| = 32 or 64.

The cubic core has index two in T. Hence the two cores generate T, and the
cubic core maps onto the cyclic Sylow subgroup of H/O₂(H). A lifted generator
has local order four at H and lies in the cubic radius-one kernel. This is
the algebraic input for the first even path extension in `EvenActors`.

The quotient equivalence remains an explicit source alternative; the D₁₀
exclusion and final assembly are owned by qt-e-quintic-sylow-lower.
Source: Aschbacher--Smith 14.2.6 and 14.2.20--21, pp.982 and988--989;
F.1.11--12, pp.262--264, for the original amalgam context.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
private theorem suzuki_zero_sylow_cyclic (P : Sylow 2 (SuzukiMatrixGroup 0)) :
    IsCyclic P ∧ Nat.card P = 4 := by
  let R : Sylow 2 (SuzukiMatrixGroup 0) := Sylow.ofCard
    (zpowers suzukiZeroRootGenerator) (by
      rw [Nat.card_zpowers, suzukiZeroRootGenerator_order, suzukiZero_card]
      decide +kernel)
  let : IsCyclic R := inferInstanceAs (IsCyclic (zpowers suzukiZeroRootGenerator))
  refine ⟨isCyclic_of_injective (P.equiv R).toMonoidHom (P.equiv R).injective, ?_⟩
  exact (Nat.card_congr (P.equiv R).toEquiv).trans (by
    change Nat.card (zpowers suzukiZeroRootGenerator) = 4
    rw [Nat.card_zpowers, suzukiZeroRootGenerator_order])

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The quintic core cannot centralize the original plane, even in the Suzuki row. -/
theorem source_suzuki_core_moves_plane
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
    ¬ H.pCoreIn 2 ≤ centralizer (localModule T M : Set G) := by
  intro hcent
  let U := conjugateSpanBy (localModule T M) H
  obtain ⟨hel, hUcard⟩ := source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 U := hel
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQU : H.pCoreIn 2 ≤ centralizer (U : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hcent
  obtain ⟨he, F, _, _, _, hloc⟩ := source_lemma_14_2_6
    hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_, hlocal, _, _, _, _⟩ := hloc H hH.1
  have hUQ : U ≤ H.pCoreIn 2 := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hUT : U ≤ (T : Subgroup G) := hUQ.trans (by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH))
  let : MulDistribMulAction H U :=
    conjMulDistribMulActionOfLeNormalizer H U (le_normalizer_conjugateSpanBy _ _)
  let f : H →* MulAut U := MulDistribMulAction.toMulAut H U
  let q : H →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
    eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := T.subtype hTH
  let P := S.mapSurjective hq
  obtain ⟨hcyc, hPc⟩ := suzuki_zero_sylow_cyclic P
  let : IsCyclic ((S : Subgroup H).map q) := hcyc
  have hk : q.ker ≤ f.ker := by
    intro a ha
    have haQ : a ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply eH.injective
      change q a = eH 1
      simpa only [map_one] using (show q a = 1 from ha)
    have haC := hQU (mem_map_of_mem H.subtype haQ)
    change f a = 1
    ext u
    change (a : G) * (u : G) * (a : G)⁻¹ = (u : G)
    have hh : (u : G) * (a : G) = (a : G) * (u : G) :=
      mem_centralizer_iff.mp haC (u : G) u.property
    rw [← hh, mul_inv_cancel_right]
  have hfix : FixedPoints.subgroup ((S : Subgroup H).map f) U ≤
      (centralInvolutions T).subgroupOf U := by
    intro u hu
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨hUT u.property, elemPow_eq_one_of_isElementaryAbelian (u : G) u.property, ?_⟩
    intro t ht
    have hh := hu ⟨f ⟨t,hTH ht⟩, mem_map_of_mem f ht⟩
    have heq := congrArg U.subtype hh
    change t * (u : G) * t⁻¹ = (u : G) at heq
    exact mul_inv_eq_iff_eq_mul.mp heq
  have hZcard : Nat.card ((centralInvolutions T).subgroupOf U) = 2 := by
    have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    have hZU : centralInvolutions T ≤ U := hZV.trans (le_conjugateSpanBy _ _)
    rw [Nat.card_congr (subgroupOfEquivOfLe hZU).toEquiv]
    exact plane_centralInvolutions_card T M hM.1.2 hcard e
  have hb := Theory.GroupAction.cyclic_image_fixed_bound q f (S : Subgroup H)
    (show Nat.card ((S : Subgroup H).map q) ∣ 4 by change Nat.card P ∣ 4; rw [hPc]) hk
  have hf := card_le_of_le hfix
  rw [hZcard] at hf
  have hb' := hb.trans (Nat.pow_le_pow_left hf 4)
  change Nat.card (conjugateSpanBy (localModule T M) H) ≤ 16 at hb'
  omega


omit [Finite G] in
private theorem sup_eq_of_index_two (S A B : Subgroup G)
    (hA : A ≤ S) (hB : B ≤ S) (hidx : A.relIndex S = 2) (hne : ¬ B ≤ A) :
    A ⊔ B = S := by
  have hm := relIndex_mul_relIndex A (A ⊔ B) S le_sup_left (sup_le hA hB)
  rw [hidx] at hm
  have hneq : A.relIndex (A ⊔ B) ≠ 1 := fun he =>
    hne (le_sup_right.trans (relIndex_eq_one.mp he))
  have hh : (A ⊔ B).relIndex S = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hneq hh.2).elim
  exact le_antisymm (sup_le hA hB) (relIndex_eq_one.mp hh)

/-- The cubic core contains an actor with local order four at the quintic endpoint. -/
theorem source_suzuki_cubic_core_actor
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
    ∃ a ∈ X.pCoreIn 2, a^4 ∈ H.pCoreIn 2 ∧ a^2 ∉ H.pCoreIn 2 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let SX := T.subtype hTX
  let SH := T.subtype hTH
  have hQXT : X.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [SX, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTX] using pCoreIn_le_sylow X SX
  have hQHT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [SH, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using pCoreIn_le_sylow H SH
  obtain ⟨hQX, ⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hidx : (X.pCoreIn 2).relIndex (T : Subgroup G) = 2 := by
    have hm := relIndex_mul_index (pCore_isPGroup.le_sylow_of_normal SX)
    rw [SymmetricThreeTwoCore.sylow_index_three eX SX,
      SymmetricThreeTwoCore.core_index eX] at hm
    have hi' : (pCore 2 X).relIndex (SX : Subgroup X) = 2 := by omega
    have hmap : (SX : Subgroup X).map X.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le hTX
    rw [←hmap, pCoreIn, relIndex_map_map_of_injective _ _ X.subtype_injective]
    exact hi'
  have hcross : ¬ H.pCoreIn 2 ≤ X.pCoreIn 2 := by
    intro hh
    apply source_suzuki_core_moves_plane hG T hempty hM hu hmany hcard e H hH hi eH
    rw [hQX] at hh
    exact hh.trans inf_le_right
  have hsup := sup_eq_of_index_two (T : Subgroup G) (X.pCoreIn 2) (H.pCoreIn 2)
    hQXT hQHT hidx hcross
  let q : H →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
    eH.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hq : Function.Surjective q := eH.surjective.comp (QuotientGroup.mk'_surjective _)
  let P := SH.mapSurjective hq
  obtain ⟨hcyc, hPc⟩ := suzuki_zero_sylow_cyclic P
  let : IsCyclic P := hcyc
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  rw [hPc] at ha
  let A := (X.pCoreIn 2).subgroupOf H
  have hjoin : A ⊔ pCore 2 H = (SH : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (hQXT.trans hTH),
      show (pCore 2 H).map H.subtype = H.pCoreIn 2 from rfl,
      hsup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  have hker : (pCore 2 H).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro x hx
    change eH (QuotientGroup.mk' (pCore 2 H) x) = 1
    have hqx : QuotientGroup.mk' (pCore 2 H) x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx, map_one]
  have hmap : A.map q = (P : Subgroup _) := by
    change A.map q = (SH : Subgroup H).map q
    rw [←hjoin, Subgroup.map_sup, hker, sup_bot_eq]
  have haA : (a : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∈ A.map q := by
    rw [hmap]
    exact a.property
  obtain ⟨x, hx, he⟩ := haA
  have h4 : (a : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)^4 = 1 := by
    have hh := pow_orderOf_eq_one a
    rw [ha] at hh
    exact congrArg Subtype.val hh
  have h2 : (a : BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0)^2 ≠ 1 := by
    intro hh
    have hh' : a^2 = 1 := Subtype.ext hh
    have hd := orderOf_dvd_of_pow_eq_one hh'
    rw [ha] at hd
    norm_num at hd
  refine ⟨x, hx, ?_, ?_⟩
  · have hx4 : x^4 ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply eH.injective
      change q (x^4) = eH 1
      rw [map_pow, he, h4, map_one]
    exact mem_map_of_mem H.subtype hx4
  · intro hx2
    have hx2' : x^2 ∈ pCore 2 H :=
      (mem_map_iff_mem (f := H.subtype) H.subtype_injective).mp hx2
    apply h2
    rw [←he, ←map_pow]
    change eH (QuotientGroup.mk' (pCore 2 H) (x^2)) = 1
    have hqx : QuotientGroup.mk' (pCore 2 H) (x^2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hx2'
    rw [hqx, map_one]

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
