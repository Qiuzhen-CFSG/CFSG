module

public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import Theory.GroupAction.ThreeSupportDisplacement
public import Theory.GroupTheory.CoprimeCentralizerDecomposition.CubicQuotient
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Normalization of a cubic actor from commuting conjugates

Three distinct commuting conjugates of a cubic block have disjoint elementary
four cores.  Their join is abelian, and a cubic actor cycling the supports
would displace a product of two supports injectively.  This gives sixteen
commutators, contradicting the four-element ambient displacement supplied by
`IsBlock.ambient_core_commutator`.

Source: Aschbacher--Smith, C.1.9, printed p.123 (the displacement step citing
Aschbacher (1981), §3.4).
-/

set_option linter.style.haveILetI false

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BlockCommutation

private theorem normal_core_dichotomy_local
    {L : Type*} [Group L] [Finite L]
    (hU : pCore 2 L = blockU L) (hc : Nat.card (pCore 2 L) = 4)
    (N : Subgroup L) [N.Normal] (hN : N ≤ pCore 2 L) :
    N = ⊥ ∨ N = pCore 2 L := by
  have hd : Nat.card N ∣ 2 ^ 2 := by simpa [hc] using card_dvd_of_le hN
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases n
  · exact Or.inl (Subgroup.card_eq_one.mp (by simpa using he))
  · right
    have hNcard : Nat.card N = 2 := by simpa using he
    let q := QuotientGroup.mk' N
    let f := q.subgroupMap (pCore 2 L)
    have hk : f.ker = N.subgroupOf (pCore 2 L) := by
      ext x
      rw [MonoidHom.mem_ker, Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff (N := N) (x : L)
    have himage : Nat.card ((pCore 2 L).map q) = 2 := by
      have hh := f.ker.index_mul_card
      rw [index_eq_card,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
          (q.subgroupMap_surjective (pCore 2 L))).toEquiv,
        hk, Nat.card_congr (subgroupOfEquivOfLe hN).toEquiv, hNcard, hc] at hh
      omega
    have hcentral := central_of_normal_card_two ((pCore 2 L).map q) himage
    have hmap : (blockU L).map q = ⊥ := by
      rw [blockU, map_commutator,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective N),
        commutator_top_right_eq_bot_iff_le_center]
      exact hcentral
    have hUN : blockU L ≤ N := by
      simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hmap
    exact le_antisymm hN (by rwa [hU])
  · exact Or.inr (eq_of_le_of_card_ge hN (by simpa [hc] using he.ge))

private theorem core_inf_center_bot_local
    {L : Type*} [Group L] [Finite L]
    (hU : pCore 2 L = blockU L) (hc : Nat.card (pCore 2 L) = 4) :
    pCore 2 L ⊓ center L = ⊥ := by
  have hne : pCore 2 L ≠ ⊥ := by
    intro hb
    rw [hb, card_bot] at hc
    omega
  have hncentral : ¬ pCore 2 L ≤ center L := by
    intro hh
    have hb := commutator_top_right_eq_bot_iff_le_center.mpr hh
    change blockU L = ⊥ at hb
    exact hne (hU.trans hb)
  rcases normal_core_dichotomy_local hU hc (pCore 2 L ⊓ center L) inf_le_left with hb | ht
  · exact hb
  · exact (hncentral (ht ▸ inf_le_right)).elim

private theorem core_centralizer_disjoint_local
    {G : Type*} [Group G] {X : Subgroup G}
    (hU : blockU X = pCore 2 X)
    (hcenter : pCore 2 X ⊓ center X = ⊥) :
    Disjoint ((blockU X).map X.subtype) (centralizer (X : Set G)) := by
  rw [Subgroup.disjoint_def]
  rintro z ⟨u, hu, rfl⟩ hc
  have huc : u ∈ center X := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_iff.mp hc x x.property
  have huone : u = 1 := hcenter.le ⟨hU ▸ hu, huc⟩
  exact congrArg Subtype.val huone

private theorem disjoint_core_conjugates_local
    {G : Type*} [Group G] {X : Subgroup G}
    (hU : blockU X = pCore 2 X)
    (hcenter : pCore 2 X ⊓ center X = ⊥) (a b : G)
    (hcomm : ⁅X.conjBy a, X.conjBy b⁆ = ⊥) :
    Disjoint (((blockU X).map X.subtype).conjBy a)
      (((blockU X).map X.subtype).conjBy b) := by
  have hblockX : (blockU X).map X.subtype ≤ X := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨u, hu, rfl⟩
    exact u.property
  rw [Subgroup.disjoint_def]
  intro z hza hzb
  have hzA : z ∈ X.conjBy a := (Subgroup.map_mono hblockX) hza
  have hcentralAB : X.conjBy a ≤ centralizer (X.conjBy b : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hzcentB : z ∈ centralizer (X.conjBy b : Set G) := hcentralAB hzA
  rcases Subgroup.mem_map.mp hzb with ⟨u, hu, hzu⟩
  rcases Subgroup.mem_map.mp hu with ⟨v, hv, hvu⟩
  have hzu' : b * (v : G) * b⁻¹ = z := by
    rw [← hvu] at hzu
    simpa [MulAut.conj_apply] using hzu
  have hvCore : (v : X) ∈ pCore 2 X := by rw [← hU]; exact hv
  have hvCenter : (v : X) ∈ center X := by
    rw [mem_center_iff]
    intro x
    have hxB : b * (x : G) * b⁻¹ ∈ X.conjBy b := by
      exact Subgroup.mem_map.mpr ⟨x, x.property, by simp [MulAut.conj_apply]⟩
    have hzc : Commute z (b * (x : G) * b⁻¹) :=
      (mem_centralizer_iff.mp hzcentB _ hxB).symm
    have hvc : Commute (v : G) (x : G) := by
      apply (Commute.conj_iff b).mp
      rw [hzu']
      exact hzc
    apply Subtype.ext
    exact hvc.eq.symm
  have hvInf : (v : X) ∈ pCore 2 X ⊓ center X := ⟨hvCore, hvCenter⟩
  have hvone : (v : X) = 1 := by simpa [hcenter] using hvInf
  have hzcalc : z = b * (v : G) * b⁻¹ := hzu'.symm
  simpa [hvone] using hzcalc

private theorem commutative_sup_local {G : Type*} [Group G]
    (R B : Subgroup G) [IsMulCommutative R] [IsMulCommutative B]
    (hBR : B ≤ centralizer (R : Set G)) : IsMulCommutative (R ⊔ B : Subgroup G) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le R.le_centralizer hBR)
  · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hBR) B.le_centralizer)

private theorem support_map_local
    {G : Type*} [Group G] (V : Subgroup G) (A : Subgroup G)
    (hAV : A ≤ normalizer (V : Set G)) (S : Subgroup V) (a : A) :
    letI : MulDistribMulAction A V :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
    (S.map (MulDistribMulAction.toMulAut A V a).toMonoidHom).map V.subtype =
      (S.map V.subtype).conjBy (a : G) := by
  let : MulDistribMulAction A V :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
  have hcomp : V.subtype.comp
      (MulDistribMulAction.toMulAut A V a).toMonoidHom =
      (MulAut.conj (a : G)).toMonoidHom.comp V.subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rfl

/-- A cubic actor normalizes a block whenever its distinct conjugates commute. -/
theorem cubic_actor_normalizes_of_conjugates_commute
    {G : Type*} [Group G] [Finite G] {X Y : Subgroup G}
    (hX : IsBlock X) (hY : IsBlock Y)
    (hqX : Nat.card (X ⧸ pCore 2 X) = 3)
    (hqY : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hcomm : ∀ a b : Y, X.conjBy (a : G) ≠ X.conjBy (b : G) →
      ⁅X.conjBy (a : G), X.conjBy (b : G)⁆ = ⊥) :
    Y ≤ normalizer (X : Set G) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcardY : Nat.card Y = 12 := hY.short.card_eq_twelve_of_quotient_three hqY
  obtain ⟨t, ht3⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3 (by
    rw [hcardY]
    norm_num)
  have ht3G : (t : G) ^ 3 = 1 := by
    simpa [ht3] using congrArg Subtype.val (pow_orderOf_eq_one t)
  have ht3G_order : orderOf (t : G) = 3 := by simpa using ht3
  have hcoreNorm : pCoreIn 2 Y ≤ normalizer (X : Set G) := by
    exact (pCoreIn_le_of_subnormal 2 hY.subnormal).trans
      (le_normalizer_of_isSubnormal_isPPerfect X (pCore 2 G)
        hX.subnormal hX.short.twoPerfect pCore_isPGroup le_normalizer_of_normal)
  have htNorm : (t : G) ∈ normalizer (X : Set G) := by
    by_contra htX
    have hmove : X.conjBy (t : G) ≠ X := by
      intro heq
      apply htX
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact heq
    have hneq01 : X.conjBy (1 : G) ≠ X.conjBy (t : G) := by
      simpa [Subgroup.conjBy_one] using hmove.symm
    have hneq02 : X.conjBy (1 : G) ≠ X.conjBy ((t : G) * (t : G)) := by
      intro heq
      have hh := Subgroup.conjBy_inv_mul_cancel X heq
      have hh2 := congrArg (fun H : Subgroup G => H.conjBy (t : G)) hh
      have hpow : (t : G) * ((t : G) * (t : G)) = 1 := by
        simpa [pow_three, mul_assoc] using ht3G
      rw [Subgroup.conjBy_conjBy] at hh2
      simp only [inv_one, one_mul] at hh2
      rw [hpow, Subgroup.conjBy_one] at hh2
      exact hmove hh2.symm
    have hneq12 : X.conjBy (t : G) ≠ X.conjBy ((t : G) * (t : G)) := by
      intro heq
      have hh := Subgroup.conjBy_inv_mul_cancel X heq
      apply hmove
      simpa [mul_assoc] using hh
    have hUcore : pCore 2 X = blockU X :=
      hX.short.core_eq_blockU_of_quotient_three hqX
    have hU : blockU X = pCore 2 X := hUcore.symm
    have hcenter : pCore 2 X ⊓ center X = ⊥ :=
      core_inf_center_bot_local hUcore
        (hX.short.core_card_four_of_quotient_three hqX)
    let U0 : Subgroup G := (blockU X).map X.subtype
    let U1 : Subgroup G := U0.conjBy (t : G)
    let U2 : Subgroup G := U0.conjBy ((t : G) * (t : G))
    let V : Subgroup G := U0 ⊔ U1 ⊔ U2
    have h12 : Disjoint U1 U2 := by
      dsimp [U0, U1, U2]
      exact disjoint_core_conjugates_local hU hcenter (t : G)
        ((t : G) * (t : G)) (hcomm t (t * t) hneq12)
    have hblockX : (blockU X).map X.subtype ≤ X := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨u, hu, rfl⟩
      exact u.property
    have hcent10 : U1 ≤ centralizer (U0 : Set G) := by
      dsimp [U0, U1]
      have hA : map (MulAut.conj (t : G)).toMonoidHom
          ((blockU X).map X.subtype) ≤ X.conjBy (t : G) :=
        Subgroup.map_mono hblockX
      have hC : X.conjBy (t : G) ≤ centralizer (X : Set G) := by
        simpa [Subgroup.conjBy_one] using
          (commutator_eq_bot_iff_le_centralizer.mp (hcomm t 1 (by
            simpa [Subgroup.conjBy_one] using hneq01.symm)))
      exact hA.trans (hC.trans (centralizer_le (show (U0 : Set G) ⊆ (X : Set G) from hblockX)))
    have hcent20 : U2 ≤ centralizer (U0 : Set G) := by
      dsimp [U0, U2]
      have hA : map (MulAut.conj ((t : G) * (t : G))).toMonoidHom
          ((blockU X).map X.subtype) ≤ X.conjBy ((t : G) * (t : G)) :=
        Subgroup.map_mono hblockX
      have hC : X.conjBy ((t : G) * (t : G)) ≤ centralizer (X : Set G) := by
        simpa [Subgroup.conjBy_one] using
          (commutator_eq_bot_iff_le_centralizer.mp (hcomm (t * t) (1 : Y) hneq02.symm))
      exact hA.trans (hC.trans (centralizer_le (show (U0 : Set G) ⊆ (X : Set G) from hblockX)))
    have hcent21 : U2 ≤ centralizer (U1 : Set G) := by
      dsimp [U0, U1, U2]
      have hA : map (MulAut.conj ((t : G) * (t : G))).toMonoidHom
          ((blockU X).map X.subtype) ≤ X.conjBy ((t : G) * (t : G)) :=
        Subgroup.map_mono hblockX
      have hB : map (MulAut.conj (t : G)).toMonoidHom
          ((blockU X).map X.subtype) ≤ X.conjBy (t : G) :=
        Subgroup.map_mono hblockX
      have hC : X.conjBy ((t : G) * (t : G)) ≤
          centralizer (X.conjBy (t : G) : Set G) := by
        exact commutator_eq_bot_iff_le_centralizer.mp (hcomm (t * t) t hneq12.symm)
      exact hA.trans (hC.trans (centralizer_le (show (U1 : Set G) ⊆
        (X.conjBy (t : G) : Set G) from hB)))
    have hjoinC : U1 ⊔ U2 ≤ centralizer (X : Set G) := by
      have hC1 : X.conjBy (t : G) ≤ centralizer (X : Set G) := by
        simpa only [Subgroup.coe_one, Subgroup.conjBy_one] using
          commutator_eq_bot_iff_le_centralizer.mp (hcomm t 1 hneq01.symm)
      have hC2 : X.conjBy ((t : G) * (t : G)) ≤ centralizer (X : Set G) := by
        simpa only [Subgroup.coe_one, Subgroup.coe_mul, Subgroup.conjBy_one] using
          commutator_eq_bot_iff_le_centralizer.mp (hcomm (t * t) 1 hneq02.symm)
      exact sup_le ((Subgroup.map_mono hblockX).trans hC1)
        ((Subgroup.map_mono hblockX).trans hC2)
    have hindependent : Disjoint U0 (U1 ⊔ U2) :=
      (core_centralizer_disjoint_local hU hcenter).mono_right hjoinC
    letI : IsMulCommutative (blockU X) := by
      letI : IsElementaryAbelian 2 (blockU X) := hX.short.elementary
      infer_instance
    letI : IsMulCommutative U0 := Subgroup.map_isMulCommutative (blockU X) X.subtype
    letI : IsMulCommutative U1 := Subgroup.map_isMulCommutative U0
      (MulAut.conj (t : G)).toMonoidHom
    letI : IsMulCommutative U2 := Subgroup.map_isMulCommutative U0
      (MulAut.conj ((t : G) * (t : G))).toMonoidHom
    letI : IsMulCommutative (U0 ⊔ U1 : Subgroup G) :=
      commutative_sup_local (U0 : Subgroup G) (U1 : Subgroup G) hcent10
    letI : IsMulCommutative V := by
      exact commutative_sup_local (U0 ⊔ U1 : Subgroup G) (U2 : Subgroup G)
        (le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hcent20)
          (le_centralizer_iff.mp hcent21)))
    have hVmap : V.map (MulAut.conj (t : G)).toMonoidHom = V := by
      calc
        V.map (MulAut.conj (t : G)).toMonoidHom =
            U0.map (MulAut.conj (t : G)).toMonoidHom ⊔
              U1.map (MulAut.conj (t : G)).toMonoidHom ⊔
              U2.map (MulAut.conj (t : G)).toMonoidHom := by
          change ((U0 ⊔ U1 ⊔ U2 : Subgroup G).map (MulAut.conj (t : G)).toMonoidHom) = _
          rw [Subgroup.map_sup, Subgroup.map_sup]
        _ = U1 ⊔ U2 ⊔ U0 := by
          rw [show U0.map (MulAut.conj (t : G)).toMonoidHom = U1 by rfl]
          rw [show U1.map (MulAut.conj (t : G)).toMonoidHom = U2 by
            change (U0.conjBy (t : G)).conjBy (t : G) = _
            rw [Subgroup.conjBy_conjBy]]
          rw [show U2.map (MulAut.conj (t : G)).toMonoidHom = U0 by
            change (U0.conjBy ((t : G) * (t : G))).conjBy (t : G) = _
            rw [Subgroup.conjBy_conjBy]
            rw [show (t : G) * ((t : G) * (t : G)) = 1 by
              simpa [pow_three, mul_assoc] using ht3G, Subgroup.conjBy_one]]
        _ = V := by
          change U1 ⊔ U2 ⊔ U0 = U0 ⊔ U1 ⊔ U2
          ac_rfl
    let A : Subgroup G := zpowers (t : G)
    have hAV : A ≤ normalizer (V : Set G) := by
      apply zpowers_le.mpr
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hVmap
    letI : MulDistribMulAction A V :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer A V hAV
    letI : MulDistribMulAction (⊤ : Subgroup A) V :=
      { smul := fun a v => (a : A) • v
        one_smul := by intro; simp
        mul_smul := by intro a b v; simp [mul_smul]
        smul_one := by intro; simp
        smul_mul := by intro a x y; simp [smul_mul'] }
    let U : Subgroup V := U0.subgroupOf V
    let W : Subgroup V := U.map (MulDistribMulAction.toMulAut A V ⟨t, mem_zpowers (t : G)⟩).toMonoidHom
    let T : Subgroup V := W.map (MulDistribMulAction.toMulAut A V ⟨t, mem_zpowers (t : G)⟩).toMonoidHom
    have hU0V : U0 ≤ V := le_sup_left.trans le_sup_left
    have hU0map : U.map V.subtype = U0 := Subgroup.map_subgroupOf_eq_of_le hU0V
    have hWmap : W.map V.subtype = U1 := by
      rw [support_map_local V A hAV U ⟨t, mem_zpowers (t : G)⟩, hU0map]
    have hTmap : T.map V.subtype = U2 := by
      rw [support_map_local V A hAV W ⟨t, mem_zpowers (t : G)⟩, hWmap]
      change (U0.conjBy (t : G)).conjBy (t : G) = U0.conjBy ((t : G) * (t : G))
      rw [Subgroup.conjBy_conjBy]
    have hUW : U.map (MulDistribMulAction.toMulAut A V ⟨t, mem_zpowers (t : G)⟩).toMonoidHom = W := rfl
    have hWT : W.map (MulDistribMulAction.toMulAut A V ⟨t, mem_zpowers (t : G)⟩).toMonoidHom = T := rfl
    have hUdisj : Disjoint U (W ⊔ T) := by
      rw [Subgroup.disjoint_def]
      intro z hzU hzWT
      have hzU' : (z : G) ∈ U.map V.subtype :=
        Subgroup.mem_map_of_mem V.subtype hzU
      have hz0 : (z : G) ∈ U0 :=
        (congrArg (fun K : Subgroup G => (z : G) ∈ K) hU0map).mp hzU'
      have hzjoin' : (z : G) ∈ (W ⊔ T).map V.subtype :=
        Subgroup.mem_map_of_mem V.subtype hzWT
      have hm : (W ⊔ T).map V.subtype = U1 ⊔ U2 := by
        rw [Subgroup.map_sup, hWmap, hTmap]
      have hzjoin : (z : G) ∈ U1 ⊔ U2 :=
        (congrArg (fun K : Subgroup G => (z : G) ∈ K) hm).mp hzjoin'
      have hzEq : (z : G) = 1 := Subgroup.disjoint_def.mp hindependent hz0 hzjoin
      exact Subtype.ext hzEq
    have hWdisj : Disjoint W T := by
      rw [Subgroup.disjoint_def]
      intro z hzW hzT
      have hz1' : (z : G) ∈ W.map V.subtype :=
        Subgroup.mem_map_of_mem V.subtype hzW
      have hz2' : (z : G) ∈ T.map V.subtype :=
        Subgroup.mem_map_of_mem V.subtype hzT
      have hz1 : (z : G) ∈ U1 :=
        (congrArg (fun K : Subgroup G => (z : G) ∈ K) hWmap).mp hz1'
      have hz2 : (z : G) ∈ U2 :=
        (congrArg (fun K : Subgroup G => (z : G) ∈ K) hTmap).mp hz2'
      exact Subtype.ext (Subgroup.disjoint_def.mp h12 hz1 hz2)
    have hthree := commutatorAction_card_ge_mul_of_three_supports
      (⊤ : Subgroup A) ⟨(t : G), mem_zpowers (t : G)⟩ (by trivial)
      U W T hUW hWT hUdisj hWdisj
    have hcardU0 : Nat.card U0 = 4 := by
      rw [show U0 = (blockU X).map X.subtype by rfl,
        Subgroup.card_map_of_injective X.subtype_injective]
      rw [← hUcore]
      exact hX.short.core_card_four_of_quotient_three hqX
    have hcardU : Nat.card U = 4 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hU0V).toEquiv]
      exact hcardU0
    have hcardW' : Nat.card W = Nat.card U := by
      dsimp [W]
      exact Subgroup.card_map_of_injective
        (MulDistribMulAction.toMulAut A V ⟨t, mem_zpowers (t : G)⟩).injective
    have hcardW : Nat.card W = 4 := hcardW'.trans hcardU
    have hcardAct : 16 ≤ Nat.card (commutatorAction (A := (⊤ : Subgroup A)) (G := V)) := by
      have := hthree
      rw [hcardU, hcardW] at this
      norm_num at this ⊢
      exact this
    have hU0M : U0 ≤ pCore 2 G := by
      dsimp [U0]
      rw [← hX.ambient_core_commutator]
      exact commutator_le_left _ _
    have hcoreconj (a : G) : (pCore 2 G).conjBy a = pCore 2 G := by
      have ha : a ∈ normalizer (pCore 2 G : Set G) :=
        le_normalizer_of_normal (show a ∈ (⊤ : Subgroup G) from trivial)
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
    have hU1M : U1 ≤ pCore 2 G := by
      dsimp [U1]
      exact (Subgroup.map_mono hU0M).trans (le_of_eq (hcoreconj _))
    have hU2M : U2 ≤ pCore 2 G := by
      dsimp [U2]
      exact (Subgroup.map_mono hU0M).trans (le_of_eq (hcoreconj _))
    have hVA : V ≤ pCore 2 G := by
      exact sup_le (sup_le hU0M hU1M) hU2M
    have hAY : A ≤ Y := zpowers_le.mpr t.property
    have himage : (commutatorAction (A := (⊤ : Subgroup A)) (G := V)).map V.subtype ≤
        ⁅(pCore 2 G : Subgroup G), (Y : Subgroup G)⁆ := by
      rw [Subgroup.map_le_iff_le_comap]
      rw [commutatorAction_eq_closure]
      apply (Subgroup.closure_le _).mpr
      rintro x ⟨a, v, rfl⟩
      have hv : (v : G) ∈ pCore 2 G := hVA v.property
      have ha : (a : G) ∈ Y := hAY a.1.property
      have hvInv : (v : G)⁻¹ ∈ pCore 2 G := (pCore 2 G).inv_mem hv
      have hc := commutator_mem_commutator hvInv ha
      change ((v⁻¹ * a • v : V) : G) ∈ ⁅(pCore 2 G : Subgroup G), (Y : Subgroup G)⁆
      have hact : ((a • v : V) : G) = (a : G) * (v : G) * (a : G)⁻¹ := by rfl
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hact]
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer,
        MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv,
        MulAut.conj_apply, commutatorElement_def, mul_assoc] using hc
    have hcardMapAct : Nat.card (commutatorAction (A := (⊤ : Subgroup A)) (G := V)) =
        Nat.card ((commutatorAction (A := (⊤ : Subgroup A)) (G := V)).map V.subtype) :=
      (Subgroup.card_map_of_injective V.subtype_injective).symm
    have hcardAmbient : Nat.card (⁅pCore 2 G, Y⁆ : Subgroup G) = 4 := by
      rw [hY.ambient_core_commutator, Subgroup.card_map_of_injective Y.subtype_injective,
        ← hY.short.core_eq_blockU_of_quotient_three hqY]
      exact hY.short.core_card_four_of_quotient_three hqY
    have hbound : 16 ≤ Nat.card (⁅pCore 2 G, Y⁆ : Subgroup G) := by
      rw [hcardMapAct] at hcardAct
      exact hcardAct.trans (Subgroup.card_le_of_le himage)
    rw [hcardAmbient] at hbound
    omega
  have hgen := pCoreIn_sup_zpowers_eq_of_quotient_card_three hqY t.property ht3G_order
  rw [← hgen]
  exact sup_le hcoreNorm (zpowers_le.mpr htNorm)

end CFSG.Quasithin.ChapterC.BlockCommutation
