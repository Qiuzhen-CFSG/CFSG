module

public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalOuterCosetGeometry
public import Stellmacher.Recognition.LargeTerminalReeCoreTable
public import Stellmacher.Recognition.LargeTerminalReeCoreModelOrientationFinal
public import Theory.SpecificGroups.ReeTwo.CoreFaithfulness
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Theory.GroupAction.CoprimeFixedConjugacy

/-!
# The two core classes of a cyclic five-fixed root

Write Q for the second core, R for the first residual, D for its derived
subgroup, and W = C_Q(D). At the upper endpoint W is abelian of order 64.
A five-fixed root t outside R has core centralizer W and sixteen core
conjugates. When the five-fixed subgroup is cyclic, coprime action separates
the classes of t and its inverse. Those two classes exhaust W minus D.
Consequently the requested preservation of the root's core class by the
second local group is equivalent to excluding an element of that local group
which inverts t. The actual terminal frame supplies a marked identification
with the Ree core. The neighboring-parabolic geometry excludes inversion
under that identification, completing class preservation for the fixed root
and all its powers. No core identification or action premise remains in
`five_fixed_core_conjugacy`.

Sources: Stellmacher (10.1), the core centralizer supplement; Thompson VI,
printed pp.629–630, for the local configuration and the implicit identification
calculation; Shinoda (1975), (2.3), pp.81–82 for the core table. The class
separation uses the coprime transporter argument; the geometric exclusion is
proved in `LargeTerminalReeCoreModelOrientationFinal`.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine SectionTen Subgroup
universe u

public theorem LargeTerminalContext.derived_centralizer_isMulCommutative
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    IsMulCommutative (twoCoreIn ctx.second ⊓
      centralizer (DerivedAmbient ctx.firstResidual : Set G) : Subgroup G) := by
  let D := DerivedAmbient ctx.firstResidual
  let W := twoCoreIn ctx.second ⊓ centralizer (D : Set G)
  have hDW : D ≤ W := by
    rw [show D = W ⊓ ctx.firstResidual from ctx.derived_centralizer_supplement.2.symm]
    exact inf_le_left
  let N := D.subgroupOf W
  have hNC : N ≤ center W := by
    intro d hd
    apply mem_center_iff.mpr
    intro w
    apply Subtype.ext
    exact (mem_centralizer_iff.mp w.property.2 d hd).symm
  let _ : N.Normal := ⟨by
    intro n hn w
    have hcomm := mem_center_iff.mp (hNC hn) w
    simpa only [hcomm, mul_inv_cancel_right] using hn⟩
  have hcard : Nat.card (W ⧸ N) = 2 := by
    have hc := N.index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hDW).toEquiv] at hc
    have hD : Nat.card D = 32 :=
      (card_map_of_injective ctx.firstResidual.subtype_injective).trans
        ctx.first_residual_structure.2.2.2.2.1
    have hW : Nat.card W = 64 := (ctx.derived_centralizer_card_and_index hS).1
    rw [hD, hW, index_eq_card] at hc
    omega
  let _ : IsCyclic (W ⧸ N) := isCyclic_of_prime_card hcard
  exact (QuotientGroup.mk' N).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [QuotientGroup.ker_mk']; exact hNC)

public theorem LargeTerminalContext.five_fixed_core_centralizer_eq_derived_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G)) (htR : t ∉ ctx.firstResidual) :
    twoCoreIn ctx.second ⊓ centralizer ({t} : Set G) =
      twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G) := by
  let W := twoCoreIn ctx.second ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let _ : IsMulCommutative W := ctx.derived_centralizer_isMulCommutative hS
  have htW : t ∈ W := ⟨htQ, ctx.five_fixed_centralizes_derived A hA hAN hfixed t htQ htA⟩
  apply (eq_of_le_of_card_ge (show W ≤ twoCoreIn ctx.second ⊓ centralizer ({t} : Set G) from ?_) ?_).symm
  · intro w hw
    refine ⟨hw.1, mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg (fun x : W => (x : G)) (mul_comm' (⟨w, hw⟩ : W) ⟨t, htW⟩)
  · have hW : Nat.card W = 64 := (ctx.derived_centralizer_card_and_index hS).1
    rw [hW]
    exact ctx.fixed_core_centralizer_card_le_sixtyfour hS A hA hAN hfixed t htQ htA htR

/-- A fixed root outside the residual has sixteen core conjugates. -/
public theorem LargeTerminalContext.five_fixed_core_conjugacy_class_card
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : twoCoreIn ctx.second) (htA : (t : G) ∈ centralizer (A : Set G))
    (htR : (t : G) ∉ ctx.firstResidual) :
    Nat.card (ConjClasses.mk t).carrier = 16 := by
  let Q := twoCoreIn ctx.second
  have hC : (centralizer ({t} : Set Q)).map Q.subtype =
      Q ⊓ centralizer ({(t : G)} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property, mem_centralizer_singleton_iff.mpr ?_⟩
      exact congrArg (fun q : Q => (q : G)) (mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hxQ, hxC⟩
      refine ⟨⟨x, hxQ⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (mem_centralizer_singleton_iff.mp hxC)
  have hc : Nat.card (centralizer ({t} : Set Q)) = 64 := by
    rw [← card_map_of_injective Q.subtype_injective, hC,
      ctx.five_fixed_core_centralizer_eq_derived_centralizer hS A hA hAN hfixed
        t t.property htA htR]
    exact (ctx.derived_centralizer_card_and_index hS).1
  have hQ : Nat.card Q = 1024 := by
    have hQS : Q ≤ (S : Subgroup G) := by
      have hSP : (S : Subgroup G) ≤ ctx.second :=
        ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
      rintro x ⟨q, hq, rfl⟩
      exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
        (S.subtype hSP) hq
    have h := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
  have hh := ConjClasses.nat_card_carrier_mul_card_centralizer t
  rw [hc, hQ] at hh
  omega

/-- Distinct elements of the cyclic five-fixed group do not fuse inside the
second core. This does not assert the analogous statement for the second local
group. -/
public theorem LargeTerminalContext.five_fixed_eq_of_core_isConj
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (x y : twoCoreIn ctx.second)
    (hx : (x : G) ∈ centralizer (A : Set G))
    (hy : (y : G) ∈ centralizer (A : Set G)) (hxy : IsConj x y) : x = y := by
  let Q := twoCoreIn ctx.second
  let F := (centralizer (A : Set G)).subgroupOf Q
  have hPQ : ctx.second ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le ctx.second)).mp
      (twoCoreIn_normal ctx.second)
  let _ := conjMulDistribMulActionOfLeNormalizer A Q (hAP.trans hPQ)
  have fixed_iff (q : Q) : (∀ a : A, a • q = q) ↔
      (q : G) ∈ centralizer (A : Set G) := by
    constructor
    · intro h
      apply mem_centralizer_iff.mpr
      intro a ha
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (h ⟨a, ha⟩))
    · intro h a
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp h a a.property)
  have hQ : ¬ 5 ∣ Nat.card Q := by
    have htwo : IsPGroup 2 Q :=
      (pCore_isPGroup (p := 2) (G := ctx.second)).map ctx.second.subtype
    let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp htwo)
    rw [hn]
    exact fun h => (by decide : ¬ 5 ∣ 2) (Nat.prime_five.dvd_of_dvd_pow h)
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk, he⟩ := Theory.GroupAction.exists_fixed_conjugator_of_prime_not_dvd_card
    (IsPGroup.of_card (p := 5) (n := 1) (by simpa using hA)) hQ
    x y ((fixed_iff x).mpr hx) ((fixed_iff y).mpr hy) hxy
  let _ : IsCyclic F := hcyc
  have hc : k * x = x * k := congrArg (fun q : F => (q : Q))
    (mul_comm' (⟨k, (fixed_iff k).mp hk⟩ : F) ⟨x, hx⟩)
  simpa only [hc, mul_inv_cancel_right] using he

/-- The two generators of a cyclic five-fixed four-group lie in different
core conjugacy classes. -/
public theorem LargeTerminalContext.five_fixed_four_not_core_isConj_inv
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G) (hA : Nat.card A = 5)
    (hAP : A ≤ ctx.second)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (t : twoCoreIn ctx.second) (ht : orderOf (t : G) = 4)
    (htA : (t : G) ∈ centralizer (A : Set G)) : ¬ IsConj t t⁻¹ := by
  intro h
  have he := ctx.five_fixed_eq_of_core_isConj A hA hAP hcyc t t⁻¹ htA
    ((centralizer (A : Set G)).inv_mem htA) h
  have hp : (t : G) ^ 2 = 1 := by
    have hv := congrArg (fun q : twoCoreIn ctx.second => (q : G)) he
    calc
      (t : G) ^ 2 = (t : G) * t := pow_two _
      _ = (t : G)⁻¹ * t := congrArg (fun x : G => x * (t : G)) hv
      _ = 1 := inv_mul_cancel _
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [ht] at hd
  norm_num at hd

/-- The two core classes of a fixed root and its inverse exhaust the derived
centralizer outside the elementary derived subgroup. The remaining geometric
question is whether the second local group interchanges these two classes. -/
public theorem LargeTerminalContext.derived_centralizer_eq_two_core_classes
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : twoCoreIn ctx.second) (ht : orderOf (t : G) = 4)
    (htA : (t : G) ∈ centralizer (A : Set G)) (htR : (t : G) ∉ ctx.firstResidual) :
    let Q := twoCoreIn ctx.second
    let D := DerivedAmbient ctx.firstResidual
    let W := Q ⊓ centralizer (D : Set G)
    (W.subgroupOf Q : Set Q) \ (D.subgroupOf Q : Set Q) =
      (ConjClasses.mk t).carrier ∪ (ConjClasses.mk t⁻¹).carrier := by
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient ctx.firstResidual
  let W := Q ⊓ centralizer (D : Set G)
  let X := (W.subgroupOf Q : Set Q) \ (D.subgroupOf Q : Set Q)
  let U := (ConjClasses.mk t).carrier
  let V := (ConjClasses.mk t⁻¹).carrier
  change X = U ∪ V
  have hDW : D ≤ W := by
    rw [show D = W ⊓ ctx.firstResidual from ctx.derived_centralizer_supplement.2.symm]
    exact inf_le_left
  have hDQ : D ≤ Q := hDW.trans inf_le_left
  have hWQ : W ≤ Q := inf_le_left
  have hWcard : (W.subgroupOf Q : Set Q).ncard = 64 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (W.subgroupOf Q) = 64
    rw [Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv]
    exact (ctx.derived_centralizer_card_and_index hS).1
  have hDcard : (D.subgroupOf Q : Set Q).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card (D.subgroupOf Q) = 32
    rw [Nat.card_congr (subgroupOfEquivOfLe hDQ).toEquiv]
    exact (card_map_of_injective ctx.firstResidual.subtype_injective).trans
      ctx.first_residual_structure.2.2.2.2.1
  have hXcard : X.ncard = 32 := by
    rw [Set.ncard_sdiff (show (D.subgroupOf Q : Set Q) ⊆ W.subgroupOf Q from
      fun _ h => hDW h), hWcard, hDcard]
  have htinvR : ((t⁻¹ : Q) : G) ∉ ctx.firstResidual := by
    simpa only [coe_inv, inv_mem_iff] using htR
  have htinvA : ((t⁻¹ : Q) : G) ∈ centralizer (A : Set G) :=
    (centralizer (A : Set G)).inv_mem htA
  have hUcard : U.ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact ctx.five_fixed_core_conjugacy_class_card hS A hA hAN hfixed t htA htR
  have hVcard : V.ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact ctx.five_fixed_core_conjugacy_class_card hS A hA hAN hfixed t⁻¹ htinvA htinvR
  have hdisj : Disjoint U V := by
    apply Set.disjoint_left.mpr
    intro x hxU hxV
    have hu : IsConj t x := hxU
    have hv : IsConj t⁻¹ x := hxV
    exact ctx.five_fixed_four_not_core_isConj_inv A hA hAP hcyc t ht htA
      (hu.trans hv.symm)
  have hsubset (v : Q) (hvA : (v : G) ∈ centralizer (A : Set G))
      (hvR : (v : G) ∉ ctx.firstResidual) : (ConjClasses.mk v).carrier ⊆ X := by
    intro x hx
    have hc : IsConj v x := hx
    obtain ⟨q, rfl⟩ := isConj_iff.mp hc
    have hqP : (q : G) ∈ ctx.second := twoCoreIn_le _ q.property
    have hvW : (v : G) ∈ W :=
      ⟨v.property, ctx.five_fixed_centralizes_derived A hA hAN hfixed v v.property hvA⟩
    refine ⟨?_, ?_⟩
    · exact ((ctx.derived_centralizer_normalizer_local_data hS).2.1 hqP (v : G)).mp hvW
    · intro hd
      exact hvR ((ctx.second_le_residual_normalizer hqP (v : G)).mpr
        ((map_subtype_le _ : D ≤ ctx.firstResidual) hd))
  apply (Set.eq_of_subset_of_ncard_le (Set.union_subset (hsubset t htA htR)
    (hsubset t⁻¹ htinvA htinvR)) ?_).symm
  rw [hXcard, Set.ncard_union_eq hdisj, hUcard, hVcard]

/-- For a cyclic five-fixed root, the requested core fusion control is exactly
the geometric assertion that no element of the second local group inverts it.
This equivalence leaves that assertion as an explicit obligation. -/
public theorem LargeTerminalContext.five_fixed_four_core_conjugacy_iff_no_local_inversion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : twoCoreIn ctx.second) (ht : orderOf (t : G) = 4)
    (htA : (t : G) ∈ centralizer (A : Set G)) (htR : (t : G) ∉ ctx.firstResidual) :
    (∀ b ∈ ctx.second, ∃ q ∈ twoCoreIn ctx.second,
      b * (t : G) * b⁻¹ = q * (t : G) * q⁻¹) ↔
    (∀ b ∈ ctx.second, b * (t : G) * b⁻¹ ≠ (t : G)⁻¹) := by
  let Q := twoCoreIn ctx.second
  let D := DerivedAmbient ctx.firstResidual
  let W := Q ⊓ centralizer (D : Set G)
  have hnoQ := ctx.five_fixed_four_not_core_isConj_inv A hA hAP hcyc t ht htA
  constructor
  · intro hf b hb hi
    obtain ⟨q, hq, he⟩ := hf b hb
    apply hnoQ
    exact isConj_iff.mpr ⟨⟨q, hq⟩, Subtype.ext (he.symm.trans hi)⟩
  · intro hn b hb
    have htW : (t : G) ∈ W :=
      ⟨t.property, ctx.five_fixed_centralizes_derived A hA hAN hfixed t t.property htA⟩
    have hyW : b * (t : G) * b⁻¹ ∈ W :=
      ((ctx.derived_centralizer_normalizer_local_data hS).2.1 hb (t : G)).mp htW
    let y : Q := ⟨b * (t : G) * b⁻¹, hyW.1⟩
    have hyD : (y : G) ∉ D := by
      intro hd
      exact htR ((ctx.second_le_residual_normalizer hb (t : G)).mpr
        ((map_subtype_le _ : D ≤ ctx.firstResidual) hd))
    have hmem : y ∈ (W.subgroupOf Q : Set Q) \ (D.subgroupOf Q : Set Q) :=
      ⟨hyW, hyD⟩
    rw [ctx.derived_centralizer_eq_two_core_classes hS A hA hAP hAN hcyc hfixed
      t ht htA htR] at hmem
    rcases hmem with hy | hy
    · have hc : IsConj t y := hy
      obtain ⟨q, hq⟩ := isConj_iff.mp hc
      exact ⟨q, q.property, (congrArg (fun q : Q => (q : G)) hq).symm⟩
    · have hc : IsConj t⁻¹ y := hy
      obtain ⟨q, hq⟩ := isConj_iff.mp hc
      have he : (q : G) * (t : G)⁻¹ * (q : G)⁻¹ = b * (t : G) * b⁻¹ :=
        congrArg (fun q : Q => (q : G)) hq
      have hqb : (q : G)⁻¹ * b ∈ ctx.second :=
        ctx.second.mul_mem (ctx.second.inv_mem (twoCoreIn_le _ q.property)) hb
      exfalso
      apply hn _ hqb
      calc
        ((q : G)⁻¹ * b) * (t : G) * ((q : G)⁻¹ * b)⁻¹ =
            (q : G)⁻¹ * (b * (t : G) * b⁻¹) * q := by group
        _ = (t : G)⁻¹ := by rw [← he]; group

/-- The second local group preserves the core conjugacy class of every element
of the cyclic five-fixed subgroup. The terminal geometry, through the marked
Ree core and its neighboring parabolic, excludes inversion of a generator. -/
public theorem LargeTerminalContext.five_fixed_core_conjugacy
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G)) :
    ∀ b ∈ ctx.second, ∃ q ∈ twoCoreIn ctx.second,
      b * t * b⁻¹ = q * t * q⁻¹ := by
  let Q := twoCoreIn ctx.second
  obtain ⟨z, hz, hzgen, hlo, hhi, _⟩ := ctx.involution_centralizer_core
  have hzR : z ∈ ctx.firstResidual := by
    apply (show CenterAmbient ctx.firstResidual ≤ ctx.firstResidual from map_subtype_le _)
    rw [ctx.first_residual_center_eq_omegaOneCenter, ← hzgen]
    exact mem_zpowers z
  let zQ : Q := ⟨z, hhi (hlo hzR)⟩
  obtain ⟨v, a, hvA, hvsq, hvgen, hframe⟩ :=
    ctx.exists_ree_frame_of_cyclic hS A hA hAP hAN hcard hcyc hfixed zQ hz hzgen
  have hFcard : Nat.card (Q ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
    rw [← inf_comm (centralizer (A : Set G)) Q, ← subgroupOf_map_subtype,
      card_map_of_injective Q.subtype_injective]
    exact hcard
  have hv4 : orderOf (v : G) = 4 := by
    rw [← Nat.card_zpowers, hvgen]
    exact hFcard
  have hvR : (v : G) ∉ ctx.firstResidual := by
    intro hvR
    let vc : center ctx.firstResidual := ⟨⟨v, hvR⟩, hfixed hvA⟩
    have ho : orderOf vc = 4 := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
      exact hv4
    have hd := orderOf_dvd_natCard vc
    rw [ho, ctx.first_residual_structure.2.2.2.1] at hd
    norm_num at hd
  have hx := ctx.ree_core_relations_of_frame A hA hAN hfixed
    v zQ hz hzgen hvA hvsq a hframe
  let f : ReeTwo.Core →* Q := ReeTwo.Core.lift hx
  have hfroot (i : ReeTwo.CoreRoot) :
      f (ReeTwo.Core.root i) = ReeTwo.frameRoots a v zQ i :=
    ReeTwo.Core.lift_root hx i
  have hfinj : Function.Injective f := ReeTwo.Core.hom_injective_of_last_root f (by
    rw [hfroot]
    change zQ ≠ 1
    intro he
    have heG : z = 1 := congrArg (fun q : Q => (q : G)) he
    rw [heG, orderOf_one] at hz
    contradiction)
  have hQS : Q ≤ (S : Subgroup G) := by
    have hSP : (S : Subgroup G) ≤ ctx.second :=
      ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have h := ctx.local_character_core_card hS
    rwa [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
  let e : ReeTwo.Core ≃* Q := MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, ReeTwo.Core.card.trans hQcard.symm⟩)
  have hev : e.symm v = ReeTwo.Core.root 2 := by
    apply e.injective
    exact (e.apply_symm_apply v).trans (hfroot 2).symm
  have hez : e.symm zQ = ReeTwo.Core.root 9 := by
    apply e.injective
    exact (e.apply_symm_apply zQ).trans (hfroot 9).symm
  have hno := ctx.five_fixed_four_no_local_inversion hS A hA hAP hAN hcard hcyc
    hfixed v zQ hv4 hvsq hz hzgen hvgen e.symm hev hez
  have hfusion := (ctx.five_fixed_four_core_conjugacy_iff_no_local_inversion
    hS A hA hAP hAN hcyc hfixed v hv4 hvA hvR).mpr hno
  have ht : t ∈ zpowers (v : G) := hvgen.symm ▸ ⟨htQ, htA⟩
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ht
  intro b hb
  obtain ⟨q, hq, he⟩ := hfusion b hb
  refine ⟨q, hq, ?_⟩
  change (MulAut.conj b) ((v : G) ^ n) = (MulAut.conj q) ((v : G) ^ n)
  rw [map_zpow, map_zpow]
  exact congrArg (fun x : G => x ^ n) he

end Stellmacher.Recognition

