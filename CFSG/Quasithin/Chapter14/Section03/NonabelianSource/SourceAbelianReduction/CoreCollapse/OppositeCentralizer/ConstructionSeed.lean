module

public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer.Local
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.ParabolicResidual
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementCyclicSpan
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.SupplementFusion

/-!
# Constructing the marked three-factor involution

The completed cyclic/TI and fusion results supply the literal conjugate span
on the original Sylow subgroup. Choose a generator d of D and a cubic actor
a in L with C_R(a)=1. Its action on the elementary seed gives the relation
among the three squares, so w=d*d^a*d^(a²) has square one.

For nonidentity, use the original block K=L O²(N_H(A)). The identities
N_G(K)=KD and K intersect D=Z put d outside K with d² in K. All three
factors have the same image in N_G(K)/K, so w is outside K. This avoids a
separate coordinate calculation for nonidentity. The actor a centralizes w;
its fixed-point-free action on V puts z in the actual C_G(w)' image.

This proves the construction and commutator premises used later in 14.3.22.
The full local geometry, nonfusion and centralizer recognition remain to be
proved by qt-e-14322-core-collapse.
Source: Aschbacher--Smith 14.3.22, printed pp.998--999.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G}

theorem CyclicTIInput.exists_generator_square [Finite G] {F : InvariantFlag T V 2}
    {L : Subgroup G} (hc : CyclicTIInput F L) :
    ∃ d ∈ supplement F, zpowers d = supplement F ∧ F.Vi 1 = zpowers (d ^ 2) := by
  let := hc.cyclic
  obtain ⟨d, hd⟩ := (supplement F).isCyclic_iff_exists_zpowers_eq_top.mp hc.cyclic
  have hdD : d ∈ supplement F := hd ▸ mem_zpowers d
  have hdo : orderOf d = 4 := by rw [← Nat.card_zpowers, hd, hc.card]
  have hd2 : orderOf (d ^ 2) = 2 := by rw [orderOf_pow, hdo]; decide
  have hzcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show F.Vi 1 ≠ ⊥ by
    intro he; simp [he] at hzcard)
  have hgen : F.Vi 1 = zpowers (z : G) := by
    have hh := congrArg (map (F.Vi 1).subtype) (zpowers_eq_top_of_prime_card hzcard hz)
    simpa only [MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, range_subtype,
      Subgroup.subtype_apply] using hh.symm
  have hzo : orderOf (z : G) = 2 := by rw [← Nat.card_zpowers, ← hgen, hzcard]
  have he : (z : G) = d ^ 2 := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (show orderOf (⟨z, hc.strict.le z.property⟩ : supplement F) = 2 from
        (Subgroup.orderOf_coe _).symm.trans hzo)
      (show orderOf (⟨d ^ 2, (supplement F).pow_mem hdD 2⟩ : supplement F) = 2 from
        (Subgroup.orderOf_coe _).symm.trans hd2))
  exact ⟨d, hdD, hd, he ▸ hgen⟩

theorem CyclicTIInput.conjugate_le_sylow {F : InvariantFlag T V 2}
    {L : Subgroup G} (hc : CyclicTIInput F L) {a : G} (ha : a ∈ L) :
    conjugate (supplement F) a ≤ (T : Subgroup G) := by
  have hm : conjugate (supplement F) a ∈
      {A : Subgroup G | ∃ b ∈ L, conjugate (supplement F) b = A} := ⟨a, ha, rfl⟩
  rw [← hc.conjugates] at hm
  obtain ⟨b, hb, hT⟩ := hm
  exact hb ▸ hT

theorem CyclicTIInput.supplement_le_sylow {F : InvariantFlag T V 2}
    {L : Subgroup G} (hc : CyclicTIInput F L) : supplement F ≤ (T : Subgroup G) := by
  have hh := hc.conjugate_le_sylow L.one_mem
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  simpa only [conjugate, inv_one, hid, map_id] using hh

private theorem cubic_square_relation (F : InvariantFlag T V 2) (L : Subgroup G)
    [IsElementaryAbelian 2 V] (hVN : L ≤ normalizer (V : Set G))
    (hVR : V ≤ (F.I₂ L).pCoreIn 2) (z a : G) (hz : z ∈ V) (ha : a ∈ L)
    (ha3 : a ^ 3 = 1) (hfree : (F.I₂ L).pCoreIn 2 ⊓ centralizer ({a} : Set G) = ⊥) :
    z * (MulAut.conj a⁻¹) z * (MulAut.conj (a ^ 2)⁻¹) z = 1 := by
  let f : G ≃* G := MulAut.conj a⁻¹
  have hfV {x : G} (hx : x ∈ V) : f x ∈ V :=
    (mem_normalizer_iff.mp (hVN (L.inv_mem ha)) x).mp hx
  have hf2 (x : G) : f (f x) = (MulAut.conj (a ^ 2)⁻¹) x := by
    simp only [f, MulAut.conj_apply, pow_succ, pow_zero, mul_inv_rev, inv_inv]
    group
  have hf3 (x : G) : f (f (f x)) = x := by
    have hh : f (f (f x)) = (a ^ 3)⁻¹ * x * a ^ 3 := by
      simp only [f, MulAut.conj_apply, pow_succ, pow_zero, mul_inv_rev, inv_inv]
      group
    rw [hh, ha3]
    simp
  let b := z * f z * f (f z)
  have hbV : b ∈ V := V.mul_mem (V.mul_mem hz (hfV hz)) (hfV (hfV hz))
  have hc (x y : G) (hx : x ∈ V) (hy : y ∈ V) : Commute x y :=
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hfb : f b = b := by
    dsimp only [b]
    rw [map_mul, map_mul, hf3, (hc _ _ (V.mul_mem (hfV hz) (hfV (hfV hz))) hz).eq,
      mul_assoc]
  have hbC : b ∈ centralizer ({a} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    simp only [f, MulAut.conj_apply, inv_inv] at hfb
    have hh := congrArg (fun x : G => a * x) hfb
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
  have hb1 : b = 1 := mem_bot.mp (hfree ▸ ⟨hVR hbV, hbC⟩)
  simpa only [b, hf2] using hb1

/-- The constructed cyclic generator and cubic actor, before the block-coset
argument proves that their triple product is nonidentity. -/
structure CubicTriple (F : InvariantFlag T V 2) (L : Subgroup G)
    (z d a : G) : Prop where
  point : F.Vi 1 = zpowers z
  generator : zpowers d = supplement F
  square : d ^ 2 = z
  actor_mem : a ∈ L
  actor_order : orderOf a = 3
  seed_le_core : V ≤ (F.I₂ L).pCoreIn 2
  actor_fixed : (F.I₂ L).pCoreIn 2 ⊓ centralizer ({a} : Set G) = ⊥
  squares : z * (MulAut.conj a⁻¹) z * (MulAut.conj (a ^ 2)⁻¹) z = 1

/-- The actual product, using the right-conjugation convention of the source. -/
@[expose] def tripleProduct (d a : G) : G :=
  d * (MulAut.conj a⁻¹) d * (MulAut.conj (a ^ 2)⁻¹) d

/-- The cubic data discharge the square and Sylow premises of the product
calculation. Only the genuine nonidentity calculation remains explicit. -/
theorem CubicTriple.involution_of_ne_one {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) (hne : tripleProduct d a ≠ 1) :
    tripleProduct d a ∈ (T : Subgroup G) ∧ orderOf (tripleProduct d a) = 2 := by
  apply triple_product_involution F hc.abelian d a (s.generator ▸ mem_zpowers d)
    hc.supplement_le_sylow (hc.conjugate_le_sylow s.actor_mem)
    (hc.conjugate_le_sylow (L.pow_mem s.actor_mem 2))
  · simpa only [s.square] using s.squares
  · exact hne

/-- Without the marked nonidentity calculation, the source product is still
in the supplied Sylow subgroup and has square one. -/
theorem CubicTriple.product_mem_sylow_and_square {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) :
    tripleProduct d a ∈ (T : Subgroup G) ∧ (tripleProduct d a) ^ 2 = 1 := by
  by_cases he : tripleProduct d a = 1
  · simp only [he, one_pow, and_true]
    exact (T : Subgroup G).one_mem
  · obtain ⟨hT, ho⟩ := s.involution_of_ne_one hc he
    exact ⟨hT, ho ▸ pow_orderOf_eq_one (tripleProduct d a)⟩

/-- Each of the three literal factors lies in the original conjugate span. -/
theorem CubicTriple.factors_mem_span {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) :
    d ∈ span F ∧ (MulAut.conj a⁻¹) d ∈ span F ∧
      (MulAut.conj (a ^ 2)⁻¹) d ∈ span F := by
  have hd : d ∈ supplement F := s.generator ▸ mem_zpowers d
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x; simp
  have h0 := map_conj_le_conjugateSubgroupClosure (supplement F)
    (P := (T : Subgroup G)) (1 : G)
    (by simpa only [hid, map_id] using hc.supplement_le_sylow)
  refine ⟨h0 (by simpa only [hid, map_id] using hd), ?_, ?_⟩
  · exact map_conj_le_conjugateSubgroupClosure (supplement F) a⁻¹
      (hc.conjugate_le_sylow s.actor_mem) (mem_map_of_mem _ hd)
  · exact map_conj_le_conjugateSubgroupClosure (supplement F) (a ^ 2)⁻¹
      (hc.conjugate_le_sylow (L.pow_mem s.actor_mem 2)) (mem_map_of_mem _ hd)

/-- The opposite product belongs to X itself, not just to T. -/
theorem CubicTriple.product_mem_span {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) : tripleProduct d a ∈ span F := by
  obtain ⟨h0, h1, h2⟩ := s.factors_mem_span hc
  exact (span F).mul_mem ((span F).mul_mem h0 h1) h2

/-- The cubic actor cyclically permutes the three commuting factors and
therefore centralizes their product. -/
theorem CubicTriple.actor_centralizes_product {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) : a ∈ centralizer ({tripleProduct d a} : Set G) := by
  let := hc.abelian
  let f : G ≃* G := MulAut.conj a⁻¹
  have hf2 (x : G) : f (f x) = (MulAut.conj (a ^ 2)⁻¹) x := by
    simp only [f, MulAut.conj_apply, pow_succ, pow_zero, mul_inv_rev, inv_inv]
    group
  have ha3 : a ^ 3 = 1 := by simpa only [s.actor_order] using pow_orderOf_eq_one a
  have hf3 (x : G) : f (f (f x)) = x := by
    have hh : f (f (f x)) = (a ^ 3)⁻¹ * x * a ^ 3 := by
      simp only [f, MulAut.conj_apply, pow_succ, pow_zero, mul_inv_rev, inv_inv]
      group
    rw [hh, ha3]
    simp
  obtain ⟨h0, h1, h2⟩ := s.factors_mem_span hc
  have hcomm : Commute (f d * f (f d)) d := by
    apply congrArg Subtype.val (mul_comm'
      (⟨f d * f (f d), (span F).mul_mem h1 (by simpa only [hf2] using h2)⟩ : span F)
      ⟨d, h0⟩)
  have hw : f (tripleProduct d a) = tripleProduct d a := by
    change f (d * f d * (MulAut.conj (a ^ 2)⁻¹) d) =
      d * f d * (MulAut.conj (a ^ 2)⁻¹) d
    rw [← hf2 d, map_mul, map_mul, hf3, hcomm.eq, ← mul_assoc]
  apply mem_centralizer_singleton_iff.mpr
  simp only [f, MulAut.conj_apply, inv_inv] at hw
  have hh := congrArg (fun x : G => a * x) hw
  symm
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh

/-- The original plane centralizes the opposite product because both lie in X. -/
theorem CubicTriple.plane_centralizes_product {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} (s : CubicTriple F L z d a)
    (hc : CyclicTIInput F L) : V ≤ centralizer ({tripleProduct d a} : Set G) := by
  let := hc.abelian
  intro v hv
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm'
    (⟨v, hc.seed_le hv⟩ : span F) ⟨tripleProduct d a, s.product_mem_span hc⟩)

/-- The cubic actor moves all of V inside the actual opposite centralizer,
putting the marked point in its ambient commutator image. -/
theorem CubicTriple.point_mem_global_commutator [Finite G] {F : InvariantFlag T V 2}
    {L : Subgroup G} {z d a : G} [IsElementaryAbelian 2 V]
    (s : CubicTriple F L z d a) (hc : CyclicTIInput F L)
    (hLN : L ≤ normalizer (V : Set G)) :
    z ∈ (_root_.commutator (centralizer ({tripleProduct d a} : Set G))).map
      (centralizer ({tripleProduct d a} : Set G)).subtype := by
  have hfix : V ⊓ centralizer (zpowers a : Set G) = ⊥ := by
    apply bot_unique
    intro v hv
    exact s.actor_fixed ▸ (show v ∈ (F.I₂ L).pCoreIn 2 ⊓ centralizer ({a} : Set G) from
      ⟨s.seed_le_core hv.1, (centralizer_le (show ({a} : Set G) ⊆ zpowers a from
        Set.singleton_subset_iff.mpr (mem_zpowers a))) hv.2⟩)
  have hcop : Nat.Coprime (Nat.card (zpowers a)) (Nat.card V) :=
    IsPGroup.coprime_card_of_ne 3 2 (by decide) (zpowers a) V
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.actor_order, pow_one]))
      (IsElementaryAbelian.isPGroup 2 V)
  have hmove : ⁅V, zpowers a⁆ = V := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers a)
      (zpowers_le.mpr (hLN s.actor_mem))
      (Group.isSolvable_of_comm fun x y => mul_comm' x y) hcop
    simpa only [hfix, sup_bot_eq] using hh.symm
  have hle := commutator_mono (s.plane_centralizes_product hc)
    (zpowers_le.mpr (s.actor_centralizes_product hc))
  rw [hmove, ← map_subtype_commutator] at hle
  exact hle (F.le_seed 1 (s.point.symm ▸ mem_zpowers z))

/-- The three conjugates stay outside a normalized subgroup whenever their
common coset has order two. This proves nonidentity without coordinates. -/
private theorem tripleProduct_not_mem (K : Subgroup G) (d a : G)
    (hdN : d ∈ normalizer (K : Set G)) (ha : a ∈ K)
    (hd2 : d ^ 2 ∈ K) (hd : d ∉ K) : tripleProduct d a ∉ K := by
  let N := normalizer (K : Set G)
  let q := QuotientGroup.mk' (K.subgroupOf N)
  let d' : N := ⟨d, hdN⟩
  let a' : N := ⟨a, K.le_normalizer ha⟩
  have hqa : q a' = 1 := (QuotientGroup.eq_one_iff _).mpr ha
  have hqd : q d' ≠ 1 := fun hh => hd ((QuotientGroup.eq_one_iff (N := K.subgroupOf N) d').mp hh)
  have hqd2 : (q d') ^ 2 = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hd2
  intro hw
  have hqw : q (d' * (a'⁻¹ * d' * a') * ((a' ^ 2)⁻¹ * d' * a' ^ 2)) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    change d * (a⁻¹ * d * a) * ((a ^ 2)⁻¹ * d * a ^ 2) ∈ K
    simpa only [tripleProduct, MulAut.conj_apply, inv_inv] using hw
  have hh : q d' * q d' * q d' = 1 := by
    simpa only [map_mul, map_inv, map_pow, hqa, one_pow, inv_one, one_mul, mul_one] using hqw
  rw [← pow_two, hqd2, one_mul] at hh
  exact hqd hh

variable [Finite G]

open Recognition
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

open CFSG.Quasithin.ChapterI.Section06To08

omit [Finite G] in
private theorem ambient_family_eq (D P : Subgroup G) :
    {A : Subgroup G | ∃ a : G, conjugate D a = A ∧ A ≤ P} =
      tightConjugateFamily ⊤ D P := by
  ext A
  constructor
  · rintro ⟨a, he, ha⟩
    exact ⟨ha, a⁻¹, mem_top _, he⟩
  · rintro ⟨ha, a, _, he⟩
    exact ⟨a⁻¹, by simpa only [conjugate, conjSubgroup, inv_inv] using he, ha⟩

omit [Finite G] in
private theorem residual_orbit_eq (D L : Subgroup G) :
    {A : Subgroup G | ∃ a ∈ L, conjSubgroup D a = A} =
      {A : Subgroup G | ∃ a ∈ L, conjugate D a = A} := by
  ext A
  constructor
  · rintro ⟨a, ha, he⟩
    exact ⟨a⁻¹, L.inv_mem ha, by simpa only [conjugate, conjSubgroup, inv_inv] using he⟩
  · rintro ⟨a, ha, he⟩
    exact ⟨a⁻¹, L.inv_mem ha, he⟩

/-- Discharge the cyclic/TI construction interface with the completed first
paragraph of the source, converting both conjugation conventions explicitly. -/
theorem source_cyclicTIInput
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < supplement F) :
    CyclicTIInput F (sourceResidual M Mc) := by
  have hc := source_supplement_cyclic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  obtain ⟨hcardD, hTI, hab, hVX, _, _, hweak, hnorm, _⟩ := source_supplement_span
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  obtain ⟨_, hfam, hthree⟩ := source_supplement_fusion_of_cyclic
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper hc
  have hspan : span F = supplementSpan (supplement F) (T : Subgroup G) := by
    rw [span_eq_sSup, ambient_family_eq]
    rfl
  refine ⟨hproper, hc, hcardD, ?_, hspan.symm ▸ hab, hspan.symm ▸ hVX,
    ?_, hspan.symm ▸ hnorm, ?_, ?_⟩
  · intro a
    by_cases hn : a⁻¹ ∈ normalizer (supplement F : Set G)
    · right
      exact mem_normalizer_iff_map_conj_eq.mp hn
    · left
      apply le_antisymm _ bot_le
      intro x hx
      apply mem_bot.mpr
      exact hTI a⁻¹ hn ⟨hx.1, hx.2⟩
  · intro a ha
    rw [hspan] at ha ⊢
    exact hweak a⁻¹ ha
  · rw [ambient_family_eq, hfam]
    exact residual_orbit_eq _ _
  · rw [← residual_orbit_eq, ← hfam]
    exact hthree

/-- Construct a generator and a fixed-point-free cubic actor on the original
parabolic core. Their three squares multiply to one. -/
theorem source_cubic_triple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨d, _, hd, hz⟩ := hc.exists_generator_square
  obtain ⟨_, _, _, a, ha, hao, hfree⟩ :=
    source_parabolic_residual_core_structure_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨A, B, hAR, _, hVA, _⟩ := source_elementary_factors_of_solvable
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  refine ⟨d ^ 2, d, a, hz, hd, rfl, ha, hao, hVA.trans hAR, hfree, ?_⟩
  apply cubic_square_relation F (sourceResidual M Mc) h.L_normalizes_seed
    (hVA.trans hAR) (d ^ 2) a (F.le_seed 1 (hz.symm ▸ mem_zpowers _)) ha
  · simpa only [hao] using pow_orderOf_eq_one a
  · exact hfree

/-- Every source cubic triple remains outside the original parabolic residual.
All three factors have the same nontrivial image modulo the original block. -/
theorem source_triple_outside_residual
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) {z d a : G}
    (s : CubicTriple F (sourceResidual M Mc) z d a) :
    tripleProduct d a ∉ sourceResidual M Mc := by
  obtain ⟨_, A, hAR, hVA, hEA, hAc, hc8, hAN, _⟩ :=
    source_factor_supplement_action_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  let := hEA
  let N := F.H ⊓ normalizer (A : Set G)
  let Y := (pResidual 2 N).map N.subtype
  let K := sourceResidual M Mc ⊔ Y
  have hNK : normalizer (K : Set G) = K ⊔ supplement F :=
    (source_factor_block_normalizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      A hAR hVA hAc hc8 hAN).1
  have hKD : K ⊓ supplement F = F.Vi 1 :=
    (source_factor_block_supplement_index_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
      A hAR hVA hAc hc8 hAN).1
  have hdD : d ∈ supplement F := s.generator ▸ mem_zpowers d
  have hdN : d ∈ normalizer (K : Set G) := hNK ▸ (show d ∈ K ⊔ supplement F from mem_sup_right hdD)
  have hd2 : d ^ 2 ∈ K := by
    have hz : z ∈ F.Vi 1 := s.point.symm ▸ mem_zpowers z
    rw [← hKD] at hz
    rw [s.square]
    exact hz.1
  have hdK : d ∉ K := by
    intro hd
    have hdZ : d ∈ F.Vi 1 := hKD ▸ (show d ∈ K ⊓ supplement F from ⟨hd, hdD⟩)
    have hDZ : supplement F ≤ F.Vi 1 := s.generator ▸ zpowers_le.mpr hdZ
    exact hc.strict.not_ge hDZ
  have hwK := tripleProduct_not_mem K d a hdN (mem_sup_left s.actor_mem) hd2 hdK
  exact fun hw => hwK (mem_sup_left hw)

/-- The actual source triple product is a nonidentity involution in the
original Sylow subgroup. The nontrivial block coset supplies nonidentity. -/
theorem source_triple_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ (T : Subgroup G) ∧ orderOf (tripleProduct d a) = 2 := by
  obtain ⟨z, d, a, s⟩ := source_cubic_triple
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  have hwL := source_triple_outside_residual
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc s
  have hw1 : tripleProduct d a ≠ 1 := fun he => hwL (he ▸ (sourceResidual M Mc).one_mem)
  exact ⟨z, d, a, s, s.involution_of_ne_one hc hw1⟩

/-- The original proper-supplement branch supplies the actual three-factor
involution, with every cyclic/TI and nonidentity premise discharged. -/
theorem source_opposite_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < supplement F) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ (T : Subgroup G) ∧ orderOf (tripleProduct d a) = 2 := by
  exact source_triple_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    (source_cyclicTIInput hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper)

/-- The literal source application constructs the opposite product and puts
the original point in the commutator of its actual global centralizer. The
remaining nonfusion, local-centralizer models and recognition are not assumed. -/
theorem source_opposite_involution_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hself : FactorSelfCentralizing F (sourceResidual M Mc))
    (hproper : F.Vi 1 < supplement F) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ (T : Subgroup G) ∧ orderOf (tripleProduct d a) = 2 ∧
      rankTwoSeed T M ≤ centralizer ({tripleProduct d a} : Set G) ∧
      a ∈ centralizer ({tripleProduct d a} : Set G) ∧
      z ∈ (_root_.commutator (centralizer ({tripleProduct d a} : Set G))).map
        (centralizer ({tripleProduct d a} : Set G)).subtype := by
  have hc := source_cyclicTIInput
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hself hproper
  obtain ⟨z, d, a, s, hwT, hw⟩ := source_triple_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  have h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  exact ⟨z, d, a, s, hwT, hw, s.plane_centralizes_product hc,
    s.actor_centralizes_product hc, s.point_mem_global_commutator hc h.L_normalizes_seed⟩

/-- A literal source application: the constructed product is a two-element
in the original T. The nonidentity and centralizer arguments remain separate. -/
theorem source_triple_square
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (hc : CyclicTIInput F (sourceResidual M Mc)) :
    ∃ z d a : G, CubicTriple F (sourceResidual M Mc) z d a ∧
      tripleProduct d a ∈ (T : Subgroup G) ∧ (tripleProduct d a) ^ 2 = 1 := by
  obtain ⟨z, d, a, s⟩ := source_cubic_triple
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs hc
  exact ⟨z, d, a, s, s.product_mem_sylow_and_square hc⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.CoreCollapse.OppositeCentralizer
