module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionOne.OrderTwoSylowInvolutions
public import Theory.Representation.OrderTwoTransvections
public import FeitThompson.BGsection1.theorem_1_18
public import FeitThompson.BGsection1.PLengthLemmas
public import Theory.GroupAction.CoprimeHall
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# The order-two endpoint in Stellmacher (1.6)

This module proves the base case `|S| = 2` in Stellmacher's Lemma (1.6).
Burnside transfer first supplies the normal odd complement
`W = O_{2'}(G)`.  Faithfulness and `m(S) = 1` make the nonidentity element
of `S` act as a transvection.  The order-two Sylow structure and the finite
transvection-count theorem then show that `G` has exactly three involutions;
consequently `W` is cyclic of order three.

Writing two distinct involutions as transvections, their product has order
three.  The cross-coefficients are therefore both one, so the range of its
difference from the identity is two-dimensional.  This identifies
`[V,W]` as a four-element module on which `S` has two fixed points.  The
restricted action is faithful, hence realizes the six-element group `G` as
`SL₂(2)`.  Finally `[G,G]=W`, and the singleton factor family gives exactly
alternative (1.6)(d), including quadraticity and the fixed-quotient count.

Source: `refs/latex/stellmacher-n-group.tex`, proof of Lemma (1.6), journal
page 17, where the case `|S| = 2` is stated to yield alternative (d).
-/

open scoped BigOperators Pointwise IsMulCommutative commutatorElement

namespace Stellmacher.SectionOne

universe u

private theorem subgroup_card_two_le_center_normalizer
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hScard : Nat.card S = 2) :
    S ≤ centerIn (G := G) (Subgroup.normalizer (S : Set G)) := by
  obtain ⟨t, ht_ne, ht_unique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
  intro s hs
  refine ⟨Subgroup.le_normalizer hs, ?_⟩
  change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  by_cases hs_one : s = 1
  · simp [hs_one]
  have hs_eq_t : (⟨s, hs⟩ : S) = t := ht_unique ⟨s, hs⟩ (by
    intro h
    exact hs_one (congrArg Subtype.val h))
  have hconj_mem : n * s * n⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.mp hn s).mp hs
  have hconj_ne : n * s * n⁻¹ ≠ 1 := by
    intro hconj
    have := congrArg (fun x : G => n⁻¹ * x * n) hconj
    exact hs_one (by simpa [mul_assoc] using this)
  have hconj_eq_t : (⟨n * s * n⁻¹, hconj_mem⟩ : S) = t :=
    ht_unique ⟨n * s * n⁻¹, hconj_mem⟩ (by
      intro h
      exact hconj_ne (congrArg Subtype.val h))
  have hconj_eq : n * s * n⁻¹ = s := by
    exact congrArg Subtype.val (hconj_eq_t.trans hs_eq_t.symm)
  have := congrArg (fun x : G => x * n) hconj_eq
  simpa [mul_assoc] using this

private theorem order_two_hasNormalPComplement
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2) :
    HasNormalPComplement 2 G :=
  hasNormalPComplement_of_sylow_le_center_normalizer
    (G := G) 2 S (subgroup_card_two_le_center_normalizer (S : Subgroup G) hScard)

private theorem sylow_isComplement_pPrimeCore_of_hasNormalPComplement
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hcomp : HasNormalPComplement p G) (S : Sylow p G) :
    (S : Subgroup G).IsComplement' (pPrimeCore p G) := by
  classical
  let N : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hQp : IsPGroup p (G ⧸ N) :=
    isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
      (p := p) (H := G) hcomp
  let Tmap : Sylow p (G ⧸ N) :=
    S.mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have htop_p : IsPGroup p (⊤ : Subgroup (G ⧸ N)) := by
    simpa using hQp.to_subgroup (⊤ : Subgroup (G ⧸ N))
  let Ttop : Sylow p (G ⧸ N) :=
    IsPGroup.toSylow (G := G ⧸ N) (p := p) htop_p (by
      simpa using (Fact.out : Nat.Prime p).not_dvd_one)
  have hTtop_normal : (Ttop : Subgroup (G ⧸ N)).Normal := by
    have hTtop_eq : (Ttop : Subgroup (G ⧸ N)) = ⊤ := by
      dsimp [Ttop]
    rw [hTtop_eq]
    infer_instance
  have : Unique (Sylow p (G ⧸ N)) := Sylow.unique_of_normal Ttop hTtop_normal
  have hTmap_eq : Tmap = Ttop := Subsingleton.elim _ _
  have hSmap_top : (S : Subgroup G).map q = ⊤ := by
    change (Tmap : Subgroup (G ⧸ N)) = ⊤
    simpa [Tmap, Ttop, IsPGroup.toSylow_coe] using
      congrArg (fun P : Sylow p (G ⧸ N) => (P : Subgroup (G ⧸ N))) hTmap_eq
  let qS : (S : Subgroup G) →* (S : Subgroup G).map q :=
    q.subgroupMap (S : Subgroup G)
  have hqS_surj : Function.Surjective qS :=
    MonoidHom.subgroupMap_surjective q (S : Subgroup G)
  have hqS_range_top : qS.range = ⊤ :=
    MonoidHom.range_eq_top.mpr hqS_surj
  have hNcop : Nat.Coprime p (Nat.card N) := by
    simpa [N] using pPrimeCore_coprime_card (p := p) (G := G)
  have hSNcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card N) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact hNcop.pow_left n
  have hSinfN : (S : Subgroup G) ⊓ N = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hSNcop).eq_bot
  have hqS_ker : qS.ker = ⊥ := by
    have hker : qS.ker = N.subgroupOf (S : Subgroup G) := by
      simpa [qS, q, N, QuotientGroup.ker_mk'] using
        (Subgroup.ker_subgroupMap (f := q) (H := (S : Subgroup G)))
    rw [hker, Subgroup.subgroupOf_eq_bot, disjoint_iff]
    simpa [inf_comm] using hSinfN
  let eKer : (S : Subgroup G) ⧸ qS.ker ≃* (S : Subgroup G) :=
    (QuotientGroup.quotientMulEquivOfEq hqS_ker).trans
      QuotientGroup.quotientBot
  let eImage : (S : Subgroup G) ⧸ qS.ker ≃* (S : Subgroup G).map q :=
    (QuotientGroup.quotientKerEquivRange qS).trans
      ((MulEquiv.subgroupCongr hqS_range_top).trans Subgroup.topEquiv)
  let eTop : (S : Subgroup G).map q ≃* G ⧸ N :=
    (MulEquiv.subgroupCongr hSmap_top).trans Subgroup.topEquiv
  let e : G ⧸ N ≃* (S : Subgroup G) :=
    eTop.symm.trans (eImage.symm.trans eKer)
  have hcard_quot : Nat.card (G ⧸ N) = Nat.card (S : Subgroup G) :=
    Nat.card_congr e.toEquiv
  have hcard_mul :
      Nat.card (S : Subgroup G) * Nat.card N = Nat.card G := by
    calc
      Nat.card (S : Subgroup G) * Nat.card N =
          Nat.card (G ⧸ N) * Nat.card N := by rw [hcard_quot]
      _ = Nat.card G :=
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := N)).symm
  simpa [N] using Subgroup.isComplement'_of_coprime hcard_mul hSNcop

private theorem order_two_oddCore_sup_eq_top
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2) :
    oddCore G ⊔ (S : Subgroup G) = ⊤ := by
  have hcomp := sylow_isComplement_pPrimeCore_of_hasNormalPComplement
    (G := G) (p := 2) (order_two_hasNormalPComplement S hScard) S
  simpa only [oddCore, sup_comm] using hcomp.sup_eq_top

private theorem normalClosure_eq_top_of_sup_eq_top_of_le_commutator
    {G : Type u} [Group G] (R L : Subgroup G)
    (hsup : R ⊔ L = ⊤) (hRcomm : R ≤ ⁅R, L⁆) :
    Subgroup.normalClosure (L : Set G) = ⊤ := by
  apply top_unique
  rw [← hsup]
  apply sup_le
  · exact hRcomm.trans (Subgroup.commutator_le.mpr fun r hr l hl => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _
        (Subgroup.normalClosure_normal.conj_mem l
          (Subgroup.subset_normalClosure hl) r)
        (Subgroup.inv_mem _ (Subgroup.subset_normalClosure hl)))
  · exact fun _ hl => Subgroup.subset_normalClosure hl

private theorem order_two_normalClosure_eq_top
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2)
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆) :
    Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤ := by
  apply normalClosure_eq_top_of_sup_eq_top_of_le_commutator
    (oddCore G) (S : Subgroup G) (order_two_oddCore_sup_eq_top S hScard)
  exact hW.le

private theorem card_eq_two_mul_fixedPoints_of_m_eq_one_of_card_two
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (S : Subgroup G)
    (hScard : Nat.card S = 2)
    (hm : m (G := G) (V := V) S = 1) :
    Nat.card V = 2 * Nat.card (FixedPoints.subgroup S V) := by
  have hfixed_ne : (Nat.card (FixedPoints.subgroup S V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup S V)).ne'
  have htwo : (2 : ℚ) ≠ 0 := by norm_num
  unfold m at hm
  rw [hScard] at hm
  have hcast : (Nat.card V : ℚ) =
      (Nat.card (FixedPoints.subgroup S V) : ℚ) * 2 := by
    apply (div_eq_one_iff_eq (mul_ne_zero hfixed_ne htwo)).mp
    exact hm
  exact_mod_cast hcast.trans (mul_comm _ _)

private theorem commutatorAction₂_eq_bot_of_actor_card_two
    {A V : Type u} [Group A] [Group V] [Finite A]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V]
    (hAcard : Nat.card A = 2) :
    commutatorAction₂ A V = ⊥ := by
  have hfirst : commutatorAction A V ≤ FixedPoints.subgroup A V := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := FixedPoints.subgroup A V)).2 ?_
    rintro d ⟨a, v, rfl⟩
    change ∀ b : A, b • (v⁻¹ * a • v) = v⁻¹ * a • v
    intro b
    obtain ⟨t, ht_ne, ht⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hAcard
    have ha : a = 1 ∨ a = t := by
      by_cases ha : a = 1
      · exact Or.inl ha
      · exact Or.inr (ht a ha)
    have hb : b = 1 ∨ b = t := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · exact Or.inr (ht b hb)
    have ht2 : t * t = 1 := by
      by_cases htt_one : t * t = 1
      · exact htt_one
      · have htt := ht (t * t) htt_one
        have ht_one : t = 1 := by
          have heq := congrArg (fun z : A => t⁻¹ * z) htt
          simpa [mul_assoc] using heq
        exact (ht_ne ht_one).elim
    have hv_inv : v⁻¹ = v := by
      apply inv_eq_of_mul_eq_one_left
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 V) v)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · simp
    · simp
    · simp
    · simp only [smul_mul', smul_smul, ht2, one_smul]
      rw [hv_inv]
      exact IsMulCommutative.is_comm.comm _ _
  apply le_antisymm
  · change Subgroup.closure
        {d : V | ∃ a : A, ∃ v : V, v ∈ commutatorAction A V ∧
          d = v⁻¹ * a • v} ≤ ⊥
    refine (Subgroup.closure_le (K := ⊥)).2 ?_
    rintro d ⟨a, v, hv, rfl⟩
    have hav : a • v = v :=
      (FixedPoints.mem_subgroup (M := A) (a := v)).1 (hfirst hv) a
    simp [hav]
  · exact bot_le

private theorem full_fixedQuotient_eq_card_of_m_eq_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (A : Subgroup G)
    (hm : m (G := G) (V := V) A = 1) :
    (Nat.card V : ℚ) / Nat.card (FixedPoints.subgroup A V) = Nat.card A := by
  have hfix : (Nat.card (FixedPoints.subgroup A V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup A V)).ne'
  have hA : (Nat.card A : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := A)).ne'
  unfold m at hm
  apply (div_eq_iff hfix).2
  have hprod : (Nat.card (FixedPoints.subgroup A V) : ℚ) * Nat.card A ≠ 0 :=
    mul_ne_zero hfix hA
  have hnum := (div_eq_one_iff_eq hprod).1 hm
  exact hnum.trans (mul_comm _ _)

private theorem subgroup_card_two_eq_zpowers_of_mem_ne_one
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) (hScard : Nat.card S = 2)
    {t : G} (htS : t ∈ S) (htne : t ≠ 1) :
    S = Subgroup.zpowers t := by
  apply le_antisymm
  · have hcardZ : Nat.card (Subgroup.zpowers t) = 2 := by
      have ht2 : t ^ 2 = 1 := by
        obtain ⟨s, hs_ne, hs_unique⟩ := (Nat.card_eq_two_iff' (1 : S)).mp hScard
        have ht_eq : (⟨t, htS⟩ : S) = s := hs_unique ⟨t, htS⟩ (by
          intro h
          exact htne (congrArg Subtype.val h))
        have ht_sq_mem : t ^ 2 ∈ S := S.pow_mem htS 2
        by_cases ht_sq : t ^ 2 = 1
        · exact ht_sq
        · have hsq_eq : (⟨t ^ 2, ht_sq_mem⟩ : S) = s :=
            hs_unique ⟨t ^ 2, ht_sq_mem⟩ (by
              intro h
              exact ht_sq (congrArg Subtype.val h))
          have := congrArg Subtype.val (hsq_eq.trans ht_eq.symm)
          have hmul : t * t = t * 1 := by simpa [pow_two] using this
          exact (htne (mul_left_cancel hmul)).elim
      rw [Nat.card_zpowers, orderOf_eq_prime ht2 htne]
    exact (Subgroup.eq_of_le_of_card_ge
      ((Subgroup.zpowers_le).mpr htS)
      (by rw [hScard, hcardZ])).symm.le
  · exact (Subgroup.zpowers_le).mpr htS

private theorem elementaryAbelianSubgroup
    {V : Type u} [Group V] [IsElementaryAbelian 2 V]
    (U : Subgroup V) : IsElementaryAbelian 2 U where
  toIsMulCommutative :=
    ⟨⟨fun x y => Subtype.ext
      (show (x : V) * (y : V) = (y : V) * (x : V) from
        (IsMulCommutative.is_comm (M := V)).comm x y)⟩⟩
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (x : V)

private theorem commutatorAction_isInvariant_of_normal_actor
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (Y : Subgroup G) [Y.Normal] :
    IsInvariant G V (commutatorAction Y V) := by
  have hforward : ∀ s : G, ∀ v : V,
      v ∈ commutatorAction Y V → s • v ∈ commutatorAction Y V := by
    intro s v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => s • x ∈ Subgroup.closure
        {x : V | ∃ y : Y, ∃ g : V, x = g⁻¹ * (y • g)})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨y, g, rfl⟩
      refine Subgroup.subset_closure
        ⟨⟨s * (y : G) * s⁻¹,
          (inferInstance : Y.Normal).conj_mem (y : G) y.property s⟩,
          s • g, ?_⟩
      change s • (g⁻¹ * ((y : G) • g)) = _
      have hconj : s • ((y : G) • g) =
          (s * (y : G) * s⁻¹) • (s • g) := by
        simp [smul_smul, mul_assoc]
      rw [smul_mul', smul_inv', hconj]
      rfl
    · simp
    · intro x z _ _ hx hz
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hz
    · intro x _ hx
      simpa [smul_inv'] using Subgroup.inv_mem _ hx
  refine ⟨?_⟩
  intro s v
  constructor
  · exact hforward s v
  · intro hv
    have hback := hforward s⁻¹ (s • v) hv
    simpa [smul_smul] using hback

private theorem transvection_mem_of_fixedPoints_card
    {G V : Type u} [Group G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (t : G) (ht2 : t ^ 2 = 1)
    (hcard : Nat.card V =
      2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V)) :
    let ρ := Representation.ofElementaryAbelianAction
      (A := G) (G := V) (p := 2)
    let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
    e ∈ LinearEquiv.transvections (ZMod 2) (Additive V) := by
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := V) (p := 2)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t)
  let d : Module.End (ZMod 2) (Additive V) :=
    e.toLinearMap - LinearMap.id
  let C := FixedPoints.subgroup (Subgroup.zpowers t) V
  let _ : IsElementaryAbelian 2 C := elementaryAbelianSubgroup C
  let eC : Additive C ≃+ d.ker :=
    { toFun := fun x => ⟨Additive.ofMul ((Additive.toMul x : C) : V), by
          rw [LinearMap.mem_ker]
          apply Additive.toMul.injective
          change ((t • (((Additive.toMul x : C) : V))) /
            (((Additive.toMul x : C) : V))) = 1
          have hfix : t • (((Additive.toMul x : C) : V)) =
              ((Additive.toMul x : C) : V) := by
            exact (FixedPoints.mem_subgroup (M := Subgroup.zpowers t)
              (a := ((Additive.toMul x : C) : V))).1
                (Additive.toMul x : C).property ⟨t, Subgroup.mem_zpowers t⟩
          simp [hfix]⟩
      invFun := fun x => Additive.ofMul ⟨Additive.toMul (x : Additive V), by
          apply (FixedPoints.mem_subgroup
            (M := Subgroup.zpowers t)
            (a := Additive.toMul (x : Additive V))).2
          intro a
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
          have hfix : t • Additive.toMul (x : Additive V) =
              Additive.toMul (x : Additive V) := by
            have hx' : e (x : Additive V) = (x : Additive V) := by
              rw [← sub_eq_zero]
              change d (x : Additive V) = 0
              exact x.property
            change ρ t (x : Additive V) = (x : Additive V) at hx'
            apply Additive.ofMul.injective
            simpa [ρ] using hx'
          change (a : G) • Additive.toMul (x : Additive V) =
            Additive.toMul (x : Additive V)
          rw [← hk]
          exact MulAction.mem_fixedBy_zpow hfix k⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_add' := by intro x y; apply Subtype.ext; rfl }
  have hcardC : Nat.card C = 2 ^ Module.finrank (ZMod 2) (Additive C) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa using (@Module.natCard_eq_pow_finrank
      (ZMod 2) (Additive C) _ _ _ _)
  have hcardKer : Nat.card d.ker =
      2 ^ Module.finrank (ZMod 2) d.ker := by
    simpa using (@Module.natCard_eq_pow_finrank
      (ZMod 2) d.ker _ _ _ _)
  have hcardV : Nat.card V =
      2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa using (@Module.natCard_eq_pow_finrank
      (ZMod 2) (Additive V) _ _ _ _)
  have hfinC : Module.finrank (ZMod 2) (Additive C) =
      Module.finrank (ZMod 2) d.ker := by
    exact LinearEquiv.finrank_eq (eC.toLinearEquiv
      (fun c x => by rfl))
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive V) =
      2 ^ (Module.finrank (ZMod 2) d.ker + 1) := by
    calc
      2 ^ Module.finrank (ZMod 2) (Additive V) = Nat.card V := hcardV.symm
      _ = 2 * Nat.card C := hcard
      _ = 2 * 2 ^ Module.finrank (ZMod 2) (Additive C) := by rw [hcardC]
      _ = 2 * 2 ^ Module.finrank (ZMod 2) d.ker := by rw [hfinC]
      _ = 2 ^ (Module.finrank (ZMod 2) d.ker + 1) := by
        rw [pow_succ]
        ac_rfl
  have hdim : Module.finrank (ZMod 2) (Additive V) =
      Module.finrank (ZMod 2) d.ker + 1 := by
    exact (Nat.pow_right_injective (by omega : 1 < 2)) hpow
  have hrange : Module.finrank (ZMod 2) d.range = 1 := by
    have hrankNull := LinearMap.finrank_range_add_finrank_ker d
    omega
  rw [LinearEquiv.mem_transvections_iff_mem_dilatransvections_and_fixedReduce_eq_one]
  refine ⟨LinearEquiv.mem_dilatransvections_iff_finrank.mpr ?_, ?_⟩
  · simpa [d] using hrange.le
  · change e.fixedReduce = LinearEquiv.refl (ZMod 2) _
    apply (LinearEquiv.fixedReduce_eq_one e).2
    intro x
    have htfix : e (e x) = x := by
      change Additive.ofMul (t • (t • Additive.toMul x)) = x
      simp [← mul_smul, ← pow_two, ht2]
    change e x - x ∈ e.toLinearMap.fixedSubmodule
    change e (e x - x) = e x - x
    have hneg (y : Additive V) : -y = y := by
      apply neg_eq_of_add_eq_zero_left
      calc
        y + y = (1 : ZMod 2) • y + (1 : ZMod 2) • y := by simp
        _ = ((1 : ZMod 2) + 1) • y := (add_smul _ _ _).symm
        _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]
    rw [map_sub, htfix, sub_eq_add_neg, sub_eq_add_neg,
      hneg (e x), hneg x, add_comm]

private theorem transvection_mul_pow_four_of_cross_zero_one
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 0) (hgv : g v = 1) :
    (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
  match_scalars <;>
    simp [ZModModule.add_self, add_comm, add_left_comm]

private theorem transvection_mul_pow_four_of_cross_one_zero
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 1) (hgv : g v = 0) :
    (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw) ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  simp [pow_succ, LinearMap.transvection.apply, hfv, hgw, hfw, hgv]
  match_scalars <;>
    simp [ZModModule.add_self, add_comm, add_left_comm]

private theorem transvection_cross_eq_one_of_pow_three_of_not_commute
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hpow : (LinearEquiv.transvection hfv *
      LinearEquiv.transvection hgw) ^ 3 = 1)
    (hncomm : ¬ Commute
      (LinearEquiv.transvection hfv) (LinearEquiv.transvection hgw)) :
    f w = 1 ∧ g v = 1 := by
  have hfw : f w = 0 ∨ f w = 1 := by
    have hz (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hz (f w)
  have hgv : g v = 0 ∨ g v = 1 := by
    have hz (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact hz (g v)
  rcases hfw with hfw | hfw <;> rcases hgv with hgv | hgv
  · exfalso
    apply hncomm
    apply LinearEquiv.ext
    intro x
    simp [LinearMap.transvection.apply, hfw, hgv]
    module
  · exfalso
    apply hncomm
    let e := LinearEquiv.transvection hfv * LinearEquiv.transvection hgw
    have hpow4 : e ^ 4 = 1 :=
      transvection_mul_pow_four_of_cross_zero_one
        f g v w hfv hgw hfw hgv
    have he : e = 1 := by
      calc
        e = e ^ 4 * (e ^ 3)⁻¹ := by group
        _ = 1 := by rw [hpow4, hpow]; simp
    rw [show LinearEquiv.transvection hfv =
        (LinearEquiv.transvection hgw)⁻¹ from
      eq_inv_of_mul_eq_one_left he]
    exact (Commute.refl (LinearEquiv.transvection hgw)).inv_left
  · exfalso
    apply hncomm
    let e := LinearEquiv.transvection hfv * LinearEquiv.transvection hgw
    have hpow4 : e ^ 4 = 1 :=
      transvection_mul_pow_four_of_cross_one_zero
        f g v w hfv hgw hfw hgv
    have he : e = 1 := by
      calc
        e = e ^ 4 * (e ^ 3)⁻¹ := by group
        _ = 1 := by rw [hpow4, hpow]; simp
    rw [show LinearEquiv.transvection hfv =
        (LinearEquiv.transvection hgw)⁻¹ from
      eq_inv_of_mul_eq_one_left he]
    exact (Commute.refl (LinearEquiv.transvection hgw)).inv_left
  · exact ⟨hfw, hgv⟩

private theorem transvection_product_range_finrank_two
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (f g : Module.Dual (ZMod 2) X) (v w : X)
    (hfv : f v = 0) (hgw : g w = 0)
    (hfw : f w = 1) (hgv : g v = 1) :
    Module.finrank (ZMod 2)
      ((LinearEquiv.transvection hfv * LinearEquiv.transvection hgw).toLinearMap -
        LinearMap.id).range = 2 := by
  let d : Module.End (ZMod 2) X :=
    (LinearEquiv.transvection hfv * LinearEquiv.transvection hgw).toLinearMap -
      LinearMap.id
  let b : Fin 2 → X := ![v, w]
  have hb : LinearIndependent (ZMod 2) b := by
    rw [LinearIndependent.pair_iff]
    intro a c hac
    have hf_ac := congrArg f hac
    have hg_ac := congrArg g hac
    simp [hfv, hgw, hfw, hgv] at hf_ac hg_ac
    exact ⟨hg_ac, hf_ac⟩
  have hvspan : v ∈ Submodule.span (ZMod 2) (Set.range b) :=
    Submodule.subset_span ⟨0, by simp [b]⟩
  have hwspan : w ∈ Submodule.span (ZMod 2) (Set.range b) :=
    Submodule.subset_span ⟨1, by simp [b]⟩
  have hdw : d w = v := by
    simp [d, LinearMap.transvection.apply, hgw, hfw]
  have hdv : d v = v + w := by
    simp [d, LinearMap.transvection.apply, hfv, hgv, hfw]
  have hrange : d.range = Submodule.span (ZMod 2) (Set.range b) := by
    apply le_antisymm
    · rintro y ⟨x, rfl⟩
      have heq : d x = (f x + g x) • v + g x • w := by
        simp [d, LinearMap.transvection.apply, hfw]
        module
      rw [heq]
      exact (Submodule.span (ZMod 2) (Set.range b)).add_mem
        ((Submodule.span (ZMod 2) (Set.range b)).smul_mem _ hvspan)
        ((Submodule.span (ZMod 2) (Set.range b)).smul_mem _ hwspan)
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      fin_cases i
      · exact ⟨w, hdw⟩
      · have hvR : v ∈ d.range := ⟨w, hdw⟩
        have hvwR : v + w ∈ d.range := ⟨v, hdv⟩
        have hadd := d.range.add_mem hvR hvwR
        have heq : v + (v + w) = w := by
          rw [← add_assoc, ZModModule.add_self, zero_add]
        simpa [b, heq] using hadd
  change Module.finrank (ZMod 2) d.range = 2
  rw [hrange, finrank_span_eq_card hb]
  rfl

private theorem cyclic_commutatorAction_eq_difference_range_of_order_three
    {G V : Type u} [Group G] [Group V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (r : G) (hrorder : orderOf r = 3) :
    let d : V →* V :=
      { toFun := fun x => x⁻¹ * (r • x)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp only [mul_inv_rev, smul_mul']
          ac_rfl }
    commutatorAction (Subgroup.zpowers r) V = d.range := by
  let d : V →* V :=
    { toFun := fun x => x⁻¹ * (r • x)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  apply le_antisymm
  · rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := d.range)).mpr ?_
    rintro z ⟨a, x, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
    have hkmod : r ^ (k % (3 : ℤ)) = (a : G) := by
      have hz : r ^ (k % (3 : ℤ)) = r ^ k := by
        simpa [hrorder] using zpow_mod_orderOf r k
      exact hz.trans hk
    have hk_nonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg _ (by omega)
    have hk_lt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos _ (by omega)
    change x⁻¹ * ((a : G) • x) ∈ d.range
    interval_cases hkm : k % (3 : ℤ)
    · rw [← hkmod]
      exact ⟨1, by simp [d]⟩
    · rw [← hkmod]
      exact ⟨x, by simp [d]⟩
    · rw [← hkmod]
      have hdx : d x ∈ d.range := ⟨x, rfl⟩
      have hdrx : d (r • x) ∈ d.range := ⟨r • x, rfl⟩
      have hmul := d.range.mul_mem hdx hdrx
      simpa [d, pow_two, smul_smul, mul_assoc] using hmul
  · intro z hz
    rcases hz with ⟨x, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure
      ⟨⟨r, Subgroup.mem_zpowers r⟩, x, rfl⟩

private theorem difference_range_card_of_linear_finrank
    {G V : Type u} [Group G] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (r : G)
    (hfin : Module.finrank (ZMod 2)
      ((LinearMap.GeneralLinearGroup.toLinearEquiv
          ((Representation.ofElementaryAbelianAction
            (A := G) (G := V) (p := 2)).asGroupHom r)).toLinearMap -
        LinearMap.id).range = 2) :
    let d : V →* V :=
      { toFun := fun x => x⁻¹ * (r • x)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp only [mul_inv_rev, smul_mul']
          ac_rfl }
    Nat.card d.range = 4 := by
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := V) (p := 2)
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom r)
  let dL : Module.End (ZMod 2) (Additive V) := e.toLinearMap - LinearMap.id
  let d : V →* V :=
    { toFun := fun x => x⁻¹ * (r • x)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hpoint (y : V) :
      dL (Additive.ofMul y) = Additive.ofMul (d y) := by
    apply Additive.toMul.injective
    change (r • y) / y = y⁻¹ * (r • y)
    rw [div_eq_mul_inv]
    exact IsMulCommutative.is_comm.comm _ _
  let ed : Additive d.range ≃+ dL.range :=
    { toFun := fun x =>
        ⟨Additive.ofMul (((Additive.toMul x : d.range) : V)), by
          rcases x.property with ⟨y, hy⟩
          refine ⟨Additive.ofMul y, ?_⟩
          rw [hpoint]
          exact congrArg Additive.ofMul hy
        ⟩
      invFun := fun x => ⟨Additive.toMul (x : Additive V), by
          rcases x.property with ⟨y, hy⟩
          refine ⟨Additive.toMul y, ?_⟩
          apply Additive.ofMul.injective
          rw [← hpoint]
          simpa using congrArg (fun z => (z : Additive V)) hy
        ⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_add' := by intro x y; apply Subtype.ext; rfl }
  calc
    Nat.card d.range = Nat.card (Additive d.range) :=
      (Nat.card_congr Additive.toMul).symm
    _ = Nat.card dL.range := Nat.card_congr ed.toEquiv
    _ = 2 ^ Module.finrank (ZMod 2) dL.range := by
      simpa using (@Module.natCard_eq_pow_finrank
        (ZMod 2) dL.range _ _ _ _)
    _ = 4 := by
      have hfin' : Module.finrank (ZMod 2) dL.range = 2 := by
        simpa [dL, e, ρ] using hfin
      rw [hfin']
      norm_num

private theorem transvections_conj
    {X : Type u} [AddCommGroup X] [Module (ZMod 2) X]
    (a e : X ≃ₗ[ZMod 2] X)
    (he : e ∈ LinearEquiv.transvections (ZMod 2) X) :
    a * e * a⁻¹ ∈ LinearEquiv.transvections (ZMod 2) X := by
  rw [LinearEquiv.mem_transvections_iff] at he ⊢
  obtain ⟨f, v, hfv, rfl⟩ := he
  let f' : Module.Dual (ZMod 2) X := f.comp a.symm.toLinearMap
  have hf' : f' (a v) = 0 := by simp [f', hfv]
  refine ⟨f', a v, hf', ?_⟩
  apply LinearEquiv.ext
  intro x
  simp [f', LinearMap.transvection.apply]

private theorem involution_conjugate_to_nontrivial_sylow_element
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2)
    {t : G} (htS : t ∈ (S : Subgroup G)) (htne : t ≠ 1)
    {x : G} (hx : IsInvolution x) :
    ∃ g : G, g * x * g⁻¹ = t := by
  have hxcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx.2 hx.1]
  have hxP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (p := 2) (n := 1) (by simpa using hxcard)
  obtain ⟨Q, hxQ⟩ := hxP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
  have hconjS : g * x * g⁻¹ ∈ (S : Subgroup G) := by
    have hxQ' : x ∈ (Q : Subgroup G) := hxQ (Subgroup.mem_zpowers x)
    have hmem : (MulAut.conj g) x ∈
        ((g • Q : Sylow 2 G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul x (MulAut.conj g)
        (Q : Subgroup G) hxQ'
    simpa [hg, MulAut.conj_apply] using hmem
  have hconjne : g * x * g⁻¹ ≠ 1 := by
    intro h
    have := congrArg (MulAut.conj g⁻¹) h
    exact hx.1 (by simpa [MulAut.conj_apply, mul_assoc] using this)
  obtain ⟨s, hsne, hsunique⟩ :=
    (Nat.card_eq_two_iff' (1 : (S : Subgroup G))).mp hScard
  have hconjeq : (⟨g * x * g⁻¹, hconjS⟩ : (S : Subgroup G)) = s :=
    hsunique _ (by
      intro h
      exact hconjne (congrArg Subtype.val h))
  have hteq : (⟨t, htS⟩ : (S : Subgroup G)) = s :=
    hsunique _ (by
      intro h
      exact htne (congrArg Subtype.val h))
  exact ⟨g, congrArg Subtype.val (hconjeq.trans hteq.symm)⟩

private theorem involution_representation_is_transvection
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Sylow 2 G) (hScard : Nat.card (S : Subgroup G) = 2)
    {t : G} (htS : t ∈ (S : Subgroup G)) (htne : t ≠ 1)
    (httrans :
      LinearMap.GeneralLinearGroup.toLinearEquiv
          ((Representation.ofElementaryAbelianAction
            (A := G) (G := V) (p := 2)).asGroupHom t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V))
    {x : G} (hx : IsInvolution x) :
    LinearMap.GeneralLinearGroup.toLinearEquiv
        ((Representation.ofElementaryAbelianAction
          (A := G) (G := V) (p := 2)).asGroupHom x) ∈
      LinearEquiv.transvections (ZMod 2) (Additive V) := by
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := V) (p := 2)
  let e (g : G) := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  obtain ⟨g, hg⟩ :=
    involution_conjugate_to_nontrivial_sylow_element S hScard htS htne hx
  have heq : e t = e g * e x * (e g)⁻¹ := by
    change LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t) = _
    rw [← hg]
    simp only [map_mul, map_inv,
      LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_inv]
    rfl
  have hrewrite : e x = (e g)⁻¹ * e t * ((e g)⁻¹)⁻¹ := by
    rw [heq]
    group
  change e x ∈ LinearEquiv.transvections (ZMod 2) (Additive V)
  rw [hrewrite]
  exact transvections_conj (e g)⁻¹ (e t) httrans

private theorem exists_distinct_conjugate_involution
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hScard : Nat.card (S : Subgroup G) = 2)
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆)
    {t : G} (htS : t ∈ (S : Subgroup G)) (htne : t ≠ 1) :
    ∃ u : G, IsInvolution u ∧ t ≠ u := by
  have hWne : oddCore G ≠ ⊥ := by
    intro hWbot
    have hStop : (S : Subgroup G) = ⊤ := by
      have hsup := order_two_oddCore_sup_eq_top S hScard
      simpa [hWbot] using hsup
    have hSnorm : (S : Subgroup G).Normal := by
      rw [hStop]
      infer_instance
    have hSle : (S : Subgroup G) ≤ pCore 2 G :=
      le_sSup ⟨hSnorm, S.isPGroup'⟩
    have htbot : t ∈ (⊥ : Subgroup G) := by
      rw [← h.twoCore_eq_bot]
      exact hSle htS
    exact htne (by simpa using htbot)
  have hWnotcent : ¬ oddCore G ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro hcent
    have hcommbot : ⁅oddCore G, (S : Subgroup G)⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcent
    exact hWne (hW.trans hcommbot)
  obtain ⟨w, hwW, hwcent⟩ := Set.not_subset.mp hWnotcent
  have hwcent' : ¬ ∀ s : G, s ∈ (S : Subgroup G) → s * w = w * s := by
    intro hall
    exact hwcent (Subgroup.mem_centralizer_iff.mpr hall)
  push Not at hwcent'
  obtain ⟨s, hsS, hscomm⟩ := hwcent'
  have hsne : s ≠ 1 := by
    intro hs
    subst s
    simp at hscomm
  have hst : s = t := by
    obtain ⟨z, hz, hzuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : (S : Subgroup G))).mp hScard
    have hs_eq : (⟨s, hsS⟩ : (S : Subgroup G)) = z :=
      hzuniq _ (by intro hs; exact hsne (congrArg Subtype.val hs))
    have ht_eq : (⟨t, htS⟩ : (S : Subgroup G)) = z :=
      hzuniq _ (by intro ht; exact htne (congrArg Subtype.val ht))
    exact congrArg Subtype.val (hs_eq.trans ht_eq.symm)
  let u := w * t * w⁻¹
  have hu : IsInvolution u := by
    constructor
    · intro hu
      apply htne
      have := congrArg (fun z : G => w⁻¹ * z * w) hu
      simpa [u, mul_assoc] using this
    · change (w * t * w⁻¹) ^ 2 = 1
      rw [pow_two]
      calc
        (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
        _ = 1 := by
          have ht2 : t ^ 2 = 1 := by
            have horder : orderOf t = 2 := by
              rw [← Nat.card_zpowers,
                ← subgroup_card_two_eq_zpowers_of_mem_ne_one
                  (S : Subgroup G) hScard htS htne]
              exact hScard
            exact orderOf_dvd_iff_pow_eq_one.mp (by rw [horder])
          rw [← pow_two, ht2]
          simp
  refine ⟨u, hu, ?_⟩
  intro htu
  apply hscomm
  rw [hst]
  have := congrArg (fun z : G => z * w) htu
  simpa [u, mul_assoc] using this

private theorem order_two_oddCore_is_cyclic_three
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hScard : Nat.card (S : Subgroup G) = 2)
    (hm : m (G := G) (V := V) (S : Subgroup G) = 1)
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆) :
    ∃ t u : G,
      IsInvolution t ∧ IsInvolution u ∧ t ∈ (S : Subgroup G) ∧ t ≠ u ∧
      (S : Subgroup G) = Subgroup.zpowers t ∧
      (∀ {x : G}, IsInvolution x →
        x = t ∨ x = u ∨ x = u⁻¹ * t * u) ∧
      (t * u) ^ 3 = 1 ∧
      oddCore G = Subgroup.zpowers (t * u) ∧
      Nat.card (oddCore G) = 3 := by
  obtain ⟨ts, htsne, htsuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : (S : Subgroup G))).mp hScard
  let t : G := ts
  have htS : t ∈ (S : Subgroup G) := ts.property
  have htne : t ≠ 1 := by
    intro ht
    exact htsne (Subtype.ext ht)
  have hSt : (S : Subgroup G) = Subgroup.zpowers t :=
    subgroup_card_two_eq_zpowers_of_mem_ne_one (S : Subgroup G) hScard htS htne
  have ht2 : t ^ 2 = 1 := by
    have htorder : orderOf t = 2 := by
      rw [← Nat.card_zpowers, ← hSt]
      exact hScard
    exact orderOf_dvd_iff_pow_eq_one.mp (by rw [htorder])
  have ht : IsInvolution t := ⟨htne, ht2⟩
  have hcardfix : Nat.card V =
      2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) := by
    rw [← hSt]
    exact card_eq_two_mul_fixedPoints_of_m_eq_one_of_card_two
      (S : Subgroup G) hScard hm
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := V) (p := 2)
  have hρlin : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
    exact h.action_faithful
  have hρ : Function.Injective ρ.asGroupHom := by
    intro a b hab
    exact hρlin (congrArg Units.val hab)
  have httrans :
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V) := by
    exact transvection_mem_of_fixedPoints_card t ht2 hcardfix
  have htrans : ∀ {x : G}, IsInvolution x →
      LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom x) ∈
        LinearEquiv.transvections (ZMod 2) (Additive V) := by
    intro x hx
    exact involution_representation_is_transvection
      S hScard htS htne httrans hx
  obtain ⟨hncomm, hproduct⟩ := order_two_sylow_involution_structure S hScard
  obtain ⟨u, hu, htu⟩ :=
    exists_distinct_conjugate_involution h S hScard hW htS htne
  have hthree : ∀ {x : G}, IsInvolution x →
      x = t ∨ x = u ∨ x = u⁻¹ * t * u :=
    Representation.three_involutions_of_faithful_transvection_representation
      ρ hρ htrans
      (fun hx hy hxy => ⟨hncomm hx hy hxy, (hproduct hx hy).2⟩)
      ht hu htu
  have htinv : t⁻¹ = t := inv_eq_self_of_orderOf_eq_two
    (orderOf_eq_prime ht.2 ht.1)
  have huinv : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two
    (orderOf_eq_prime hu.2 hu.1)
  have htt : t * t = 1 := by simpa [pow_two] using ht.2
  have huu : u * u = 1 := by simpa [pow_two] using hu.2
  let q : G := t * u * t
  have hu_conj_q : u = t * q * t := by
    dsimp [q]
    calc
      u = 1 * u * 1 := by simp
      _ = (t * t) * u * (t * t) := by rw [htt]
      _ = t * (t * u * t) * t := by group
  have hq : IsInvolution q := by
    constructor
    · intro hqone
      apply hu.1
      calc
        u = t * q * t := hu_conj_q
        _ = t * 1 * t := by rw [hqone]
        _ = 1 := by simpa using htt
    · dsimp [q]
      rw [pow_two]
      calc
        (t * u * t) * (t * u * t) = t * u * (t * t) * u * t := by group
        _ = t * (u * u) * t := by rw [htt]; simp [mul_assoc]
        _ = 1 := by rw [huu]; simpa using htt
  have hqt : q ≠ t := by
    intro hqt
    apply htu
    calc
      t = t * t * t := by rw [htt]; simp
      _ = t * q * t := by rw [hqt]
      _ = u := hu_conj_q.symm
  have hqu : q ≠ u := by
    intro hqu
    apply hncomm ht hu htu
    show t * u = u * t
    have := congrArg (fun z : G => z * t) hqu
    calc
      t * u = (t * u * t) * t := by rw [mul_assoc, htt, mul_one]
      _ = u * t := this
  have hqeq : q = u⁻¹ * t * u := by
    rcases hthree hq with hqt' | hqu' | hqeq
    · exact (hqt hqt').elim
    · exact (hqu hqu').elim
    · exact hqeq
  have htu3 : (t * u) ^ 3 = 1 := by
    have hqutu : q = u * t * u := by simpa [huinv] using hqeq
    calc
      (t * u) ^ 3 = q * (u * t * u) := by
        dsimp [q]
        simp [pow_succ, mul_assoc]
      _ = q * q := by rw [← hqutu]
      _ = q ^ 2 := by rw [pow_two]
      _ = 1 := hq.2
  let r : G := t * u
  have hrne : r ≠ 1 := by
    intro hr
    apply htu
    have hteq : t = u⁻¹ := eq_inv_of_mul_eq_one_left hr
    exact hteq.trans huinv
  have hrorder : orderOf r = 3 := orderOf_eq_prime (by simpa [r] using htu3) hrne
  have hrW : r ∈ oddCore G := by
    simpa [oddCore, r] using (hproduct ht hu).1
  have hWle : oddCore G ≤ Subgroup.zpowers r := by
    rw [hW]
    apply Subgroup.commutator_le.mpr
    intro w hw s hs
    have hs_cases : s = 1 ∨ s = t := by
      by_cases hsone : s = 1
      · exact Or.inl hsone
      · have hseq : (⟨s, hs⟩ : (S : Subgroup G)) = ts := htsuniq _ (by
          intro heq
          exact hsone (congrArg Subtype.val heq))
        exact Or.inr (congrArg Subtype.val hseq)
    rcases hs_cases with rfl | rfl
    · simp
    · let a : G := w * t * w⁻¹
      have ha : IsInvolution a := by
        constructor
        · intro haone
          apply ht.1
          have := congrArg (fun z : G => w⁻¹ * z * w) haone
          simpa [a, mul_assoc] using this
        · change (w * t * w⁻¹) ^ 2 = 1
          rw [pow_two]
          calc
            (w * t * w⁻¹) * (w * t * w⁻¹) = w * (t * t) * w⁻¹ := by group
            _ = 1 := by rw [← pow_two, ht.2]; simp
      rcases hthree ha with haeq | haeq | haeq
      · change w * t * w⁻¹ * t⁻¹ ∈ Subgroup.zpowers r
        rw [show w * t * w⁻¹ = t from haeq, htinv, htt]
        exact (Subgroup.zpowers r).one_mem
      · have hri : r⁻¹ ∈ Subgroup.zpowers r :=
          (Subgroup.zpowers r).inv_mem (Subgroup.mem_zpowers r)
        change w * t * w⁻¹ * t⁻¹ ∈ Subgroup.zpowers r
        rw [show w * t * w⁻¹ = u from haeq, htinv]
        have heq : u * t = r⁻¹ := by
          simp [r, mul_inv_rev, htinv, huinv]
        rw [heq]
        exact hri
      · have hri : r⁻¹ ∈ Subgroup.zpowers r :=
          (Subgroup.zpowers r).inv_mem (Subgroup.mem_zpowers r)
        have hrii : r⁻¹ * r⁻¹ ∈ Subgroup.zpowers r :=
          (Subgroup.zpowers r).mul_mem hri hri
        change w * t * w⁻¹ * t⁻¹ ∈ Subgroup.zpowers r
        rw [show w * t * w⁻¹ = u⁻¹ * t * u from haeq, htinv]
        have heq : (u⁻¹ * t * u) * t = r⁻¹ * r⁻¹ := by
          simp [r, mul_inv_rev, htinv, huinv, mul_assoc]
        rw [heq]
        exact hrii
  have hWeq : oddCore G = Subgroup.zpowers r := by
    apply le_antisymm hWle
    exact (Subgroup.zpowers_le).mpr hrW
  have hWcard : Nat.card (oddCore G) = 3 := by
    rw [hWeq, Nat.card_zpowers, hrorder]
  exact ⟨t, u, ht, hu, htS, htu, hSt, hthree, htu3,
    by simpa [r] using hWeq, hWcard⟩

private theorem order_two_oddCore_commutator_and_fixed_card
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hScard : Nat.card (S : Subgroup G) = 2)
    (hm : m (G := G) (V := V) (S : Subgroup G) = 1)
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆) :
    Nat.card (commutatorAction (oddCore G) V) = 4 ∧
      Nat.card (↥((commutatorAction (oddCore G) V) ⊓
        FixedPoints.subgroup (S : Subgroup G) V)) = 2 ∧
      IsSL2Two G := by
  obtain ⟨t, u, ht, hu, htS, htu, hSt, _hthree, htu3, hWeq, _hWcard⟩ :=
    order_two_oddCore_is_cyclic_three h S hScard hm hW
  have ht2 : t ^ 2 = 1 := ht.2
  have hcardfix : Nat.card V =
      2 * Nat.card (FixedPoints.subgroup (Subgroup.zpowers t) V) := by
    rw [← hSt]
    exact card_eq_two_mul_fixedPoints_of_m_eq_one_of_card_two
      (S : Subgroup G) hScard hm
  let ρ := Representation.ofElementaryAbelianAction
    (A := G) (G := V) (p := 2)
  let e (g : G) :=
    LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)
  have hρlin : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rw [Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
    exact h.action_faithful
  have hρ : Function.Injective ρ.asGroupHom := by
    intro a b hab
    exact hρlin (congrArg Units.val hab)
  have httrans : e t ∈
      LinearEquiv.transvections (ZMod 2) (Additive V) := by
    exact transvection_mem_of_fixedPoints_card t ht2 hcardfix
  have hutrans : e u ∈
      LinearEquiv.transvections (ZMod 2) (Additive V) := by
    exact involution_representation_is_transvection
      S hScard htS ht.1 httrans hu
  obtain ⟨hncomm, _hproduct⟩ :=
    order_two_sylow_involution_structure S hScard
  have he_ncomm : ¬ Commute (e t) (e u) := by
    intro hecomm
    apply hncomm ht hu htu
    apply hρ
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Additive V)).injective
    rw [map_mul, map_mul]
    rw [map_mul]
    change e t * e u = e u * e t
    exact hecomm.eq
  rw [LinearEquiv.mem_transvections_iff] at httrans hutrans
  obtain ⟨f, v, hfv, hteq⟩ := httrans
  obtain ⟨g, w, hgw, hueq⟩ := hutrans
  have hpow : (LinearEquiv.transvection hfv *
      LinearEquiv.transvection hgw) ^ 3 = 1 := by
    rw [← hteq, ← hueq]
    let eHom : G →* (Additive V ≃ₗ[ZMod 2] Additive V) :=
      (LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod 2) (Additive V)).toMonoidHom.comp ρ.asGroupHom
    change (eHom t * eHom u) ^ 3 = 1
    rw [← map_mul, ← map_pow, htu3, map_one]
  have hcross : f w = 1 ∧ g v = 1 :=
    transvection_cross_eq_one_of_pow_three_of_not_commute
      f g v w hfv hgw hpow (by simpa [hteq, hueq] using he_ncomm)
  have hfin : Module.finrank (ZMod 2)
      ((e (t * u)).toLinearMap - LinearMap.id).range = 2 := by
    have hmul : e (t * u) = e t * e u := by
      simp [e, ρ, LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
    rw [hmul, hteq, hueq]
    exact transvection_product_range_finrank_two
      f g v w hfv hgw hcross.1 hcross.2
  let d : V →* V :=
    { toFun := fun x => x⁻¹ * ((t * u) • x)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp only [mul_inv_rev, smul_mul']
        ac_rfl }
  have hdcard : Nat.card d.range = 4 :=
    difference_range_card_of_linear_finrank (t * u) (by
      simpa [e, ρ] using hfin)
  have hcomm : commutatorAction (Subgroup.zpowers (t * u)) V = d.range :=
    cyclic_commutatorAction_eq_difference_range_of_order_three
      (t * u) (orderOf_eq_prime htu3 (by
        intro htu_one
        apply htu
        exact eq_inv_of_mul_eq_one_left htu_one |>.trans
          (inv_eq_self_of_orderOf_eq_two (orderOf_eq_prime hu.2 hu.1))))
  have hUeq : commutatorAction (oddCore G) V = d.range := by
    rw [hWeq, hcomm]
  have hUcard : Nat.card (commutatorAction (oddCore G) V) = 4 := by
    rw [hUeq]
    exact hdcard
  have hmul : e (t * u) = e t * e u := by
    simp [e, ρ, LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
  have hdw : d (Additive.toMul w) = Additive.toMul v := by
    apply Additive.ofMul.injective
    change -w + e (t * u) w = v
    rw [hmul, hteq, hueq]
    simp [LinearMap.transvection.apply, hgw, hcross.1]
  have hdv : d (Additive.toMul v) = Additive.toMul (v + w) := by
    apply Additive.ofMul.injective
    change -v + e (t * u) v = v + w
    rw [hmul, hteq, hueq]
    simp [LinearMap.transvection.apply, hfv, hcross.1, hcross.2]
  have hvD : Additive.toMul v ∈ d.range := ⟨Additive.toMul w, hdw⟩
  have hvwD : Additive.toMul (v + w) ∈ d.range :=
    ⟨Additive.toMul v, hdv⟩
  have hwD : Additive.toMul w ∈ d.range := by
    have hadd := d.range.mul_mem hvD hvwD
    have heq : Additive.toMul v * Additive.toMul (v + w) =
        Additive.toMul w := by
      apply Additive.ofMul.injective
      change v + (v + w) = w
      rw [← add_assoc, ZModModule.add_self, zero_add]
    rw [heq] at hadd
    exact hadd
  have hvU : Additive.toMul v ∈ commutatorAction (oddCore G) V := by
    rw [hUeq]
    exact hvD
  have hwU : Additive.toMul w ∈ commutatorAction (oddCore G) V := by
    rw [hUeq]
    exact hwD
  have hvne : Additive.toMul v ≠ (1 : V) := by
    intro hvone
    have hvzero : v = 0 := by
      apply Additive.toMul.injective
      simpa using hvone
    have := hcross.2
    rw [hvzero, map_zero] at this
    norm_num at this
  have htfixv : t • Additive.toMul v = Additive.toMul v := by
    apply Additive.ofMul.injective
    change e t v = v
    rw [hteq]
    simp [LinearMap.transvection.apply, hfv]
  have ht_notfix_w : t • Additive.toMul w ≠ Additive.toMul w := by
    intro hwfix
    have hwfix' := congrArg Additive.ofMul hwfix
    change e t w = w at hwfix'
    rw [hteq] at hwfix'
    simp [LinearMap.transvection.apply, hcross.1] at hwfix'
    exact hvne (by
      apply Additive.ofMul.injective
      exact hwfix')
  have hvFix : Additive.toMul v ∈
      FixedPoints.subgroup (S : Subgroup G) V := by
    rw [FixedPoints.mem_subgroup]
    intro a
    have haZ : (a : G) ∈ Subgroup.zpowers t := by
      rw [← hSt]
      exact a.property
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haZ
    change ((a : G) • Additive.toMul v) = Additive.toMul v
    rw [← hk]
    exact MulAction.mem_fixedBy_zpow htfixv k
  have hwNotFix : Additive.toMul w ∉
      FixedPoints.subgroup (S : Subgroup G) V := by
    intro hwfix
    have hfix := (FixedPoints.mem_subgroup
      (M := (S : Subgroup G)) (a := Additive.toMul w)).mp hwfix
      ⟨t, htS⟩
    exact ht_notfix_w hfix
  let H : Subgroup V := (commutatorAction (oddCore G) V) ⊓
    FixedPoints.subgroup (S : Subgroup G) V
  have hvH : Additive.toMul v ∈ H := ⟨hvU, hvFix⟩
  have hvpow : (Additive.toMul v) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (Additive.toMul v)
  have hzcard : Nat.card (Subgroup.zpowers (Additive.toMul v)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hvpow hvne]
  have hzleH : Subgroup.zpowers (Additive.toMul v) ≤ H :=
    (Subgroup.zpowers_le).mpr hvH
  have htwo_dvd : 2 ∣ Nat.card H := by
    rw [← hzcard]
    exact Subgroup.card_dvd_of_le hzleH
  have hH_dvd_four : Nat.card H ∣ 4 := by
    rw [← hUcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hH_ne_four : Nat.card H ≠ 4 := by
    intro hHcard
    have hHU : H = commutatorAction (oddCore G) V := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hHcard, hUcard]
    have hwH : Additive.toMul w ∈ H := by
      rw [hHU]
      exact hwU
    exact hwNotFix hwH.2
  have hHcard : Nat.card H = 2 := by
    have hHle : Nat.card H ≤ 4 := Nat.le_of_dvd (by omega) hH_dvd_four
    obtain ⟨a, ha⟩ := htwo_dvd
    obtain ⟨b, hb⟩ := hH_dvd_four
    have hHpos : 0 < Nat.card H := Nat.card_pos
    omega
  have hGcard : Nat.card G = 6 := by
    have hcomp := sylow_isComplement_pPrimeCore_of_hasNormalPComplement
      (G := G) (p := 2) (order_two_hasNormalPComplement S hScard) S
    have hmul := hcomp.card_mul_card
    have hWcard' : Nat.card (pPrimeCore 2 G) = 3 := by
      simpa only [oddCore] using _hWcard
    rw [hScard, hWcard'] at hmul
    omega
  let U : Subgroup V := commutatorAction (oddCore G) V
  let _ : (oddCore G).Normal := by
    simpa only [oddCore] using (pPrimeCore_normal (p := 2) (G := G))
  let hUinv : IsInvariant G V U := by
    simpa [U] using
      (commutatorAction_isInvariant_of_normal_actor (G := G) (V := V)
        (oddCore G))
  let _ : IsInvariant G V U := hUinv
  let _ : IsElementaryAbelian 2 U := elementaryAbelianSubgroup U
  let ρU := Representation.ofElementaryAbelianAction
    (A := G) (G := U) (p := 2)
  let K : Subgroup G := ρU.asGroupHom.ker
  have ht_notK : t ∉ K := by
    intro htK
    have hρt : ρU t = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.mp htK)
    have happ := LinearMap.congr_fun hρt
      (Additive.ofMul (⟨Additive.toMul w, by simpa [U] using hwU⟩ : U))
    have hfixU : t •
        (⟨Additive.toMul w, by simpa [U] using hwU⟩ : U) =
        ⟨Additive.toMul w, by simpa [U] using hwU⟩ := by
      apply Additive.ofMul.injective
      simpa [ρU, mul_smul] using happ
    exact ht_notfix_w (congrArg Subtype.val hfixU)
  have hr_notK : t * u ∉ K := by
    intro hrK
    have hρr : ρU (t * u) = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.mp hrK)
    have happ := LinearMap.congr_fun hρr
      (Additive.ofMul (⟨Additive.toMul w, by simpa [U] using hwU⟩ : U))
    have hfixU : (t * u) •
        (⟨Additive.toMul w, by simpa [U] using hwU⟩ : U) =
        ⟨Additive.toMul w, by simpa [U] using hwU⟩ := by
      apply Additive.ofMul.injective
      simpa [ρU, mul_smul] using happ
    have hfixV : (t * u) • Additive.toMul w = Additive.toMul w :=
      congrArg Subtype.val hfixU
    have hd_one : d (Additive.toMul w) = 1 := by
      simp [d, hfixV]
    rw [hdw] at hd_one
    exact hvne hd_one
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKcard_dvd : Nat.card K ∣ 6 := by
    rw [← hGcard]
    have hd : Nat.card K ∣ Nat.card (⊤ : Subgroup G) :=
      Subgroup.card_dvd_of_le (H := K) (K := ⊤) le_top
    simpa using hd
  have hKcard : Nat.card K = 1 := by
    have hKle : Nat.card K ≤ 6 := Nat.le_of_dvd (by omega) hKcard_dvd
    have hKpos : 0 < Nat.card K := Nat.card_pos
    interval_cases hk : Nat.card K
    · rfl
    · have hKp : IsPGroup 2 K :=
        IsPGroup.of_card (p := 2) (n := 1) (by simpa using hk)
      have hKcore : K ≤ pCore 2 G := le_sSup ⟨hKnormal, hKp⟩
      have hKbot : K = ⊥ := by
        apply le_antisymm
        · rw [← h.twoCore_eq_bot]
          exact hKcore
        · exact bot_le
      have : Nat.card K = 1 := by rw [hKbot]; simp
      omega
    · have hKodd : Nat.Coprime 2 (Nat.card K) := by
        rw [hk]
        decide
      have hKW : K ≤ oddCore G := le_sSup ⟨hKnormal, hKodd⟩
      have hKeq : K = oddCore G := by
        apply Subgroup.eq_of_le_of_card_ge hKW
        rw [hk, _hWcard]
      exfalso
      apply hr_notK
      rw [hKeq, hWeq]
      exact Subgroup.mem_zpowers (t * u)
    · norm_num [hk] at hKcard_dvd
    · norm_num [hk] at hKcard_dvd
    · have hKeq : K = ⊤ := by
        apply Subgroup.eq_of_le_of_card_ge le_top
        rw [hk, Subgroup.card_top, hGcard]
      exfalso
      apply ht_notK
      rw [hKeq]
      exact Subgroup.mem_top t
  have hρUinj : Function.Injective ρU.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact (Subgroup.card_eq_one.mp hKcard)
  let toSL : LinearMap.GeneralLinearGroup (ZMod 2) (Additive U) →*
      _root_.SpecialLinearGroup (ZMod 2) (Additive U) :=
    { toFun := fun a => ⟨a.toLinearEquiv, Subsingleton.elim _ _⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  have htoSLinj : Function.Injective toSL := by
    intro a b hab
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Additive U)).injective
    exact congrArg Subtype.val hab
  have htoSLsurj : Function.Surjective toSL := by
    intro a
    refine ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv a.1, ?_⟩
    apply Subtype.ext
    rfl
  let eGLSL : LinearMap.GeneralLinearGroup (ZMod 2) (Additive U) ≃*
      _root_.SpecialLinearGroup (ZMod 2) (Additive U) :=
    MulEquiv.ofBijective toSL ⟨htoSLinj, htoSLsurj⟩
  let nU := Module.finrank (ZMod 2) (Additive U)
  have hnU : nU = 2 := by
    have hc : Nat.card (Additive U) = 4 := by
      calc
        Nat.card (Additive U) = Nat.card U := Nat.card_congr Additive.toMul
        _ = 4 := by simpa [U] using hUcard
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive U)] at hc
    norm_num at hc
    change 2 ^ nU = 2 ^ 2 at hc
    exact Nat.pow_right_injective (by omega) hc
  let b0 : Module.Basis (Fin nU) (ZMod 2) (Additive U) :=
    Module.finBasis (ZMod 2) (Additive U)
  let _ : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Additive U)) :=
    Finite.of_equiv (Matrix.GeneralLinearGroup (Fin nU) (ZMod 2))
      (Matrix.GeneralLinearGroup.toLin' b0).toEquiv
  let _ : Finite (_root_.SpecialLinearGroup (ZMod 2) (Additive U)) :=
    Finite.of_equiv
      (LinearMap.GeneralLinearGroup (ZMod 2) (Additive U)) eGLSL.toEquiv
  have hGLcard : Nat.card
      (LinearMap.GeneralLinearGroup (ZMod 2) (Additive U)) = 6 := by
    calc
      Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) (Additive U)) =
          Nat.card (Matrix.GeneralLinearGroup (Fin nU) (ZMod 2)) :=
        Nat.card_congr (Matrix.GeneralLinearGroup.toLin' b0).symm.toEquiv
      _ = 6 := by
        rw [hnU, Matrix.card_GL_field]
        norm_num [Fin.prod_univ_succ]
  have hSLcard : Nat.card
      (_root_.SpecialLinearGroup (ZMod 2) (Additive U)) = 6 := by
    rw [← hGLcard]
    exact Nat.card_congr eGLSL.toEquiv |>.symm
  let φ : G →* _root_.SpecialLinearGroup (ZMod 2) (Additive U) :=
    toSL.comp ρU.asGroupHom
  have hφinj : Function.Injective φ := htoSLinj.comp hρUinj
  have hφbij : Function.Bijective φ := by
    let iG : Fintype G := Fintype.ofFinite G
    let iSL : Fintype (_root_.SpecialLinearGroup (ZMod 2) (Additive U)) :=
      Fintype.ofFinite
      (_root_.SpecialLinearGroup (ZMod 2) (Additive U))
    apply (@Fintype.bijective_iff_injective_and_card _ _ iG iSL φ).2
    refine ⟨hφinj, ?_⟩
    rw [← @Nat.card_eq_fintype_card G iG,
      ← @Nat.card_eq_fintype_card
        (_root_.SpecialLinearGroup (ZMod 2) (Additive U)) iSL]
    exact hGcard.trans hSLcard.symm
  let eG : G ≃* _root_.SpecialLinearGroup (ZMod 2) (Additive U) :=
    MulEquiv.ofBijective φ hφbij
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) := by
    simpa [hnU] using b0
  have hSL2 : IsSL2Two G :=
    ⟨eG.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm⟩
  exact ⟨hUcard, by simpa [H] using hHcard, hSL2⟩

/-- The order-two base case in Stellmacher's proof of Lemma (1.6). -/
public theorem order_two_odd_complement_classification
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (_hS_elem : IsElementaryAbelian 2 (S : Subgroup G))
    (hScard : Nat.card (S : Subgroup G) = 2)
    (hm : m (G := G) (V := V) (S : Subgroup G) = 1)
    (hW : oddCore G = ⁅oddCore G, (S : Subgroup G)⁆) :
    LemmaOneSixConclusion (G := G) (V := V) (S : Subgroup G) := by
  obtain ⟨hUcard, hFixCard, hSL2⟩ :=
    order_two_oddCore_commutator_and_fixed_card h S hScard hm hW
  obtain ⟨_t, _u, _ht, _hu, _htS, _htu, _hSt, _hthree, _htu3,
      _hWeq, hWcard⟩ :=
    order_two_oddCore_is_cyclic_three h S hScard hm hW
  let _ : (oddCore G).Normal := by
    simpa only [oddCore] using (pPrimeCore_normal (p := 2) (G := G))
  have hGcard : Nat.card G = 6 := by
    have hcomp := sylow_isComplement_pPrimeCore_of_hasNormalPComplement
      (G := G) (p := 2) (order_two_hasNormalPComplement S hScard) S
    have hmul := hcomp.card_mul_card
    have hWcard' : Nat.card (pPrimeCore 2 G) = 3 := by
      simpa only [oddCore] using hWcard
    rw [hScard, hWcard'] at hmul
    omega
  have hQcard : Nat.card (G ⧸ oddCore G) = 2 := by
    have hmul :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore G)
    rw [hGcard, hWcard] at hmul
    omega
  have hQcomm : IsMulCommutative (G ⧸ oddCore G) :=
    (isCyclic_of_prime_card (p := 2) hQcard).isMulCommutative
  have hcomm_le : commutator G ≤ oddCore G :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hQcomm
  have hW_le_comm : oddCore G ≤ commutator G := by
    rw [hW]
    calc
      ⁅oddCore G, (S : Subgroup G)⁆ ≤
          ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mono le_top le_top
      _ = commutator G := rfl
  have hcomm_eq : commutator G = oddCore G :=
    le_antisymm hcomm_le hW_le_comm
  let E : Subgroup G := ⊤
  let D : Subgroup G := (commutator (↥E)).map E.subtype
  have hDE : D = oddCore G := by
    calc
      D = ⁅E, E⁆ := Subgroup.map_subtype_commutator E
      _ = commutator G := by rfl
      _ = oddCore G := hcomm_eq
  have hEsl : IsSL2Two (↥E) := by
    rcases hSL2 with ⟨e⟩
    exact ⟨Subgroup.topEquiv.trans e⟩
  have hDone : oneOmega (G := G) (V := V) D := by
    rw [hDE]
    exact ⟨le_rfl, hWcard, hUcard⟩
  have hproduct : ∃ F : Finset (Subgroup G),
      (∀ E' : Subgroup G, E' ∈ F →
        IsSL2Two (↥E') ∧
          oneOmega (G := G) (V := V)
            ((commutator (↥E')).map E'.subtype)) ∧
      IsInternalDirectProduct (oddCore G ⊔ (S : Subgroup G)) F := by
    refine ⟨{E}, ?_, ?_⟩
    · intro E' hE'
      have hEE : E' = E := by simpa using hE'
      subst E'
      exact ⟨hEsl, hDone⟩
    · simp [E, IsInternalDirectProduct,
        order_two_oddCore_sup_eq_top S hScard]
  have hquadratic : commutatorAction₂ (S : Subgroup G) V = ⊥ :=
    commutatorAction₂_eq_bot_of_actor_card_two hScard
  have hfixed : fixedQuotientCard (G := G) (V := V)
      (S : Subgroup G) (commutatorAction (oddCore G) V) =
        (Nat.card (S : Subgroup G) : ℚ) := by
    unfold fixedQuotientCard
    rw [hUcard, hFixCard, hScard]
    norm_num
  exact LemmaOneSixConclusion.sl2Product hproduct hquadratic hfixed

end Stellmacher.SectionOne
