module

public import Theory.GroupTheory.PStar.ExtensionKernels
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.ChiefFactorDirectPower

/-!
# Reduction of the two-star extension criterion to chief kernels

Assume the extension criterion for a two-perfect finite group with an ambient
chief kernel. Strong induction on the normal kernel order proves the general
two-perfect case. When its residual is trivial, the kernel is a central
two-group. Otherwise choose an ambient minimal normal subgroup in the embedded
kernel residual, pass to the quotient, and use the two-star property of that
residual to obtain the Sylow-centralizer supplement for the chief kernel.

For an arbitrary ambient group, restrict to its two-residual. The quotient
covers the original quotient, the kernel residual is unchanged under the
literal embeddings, and Sylow restriction preserves the generation hypothesis.
This discharges the passage to a two-perfect ambient group.

Source: GLS II, Chapter B, Lemma 5.3, reduction before the chief-kernel argument
(`refs/KGroup/GLS2/ChapterB.tex`, lines 600–628). The residual restriction follows
the same explicit maps as `PStar/SylowBound/ResidualReduction.lean`.
The sole unproved input is the stated universal chief-kernel implication;
the source theorem's assembly must supply it.
-/

public section

open Subgroup
namespace Theory.GroupTheory
universe u

/-- The chief-kernel case of GLS II B.5.3. Its universe is shared with the
subgroup and quotient applications in the reduction. -/
abbrev PStarChiefExtensionCriterion : Prop :=
  ∀ (Y : Type u) [Group Y] [Finite Y] (K : Subgroup Y) [K.Normal],
    ChiefFactor.IsChief K ⊥ → ∀ S : Sylow 2 K,
    IsPPerfect 2 Y → IsPStar 2 (Y ⧸ K) →
    K ⊔ centralizer ((S : Subgroup K).map K.subtype : Set Y) = ⊤ → IsPStar 2 Y

variable {G : Type u} [Group G] [Finite G]

private theorem exists_chief_in (H : Subgroup G) [H.Normal] (hH : H ≠ ⊥) :
    ∃ K : Subgroup G, ChiefFactor.IsChief K ⊥ ∧ K ≤ H := by
  obtain ⟨K, ⟨hK, hne, hKH⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥ ∧ K ≤ H)
    ⟨H, inferInstance, hH, le_rfl⟩
  refine ⟨K, ⟨hK, inferInstance, bot_lt_iff_ne_bot.mpr hne, ?_⟩, hKH⟩
  intro J hJ _ hJK
  by_cases he : J = ⊥
  · exact Or.inl he
  · exact Or.inr (le_antisymm hJK (hmin ⟨hJ, he, hJK.trans hKH⟩ hJK))

omit [Finite G] in
private theorem supplement_inside (R K : Subgroup G) [K.Normal]
    (hR : IsPStar 2 R) (hKR : K ≤ R) (S : Sylow 2 K) :
    R ≤ K ⊔ centralizer ((S : Subgroup K).map K.subtype : Set G) := by
  let J := K.subgroupOf R
  let e : J ≃* K := subgroupOfEquivOfLe hKR
  let T : Sylow 2 J := S.comapOfInjective e.toMonoidHom e.injective
    (by rw [e.toMonoidHom.range_eq_top_of_surjective e.surjective]; exact le_top)
  intro r hr
  have hx : (⟨r, hr⟩ : R) ∈ J ⊔ centralizer ((T : Subgroup J).map J.subtype : Set R) := by
    rw [hR.2 J T]
    trivial
  obtain ⟨k, hk, c, hc, he⟩ := mem_sup_of_normal_left.mp hx
  refine mem_sup_of_normal_left.mpr ⟨k.val, hk, c.val, ?_, congrArg Subtype.val he⟩
  rintro s ⟨a, ha, rfl⟩
  have ht : e.symm a ∈ (T : Subgroup J) := by
    change e (e.symm a) ∈ (S : Subgroup K)
    rw [e.apply_symm_apply]
    exact ha
  exact congrArg Subtype.val (hc (J.subtype (e.symm a)) (mem_map_of_mem J.subtype ht))

private theorem sylow_restrict (N K : Subgroup G) [K.Normal]
    (hKN : K ≤ N) (P : Sylow 2 N) :
    ∃ S : Sylow 2 K,
      (S : Subgroup K).map K.subtype ≤ (P : Subgroup N).map N.subtype := by
  let J := K.subgroupOf N
  obtain ⟨T, hT⟩ := P.exists_subgroupOf_eq_of_normal J
  let e : J ≃* K := subgroupOfEquivOfLe hKN
  refine ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  rintro s ⟨a, ha, rfl⟩
  change a ∈ (T : Subgroup J).map e.toMonoidHom at ha
  obtain ⟨t, ht, rfl⟩ := ha
  rw [hT] at ht
  exact mem_map.mpr ⟨t.val, ht, rfl⟩

private theorem quotient_kernel_card_lt (N K : Subgroup G) [K.Normal]
    (hKN : K ≤ N) (hne : K ≠ ⊥) :
    Nat.card (N.map (QuotientGroup.mk' K)) < Nat.card N := by
  classical
  let f := (QuotientGroup.mk' K).subgroupMap N
  let := Fintype.ofFinite N
  let := Fintype.ofFinite (N.map (QuotientGroup.mk' K))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_surjective_not_injective f
    ((QuotientGroup.mk' K).subgroupMap_surjective N)
  intro hi
  apply hne
  apply eq_bot_iff.mpr
  intro k hk
  have he : f ⟨k, hKN hk⟩ = f 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr hk
  exact congrArg Subtype.val (hi he)

private theorem quotient_hypotheses (N K : Subgroup G) [N.Normal] [K.Normal]
    (hKN : K ≤ N) (P : Sylow 2 N)
    (hquot : IsPStar 2 (G ⧸ N)) (hres : IsPStar 2 (pResidual 2 N))
    (hgen : (pResidual 2 N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    ∃ Q : Sylow 2 (N.map (QuotientGroup.mk' K)),
      IsPStar 2 ((G ⧸ K) ⧸ N.map (QuotientGroup.mk' K)) ∧
      IsPStar 2 (pResidual 2 (N.map (QuotientGroup.mk' K))) ∧
      (pResidual 2 (N.map (QuotientGroup.mk' K))).map
          (N.map (QuotientGroup.mk' K)).subtype ⊔
        centralizer ((Q : Subgroup (N.map (QuotientGroup.mk' K))).map
          (N.map (QuotientGroup.mk' K)).subtype : Set (G ⧸ K)) = ⊤ := by
  let q := QuotientGroup.mk' K
  let M := N.map q
  let f := q.subgroupMap N
  let Q := P.mapSurjective (q.subgroupMap_surjective N)
  refine ⟨Q, ?_, ?_, ?_⟩
  · let g := QuotientGroup.lift K (QuotientGroup.mk' N) (by simpa using hKN)
    have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective K
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) (by simpa using hKN)
    have hk : g.ker = M := by
      simpa only [QuotientGroup.ker_mk'] using
        QuotientGroup.ker_lift K (QuotientGroup.mk' N) (by simpa using hKN)
    exact hquot.of_equiv ((QuotientGroup.quotientKerEquivOfSurjective g hg).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))
  · exact (hres.of_surjective (f.subgroupMap (pResidual 2 N))
      (f.subgroupMap_surjective (pResidual 2 N))).of_equiv
      (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 f
        (q.subgroupMap_surjective N)))
  · have he : (Q : Subgroup M).map M.subtype =
        ((P : Subgroup N).map N.subtype).map q := by
      simp only [Q, Sylow.coe_mapSurjective, map_map]
      rfl
    have hg := congrArg (Subgroup.map q) hgen
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective K),
      map_embedded_pResidual] at hg
    apply top_unique
    rw [← hg]
    apply sup_le_sup_left
    rw [he]
    exact map_centralizer_le_centralizer_image _ q

/-- In a two-perfect ambient group, induction on the normal kernel order
reduces GLS II B.5.3 to its ambient chief-kernel case. -/
theorem isPStar_of_extension_of_chief_case (hchief : PStarChiefExtensionCriterion.{u})
    (N : Subgroup G) [N.Normal] (P : Sylow 2 N) (hG : IsPPerfect 2 G)
    (hquot : IsPStar 2 (G ⧸ N)) (hres : IsPStar 2 (pResidual 2 N))
    (hgen : (pResidual 2 N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) : IsPStar 2 G := by
  classical
  generalize hn : Nat.card N = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    let R := (pResidual 2 N).map N.subtype
    by_cases hR : R = ⊥
    · have hr : pResidual 2 N = ⊥ := by
        apply (map_injective N.subtype_injective)
        simpa only [Subgroup.map_bot] using hR
      have hpN : IsPGroup 2 N := (isPGroup_quotient_pResidual (G := N) 2).of_equiv
        ((QuotientGroup.quotientMulEquivOfEq hr).trans QuotientGroup.quotientBot)
      have hP : (P : Subgroup N) = ⊤ := (P.is_maximal' (hpN.to_subgroup ⊤) le_top).symm
      have hc : N ≤ center G := by
        have ht : (P : Subgroup N).map N.subtype = N := by
          rw [hP, ← MonoidHom.range_eq_map, range_subtype]
        change R ⊔ _ = ⊤ at hgen
        rw [hR, bot_sup_eq, ht] at hgen
        exact centralizer_eq_top_iff_subset.mp hgen
      exact isPStar_of_surjective_central_pgroup_kernel hG (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N) (by simpa only [QuotientGroup.ker_mk'] using hc)
        (hpN.of_equiv (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' N)).symm) hquot
    · obtain ⟨K, hK, hKR⟩ := exists_chief_in R hR
      let : K.Normal := hK.normal_upper
      have hKN : K ≤ N := hKR.trans (map_subtype_le _)
      obtain ⟨Q, hqquot, hqres, hqgen⟩ := quotient_hypotheses N K hKN P hquot hres hgen
      have hcard : Nat.card (N.map (QuotientGroup.mk' K)) < n := by
        rw [← hn]
        exact quotient_kernel_card_lt N K hKN hK.lt.ne'
      have hbar : IsPStar 2 (G ⧸ K) := ih _ hcard (N.map (QuotientGroup.mk' K)) Q
        (hG.of_surjective (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K))
        hqquot hqres hqgen rfl
      obtain ⟨S, hSP⟩ := sylow_restrict N K hKN P
      have hRstar : IsPStar 2 R := hres.of_equiv
        ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective)
      have hs : K ⊔ centralizer ((S : Subgroup K).map K.subtype : Set G) = ⊤ := by
        apply top_unique
        rw [← hgen]
        exact sup_le (supplement_inside R K hRstar hKR S)
          ((centralizer_le hSP).trans le_sup_right)
      exact hchief G K hK S hG hbar hs

/-- GLS II B.5.3 for p = 2, conditional only on its universal chief-kernel case.
The conclusion concerns the ambient residual; the ambient group need not be
two-perfect. -/
theorem isPStar_pResidual_of_extension_of_chief_case
    (hchief : PStarChiefExtensionCriterion.{u})
    (N : Subgroup G) [N.Normal] (P : Sylow 2 N)
    (hquot : IsPStar 2 (G ⧸ N)) (hres : IsPStar 2 (pResidual 2 N))
    (hgen : (pResidual 2 N).map N.subtype ⊔ centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar 2 (pResidual 2 G) := by
  let Y := pResidual 2 G
  let R := (pResidual 2 N).map N.subtype
  let C := centralizer ((P : Subgroup N).map N.subtype : Set G)
  let K := N.subgroupOf Y
  let J := Y.subgroupOf N
  have hRY : R ≤ Y := map_pResidual_le 2 N.subtype
  have hYRC : Y ≤ R ⊔ C := by
    rw [show R ⊔ C = ⊤ from hgen]
    exact le_top
  let f : Y →* G ⧸ N := (QuotientGroup.mk' N).comp Y.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    exact (map_pResidual_of_surjective 2 (QuotientGroup.mk' N)
      (QuotientGroup.mk'_surjective N)).trans hquot.1
  have hk : f.ker = K := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hKquot : IsPStar 2 (Y ⧸ K) := hquot.of_equiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))
  let i : K →* N :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hresK : (pResidual 2 K).map K.subtype = R.subgroupOf Y := by
    apply le_antisymm
    · rintro x ⟨k, hk, rfl⟩
      exact mem_map.mpr ⟨i k, map_pResidual_le 2 i (mem_map.mpr ⟨k, hk, rfl⟩), rfl⟩
    · intro x hx
      obtain ⟨n, hn, he⟩ := mem_map.mp hx
      let a : pResidual 2 N := ⟨n, hn⟩
      let j : pResidual 2 N →* K :=
        { toFun := fun n => ⟨⟨n.val.val, hRY (mem_map.mpr ⟨n.val, n.property, rfl⟩)⟩,
            n.val.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have ha : a ∈ pResidual 2 (pResidual 2 N) := by rw [hres.1]; trivial
      have hj : j a ∈ pResidual 2 K := map_pResidual_le 2 j (mem_map.mpr ⟨a, ha, rfl⟩)
      exact mem_map.mpr ⟨j a, hj, Subtype.ext he⟩
  have hKstar : IsPStar 2 (pResidual 2 K) := by
    let eR := (pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective
    let eK := (pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective
    exact (((hres.of_equiv eR).of_equiv (subgroupOfEquivOfLe hRY).symm).of_equiv
      (MulEquiv.subgroupCongr hresK).symm).of_equiv eK.symm
  obtain ⟨S, hS⟩ := P.exists_subgroupOf_eq_of_normal J
  let e : K ≃* J :=
    { toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let Q : Sylow 2 K := S.comapOfInjective e.toMonoidHom e.injective
    (by rw [e.toMonoidHom.range_eq_top_of_surjective e.surjective]; exact le_top)
  have hQ : ∀ k ∈ (Q : Subgroup K), i k ∈ (P : Subgroup N) := by
    intro k hk
    change e k ∈ (S : Subgroup J) at hk
    rw [hS] at hk
    exact hk
  have hstrong : (pResidual 2 K).map K.subtype ⊔
      centralizer ((Q : Subgroup K).map K.subtype : Set Y) = ⊤ := by
    rw [hresK]
    apply top_unique
    intro y _
    obtain ⟨r, hr, c, hc, he⟩ := mem_sup_of_normal_left.mp (hYRC y.property)
    have hcY : c ∈ Y := by
      have h : r⁻¹ * (y : G) ∈ Y := Y.mul_mem (Y.inv_mem (hRY hr)) y.property
      simpa only [← he, inv_mul_cancel_left] using h
    have hcQ : (⟨c, hcY⟩ : Y) ∈ centralizer ((Q : Subgroup K).map K.subtype : Set Y) := by
      rintro z ⟨k, hk, rfl⟩
      apply Subtype.ext
      exact hc (i k : G) (mem_map.mpr ⟨i k, hQ k hk, rfl⟩)
    exact mem_sup_of_normal_left.mpr
      ⟨⟨r, hRY hr⟩, hr, ⟨c, hcY⟩, hcQ, Subtype.ext he⟩
  exact isPStar_of_extension_of_chief_case hchief K Q (isPPerfect_pResidual 2) hKquot hKstar hstrong
end Theory.GroupTheory
