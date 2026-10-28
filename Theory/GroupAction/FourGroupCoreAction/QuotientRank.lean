module

public import Theory.GroupAction.FourGroupCoreAction
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.NormalJoinQuotientProduct
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.Rank
public import Theory.Quasithin.CoprimeRank

/-!
# The quotient of the four-group normalizer

Write `Y = ⟨O₂(C_G(v₁)), O₂(C_G(v₂))⟩`, `C = C_G(V)` and
`M = N_G(V)`.  Once the kernel identity `O₂(Y) = Y ∩ C` is supplied,
the two normal factors give the direct product decomposition of `M/O₂(Y)`.
The rank consequence is the odd-rank calculation in A.1.14(3)--(4).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.1.14, printed p.23.
-/

@[expose] public section
noncomputable section

open Subgroup

namespace FourGroupCorePair

variable {G : Type*} [Group G] [Finite G]
variable {V : Subgroup G} {v₁ v₂ : G}

/- The quotient has the literal multiplication coordinates of the two images. -/
theorem quotient_directProduct
    (h : FourGroupCorePair V v₁ v₂)
    (hkernel : (generated v₁ v₂).pCoreIn 2 =
      generated v₁ v₂ ⊓ centralizer (V : Set G)) :
    let Y := generated v₁ v₂
    let C := centralizer (V : Set G)
    let M := normalizer (V : Set G)
    let P := Y.pCoreIn 2
    let A := Y.subgroupOf M
    let B := C.subgroupOf M
    let Pm := P.subgroupOf M
    let hPnormG : M ≤ normalizer (P : Set G) :=
      h.normalizer_le_normalizer_generated.trans
        (by
          simpa only [Y, P, pCoreIn] using
            (Subgroup.normalizer_le_normalizer_characteristic_image
              Y (pCore 2 Y)))
    letI : Pm.Normal := normal_subgroupOf_of_le_normalizer hPnormG
    let q : M →* (M ⧸ Pm) := QuotientGroup.mk' Pm
    ∃ e : A.map q × B.map q ≃* (M ⧸ Pm),
      ∀ a b, (e (a, b) : M ⧸ Pm) = (a : M ⧸ Pm) * (b : M ⧸ Pm) := by
  let Y := generated v₁ v₂
  let C := centralizer (V : Set G)
  let M := normalizer (V : Set G)
  let P := Y.pCoreIn 2
  let A := Y.subgroupOf M
  let B := C.subgroupOf M
  let Pm := P.subgroupOf M
  have hYM : Y ≤ M := by exact h.generated_le_normalizer
  have hCM : C ≤ M := centralizer_le_normalizer _
  have hPM : P ≤ M := (pCoreIn_le 2 Y).trans hYM
  have hPm : Pm = A ⊓ B := by
    ext x
    change (x : G) ∈ P ↔ (x : G) ∈ Y ∧ (x : G) ∈ C
    have hkernel' : P = Y ⊓ C := by simpa [Y, C, P] using hkernel
    rw [hkernel']
    rfl
  have hPnormG : M ≤ normalizer (P : Set G) := by
    have hchar := Subgroup.normalizer_le_normalizer_characteristic_image
      Y (pCore 2 Y)
    simpa only [Y, P, pCoreIn] using h.normalizer_le_normalizer_generated.trans hchar
  let _ : Pm.Normal := normal_subgroupOf_of_le_normalizer hPnormG
  let _ : A.Normal := h.generated_normal
  let _ : B.Normal := inferInstance
  let q : M →* (M ⧸ Pm) := QuotientGroup.mk' Pm
  have hsup : A ⊔ B = ⊤ := by
    have hs := congrArg (fun K : Subgroup G => K.subgroupOf M)
      (show M = Y ⊔ C by simpa [M, Y, C] using h.normalizer_eq_sup_centralizer)
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hYM hCM] at hs
    simpa only [A, B] using hs.symm
  obtain ⟨_, e₀, he₀⟩ := Subgroup.normal_join_image_direct_product q A B
    (by
      simp [q, hPm])
  have htop : (A ⊔ B).map q = (⊤ : Subgroup (M ⧸ Pm)) := by
    rw [hsup, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective q (QuotientGroup.mk'_surjective Pm)
  let e : A.map q × B.map q ≃* (M ⧸ Pm) :=
    e₀.trans ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  refine ⟨e, ?_⟩
  intro a b
  exact he₀ a b

/- The odd rank of the centralizer section is at most one. -/
theorem primeRank_three_centralizer_quotient_le_one
    (h : FourGroupCorePair V v₁ v₂)
    (hkernel : (generated v₁ v₂).pCoreIn 2 =
      generated v₁ v₂ ⊓ centralizer (V : Set G))
    (hG : IsQuasithin G) :
    let Y := generated v₁ v₂
    let C := centralizer (V : Set G)
    let M := normalizer (V : Set G)
    let P := Y.pCoreIn 2
    let PC := P.subgroupOf C
    let hPnormG : M ≤ normalizer (P : Set G) :=
      h.normalizer_le_normalizer_generated.trans
        (by
          simpa only [Y, P, pCoreIn] using
            (Subgroup.normalizer_le_normalizer_characteristic_image
              Y (pCore 2 Y)))
    let hPnormC : C ≤ normalizer (P : Set G) :=
      (centralizer_le_normalizer (V : Set G)).trans hPnormG
    letI : PC.Normal := normal_subgroupOf_of_le_normalizer hPnormC
    primeRank 3 C ≤ 1 := by
  dsimp
  let Y := generated v₁ v₂
  let C := centralizer (V : Set G)
  let M := normalizer (V : Set G)
  let P := Y.pCoreIn 2
  let PC := P.subgroupOf C
  have hYM : Y ≤ M := h.generated_le_normalizer
  have hCM : C ≤ M := centralizer_le_normalizer _
  have hPM : P ≤ M := (pCoreIn_le 2 Y).trans hYM
  have hkernel' : P = Y ⊓ C := by simpa [Y, C, P] using hkernel
  have hPnormG : M ≤ normalizer (P : Set G) := by
    have hchar := Subgroup.normalizer_le_normalizer_characteristic_image
      Y (pCore 2 Y)
    simpa only [Y, P, pCoreIn] using h.normalizer_le_normalizer_generated.trans hchar
  let _ : PC.Normal := normal_subgroupOf_of_le_normalizer (hCM.trans hPnormG)
  let Pm := P.subgroupOf M
  let _ : Pm.Normal := normal_subgroupOf_of_le_normalizer hPnormG
  let _ : IsKleinFour V := h.four
  let _ := Fintype.ofFinite V
  have hVne : V ≠ ⊥ := by
    intro hV
    have hc := IsKleinFour.card_four (G := V)
    rw [hV] at hc
    simp at hc
  have hVtwo : IsPGroup 2 V := by
    exact IsPGroup.of_card (n := 2) (by
      rw [IsKleinFour.card_four]
      norm_num)
  have hMlocal : IsTwoLocal M := ⟨V, hVne, hVtwo, rfl⟩
  have hMrank : primeRank 3 M ≤ 2 := by
    exact isQuasithin_iff_twoLocal.mp hG M hMlocal 3 Nat.prime_three (by decide)
  have hPtwo : IsPGroup 2 P := isPGroup_pCoreIn 2 Y
  have hPm : Pm = (Y.subgroupOf M) ⊓ (C.subgroupOf M) := by
    ext x
    change (x : G) ∈ P ↔ (x : G) ∈ Y ∧ (x : G) ∈ C
    rw [hkernel']
    rfl
  have hPmtwo : IsPGroup 2 Pm := by
    exact hPtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  let q : M →* (M ⧸ Pm) := QuotientGroup.mk' Pm
  have hquotrank : primeRank 3 (M ⧸ Pm) ≤ primeRank 3 M :=
    primeRank_quotient_le_of_isTwoGroup 3 (by decide) Pm hPmtwo
  obtain ⟨eM, heM⟩ := h.quotient_directProduct hkernel
  have hArank : primeRank 3 ((Y.subgroupOf M).map q) = 1 := by
    let iY : Y →* M := Subgroup.inclusion hYM
    let qY : Y →* (M ⧸ Pm) := q.comp iY
    have hqYker : qY.ker = pCore 2 Y := by
      ext y
      change q (iY y) = 1 ↔ y ∈ pCore 2 Y
      change ((iY y : M) : M ⧸ Pm) = 1 ↔ y ∈ pCore 2 Y
      rw [QuotientGroup.eq_one_iff]
      change (y : G) ∈ P ↔ y ∈ pCore 2 Y
      constructor
      · intro hy
        have hy' : (y : G) ∈ (pCore 2 Y).map Y.subtype := by
          simpa [P, pCoreIn] using hy
        obtain ⟨z, hz, hzy⟩ := (Subgroup.mem_map.mp hy')
        have : z = y := Subtype.ext hzy
        simpa [this] using hz
      · intro hy
        simpa [P, pCoreIn] using Subgroup.mem_map_of_mem Y.subtype hy
    let qYbar : Y →* ((Y.subgroupOf M).map q) :=
      qY.codRestrict ((Y.subgroupOf M).map q) (fun y => by
        apply Subgroup.mem_map_of_mem q
        exact y.property)
    have hqYbar_surj : Function.Surjective qYbar := by
      intro a
      obtain ⟨a', ha', hqa⟩ := Subgroup.mem_map.mp a.property
      let y : Y := ⟨(a' : G), ha'⟩
      refine ⟨y, ?_⟩
      apply Subtype.ext
      exact hqa
    have hqYbarker : qYbar.ker = pCore 2 Y := by
      rw [MonoidHom.ker_codRestrict]
      exact hqYker
    let eY : Y ⧸ pCore 2 Y ≃* (Y.subgroupOf M).map q :=
      (QuotientGroup.quotientMulEquivOfEq hqYbarker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective qYbar hqYbar_surj)
    have hActionKer : h.action.ker = pCore 2 Y := by
      have hsub : (centralizer (V : Set G)).subgroupOf Y = pCore 2 Y := by
        refine (Subgroup.map_injective (f := Y.subtype) Y.subtype_injective) ?_
        calc
          ((centralizer (V : Set G)).subgroupOf Y).map Y.subtype =
              centralizer (V : Set G) ⊓ Y :=
            Subgroup.subgroupOf_map_subtype _ _
          _ = Y ⊓ C := by rw [inf_comm]
          _ = P := hkernel'.symm
          _ = (pCore 2 Y).map Y.subtype := by rfl
      calc
        h.action.ker = (centralizer (V : Set G)).subgroupOf Y := h.action_ker
        _ = pCore 2 Y := hsub
    let eAction : Y ⧸ pCore 2 Y ≃* MulAut V :=
      (QuotientGroup.quotientMulEquivOfEq hActionKer.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective h.action h.action_surjective)
    have hSylow : ∃ S : Sylow 3 (MulAut V), Nat.card S = 3 := by
      let S : Sylow 3 (MulAut V) :=
        Classical.choice (inferInstance : Nonempty (Sylow 3 (MulAut V)))
      refine ⟨S, ?_⟩
      rw [Sylow.card_eq_multiplicity, IsKleinFour.card_mulAut]
      have hp : padicValNat 3 6 = 1 := by
        rw [show 6 = 3 * 2 by norm_num,
          padicValNat_base_mul (by norm_num) (by norm_num)]
        rw [padicValNat.eq_zero_of_not_dvd]
        norm_num
      rw [Nat.factorization_def 6 Nat.prime_three, hp]
      norm_num
    obtain ⟨S, hScard⟩ := hSylow
    let _ : IsCyclic S := isCyclic_of_prime_card hScard
    have hupper : primeRank 3 (MulAut V) ≤ 1 :=
      S.primeRank_le_one_of_isCyclic inferInstance
    let _ : IsMulCommutative S := (inferInstance : IsCyclic S).isMulCommutative
    let _ : IsElementaryAbelian 3 S := by
      refine ⟨?_⟩
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply orderOf_dvd_iff_pow_eq_one.mp
      have ho : orderOf x ∣ Nat.card S := orderOf_dvd_natCard x
      rw [hScard] at ho
      exact ho
    have hlower : 1 ≤ primeRank 3 (MulAut V) := by
      apply IsElementaryAbelian.primeRank_ge_of_card S
      rw [hScard]
      norm_num
    have hAutrank : primeRank 3 (MulAut V) = 1 := Nat.le_antisymm hupper hlower
    calc
      primeRank 3 ((Y.subgroupOf M).map q) = primeRank 3 (Y ⧸ pCore 2 Y) :=
        (primeRank_congr 3 eY).symm
      _ = primeRank 3 (MulAut V) := primeRank_congr 3 eAction
      _ = 1 := hAutrank
  have hBrank : primeRank 3 ((C.subgroupOf M).map q) ≤ 1 := by
    have hsum : primeRank 3 ((Y.subgroupOf M).map q) +
        primeRank 3 ((C.subgroupOf M).map q) = primeRank 3 (M ⧸ Pm) := by
      calc
        _ = primeRank 3 (((Y.subgroupOf M).map q) × ((C.subgroupOf M).map q)) :=
          (primeRank_prod_eq_add 3).symm
        _ = primeRank 3 (M ⧸ Pm) := primeRank_congr 3 eM
    omega
  have hPC : P ≤ C := by
    rw [hkernel']
    exact inf_le_right
  have hPCtwo : IsPGroup 2 PC := by
    exact hPtwo.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  let iC : C →* M := Subgroup.inclusion hCM
  let qC : C →* (M ⧸ Pm) := q.comp iC
  have hqCker : qC.ker = PC := by
    ext c
    change ((iC c : M) : M ⧸ Pm) = 1 ↔ c ∈ PC
    rw [QuotientGroup.eq_one_iff]
    change (c : G) ∈ P ↔ (c : G) ∈ P
    rfl
  let qCbar : C →* ((C.subgroupOf M).map q) :=
    qC.codRestrict ((C.subgroupOf M).map q) (fun c => by
      apply Subgroup.mem_map_of_mem q
      exact c.property)
  have hqCbar_surj : Function.Surjective qCbar := by
    intro b
    obtain ⟨m, hm, hqm⟩ := Subgroup.mem_map.mp b.property
    let c : C := ⟨(m : G), hm⟩
    refine ⟨c, ?_⟩
    apply Subtype.ext
    exact hqm
  have hqCbarker : qCbar.ker = PC := by
    rw [MonoidHom.ker_codRestrict]
    exact hqCker
  let eC : C ⧸ PC ≃* (C.subgroupOf M).map q :=
    (QuotientGroup.quotientMulEquivOfEq hqCbarker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective qCbar hqCbar_surj)
  have hCquot : primeRank 3 (C ⧸ PC) ≤ 1 := by
    rw [primeRank_congr 3 eC]
    exact hBrank
  have hCeq : primeRank 3 (C ⧸ PC) = primeRank 3 C :=
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) PC hPCtwo
  rw [hCeq] at hCquot
  exact hCquot

end FourGroupCorePair

end
