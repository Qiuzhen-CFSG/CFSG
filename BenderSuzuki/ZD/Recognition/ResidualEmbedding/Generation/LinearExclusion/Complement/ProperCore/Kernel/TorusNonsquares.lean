module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.Kernel.Reduction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.ProperCore.LocalControl
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.ProperModels.LocalStructure.LinearBorel
public import Theory.GroupAction.CoprimeQuotientTransitivity
public import Theory.GroupTheory.ConjugateInvolutionNonsquares

/-!
# Torus orbits and nonsquares above the linear centralizer closure

Write `A = M°`, `J = C_G(L)`, `K = D ∩ L`, `V = O₂(M)` and
`R = ⟨Jᴹ⟩`, all viewed inside `M`. Given the abelian index-two base
`B ≤ R`, its noninvolution profile makes it normal in `M`.

Localization `C_V(J) ≤ AJ` makes this centralizer elementary abelian
of order at most `2q`. The supplement `M = DV`, the fixed-point
identity and the source order formula give `|V| = 2q³`. Orbit-stabilizer
therefore fills `R ∖ B` with the conjugates of the nonidentity element
of `J`, excluding squares throughout that coset.

Every nonidentity torus element has centralizer `J` in `V` by the
nilpotent normalizer argument in `LocalControl`. Coprime fixed-point
lifting makes its action on `V/R` free away from the identity. Since
`|V/R| = q = |K| + 1`, the action is transitive there. The final theorem
feeds these literal coset and nonsquare facts to the existing kernel
reduction. This route uses the actual normal closure throughout and
needs no identification with the intermediate normalizer `R₁`.

Three earlier-source premises remain explicit: involution-centralizer
localization, the action of the torus on `A`, and the order of `M`.
Their source producers must be assembled before the original task is
complete. Neither fusion nor an elementary quotient is assumed here.
Source: GLS, Volume 4, Chapter 2, Lemmas 15.6–15.7,
`refs/KGroup/GLS4/Chapter2.tex`, lines 2703–2750.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Subgroup Theory.GroupTheory

private theorem twoCore_card_of_supplement
    {H : Type*} [Group H] [Finite H] (D V J : Subgroup H) [V.Normal]
    (hDV : D ⊔ V = ⊤) (hinter : D ⊓ V = J) (hJ : Nat.card J = 2)
    {q : ℕ} (hH : Nat.card H = q ^ 3 * Nat.card D) : Nat.card V = 2 * q ^ 3 := by
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes V D le_normalizer_of_normal
  rw [inf_comm V D, hinter, hJ, sup_comm V D, hDV, Nat.card_congr (topEquiv : (⊤ : Subgroup H) ≃* H).toEquiv, hH] at hp
  have hd : 0 < Nat.card D := Nat.card_pos
  nlinarith

private theorem nonsquares_of_localization
    {H : Type*} [Group H] [Finite H] (V R B A J : Subgroup H)
    [V.Normal] [R.Normal] [B.Normal] [A.Normal]
    (hRV : R ≤ V) (hBR : B ≤ R) (hi : B.relIndex R = 2)
    (hJR : J ≤ R) (hdis : Disjoint B J) (hJ : Nat.card J = 2)
    {q : ℕ} (hq : 0 < q) (hV : Nat.card V = 2 * q ^ 3)
    (hR : Nat.card R = 2 * q ^ 2) (hA : Nat.card A = q)
    (hAsq : ∀ a ∈ A, a ^ 2 = 1) (hAJ : ∀ a ∈ A, ∀ j ∈ J, Commute a j)
    (hloc : V ⊓ centralizer (J : Set H) ≤ A ⊔ J) :
    ∀ v ∈ V, v ^ 2 ∈ R → v ^ 2 ∈ B := by
  obtain ⟨u, hu1, huniq⟩ := (Nat.card_eq_two_iff' (1 : J)).mp hJ
  let uV : V := ⟨u, hRV (hJR u.property)⟩
  have huB : (u : H) ∉ B := by
    intro huB
    exact hu1 (Subtype.ext (Subgroup.disjoint_def.mp hdis huB u.property))
  have hC : ∀ x ∈ centralizer ({uV} : Set V), (x : H) ∈ A ⊔ J := by
    intro x hx
    apply hloc
    refine ⟨x.property, ?_⟩
    intro j hj
    by_cases hj1 : j = 1
    · simp [hj1]
    have hju : (⟨j, hj⟩ : J) = u := huniq _ (fun he => hj1 (congrArg Subtype.val he))
    have he := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hx)
    change (x : H) * (u : H) = (u : H) * x at he
    rw [show j = (u : H) from congrArg Subtype.val hju]
    exact he.symm
  have hCc : Nat.card (centralizer ({uV} : Set V)) ≤ 2 * q := by
    let f : centralizer ({uV} : Set V) → (A ⊔ J : Subgroup H) :=
      fun x => ⟨x.val, hC x.val x.property⟩
    have hf : Function.Injective f := by
      intro x y hxy
      have he : (x.val : H) = (y.val : H) :=
        congrArg (fun a : (A ⊔ J : Subgroup H) => (a : H)) hxy
      exact Subtype.ext (Subtype.ext he)
    have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes A J le_normalizer_of_normal
    have hp1 : 1 ≤ Nat.card (A ⊓ J : Subgroup H) := Nat.card_pos
    have hb : Nat.card (A ⊔ J : Subgroup H) ≤ 2 * q := by
      rw [hA, hJ] at hp
      nlinarith
    exact (Nat.card_le_card_of_injective f hf).trans hb
  have hCsq : ∀ x ∈ centralizer ({uV} : Set V), x ^ 2 = 1 := by
    intro x hx
    obtain ⟨a, ha, j, hj, hxaj⟩ := mem_sup_of_normal_left.mp (hC x hx)
    apply Subtype.ext
    change (x : H) ^ 2 = 1
    rw [← hxaj, (hAJ a ha j hj).mul_pow, hAsq a ha, one_mul]
    have hh := pow_card_eq_one' (x := (⟨j, hj⟩ : J))
    rw [hJ] at hh
    exact congrArg Subtype.val hh
  have hRv : Nat.card (R.subgroupOf V) = 2 * q ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRV).toEquiv).trans hR
  have hiv : (B.subgroupOf V).relIndex (R.subgroupOf V) = 2 := by
    rw [relIndex_subgroupOf hRV, hi]
  intro v hv hvR
  have hh := squares_mem_of_index_two_of_centralizer_bound (R.subgroupOf V) (B.subgroupOf V)
    (Subgroup.comap_mono hBR) hiv hq hRv hV uV (hJR u.property) huB hCc hCsq ⟨v, hv⟩ hvR
  exact hh

/-- The literal torus is transitive above the actual normal closure, and its
outside involutions are not squares, once the earlier source localization,
order and root-group action facts have been supplied. -/
public theorem linear_torus_nonsquares_of_localization_and_orders
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hfixed : pCore 2 M ⊓ centralizer
      (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (B : Subgroup M) (hBR : B ≤ linearCentralizerClosure M z t)
    (hindex : B.relIndex (linearCentralizerClosure M z t) = 2)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hnon : ∃ b ∈ B, b ^ 2 ≠ 1)
    (hout : ∀ x ∈ linearCentralizerClosure M z t, x ∉ B → x ^ 2 = 1)
    (hdis : Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M))
    (hlocal : pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓ centralizer ({k} : Set M) = ⊥)
    (hMcard : Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t)) :
    (∀ v ∈ pCore 2 M, v ^ 2 ∈ linearCentralizerClosure M z t → v ^ 2 ∈ B) ∧
      (∀ v ∈ pCore 2 M, v ∉ linearCentralizerClosure M z t →
        ∀ w ∈ pCore 2 M, w ∉ linearCentralizerClosure M z t →
        ∃ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
          ∃ a ∈ linearCentralizerClosure M z t, w = k * v * k⁻¹ * a) := by
  let V := pCore 2 M
  let R := linearCentralizerClosure M z t
  let D := (residualPairStabilizer M t).subgroupOf M
  let K := (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M
  let J := (centralizer (residualGenerated M z t : Set G)).subgroupOf M
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : R.Normal := Subgroup.normalClosure_normal
  let : B.Normal := normal_of_noninvolution_profile R B hBR hcomm hnon hout
  let : A.Normal := distinguishedClosure_normal h
  have hRV : R ≤ V := linearCentralizerClosure_le_twoCore hR
  have hJc : Nat.card J = 2 := linearCentralizer_subgroupOf_card h hz hzM hJ
  have hDi : D ⊓ V = J := linear_pair_inf_twoCore_eq_of_fixed_centralizer
    h r hz hzM ht htM hL (linear_pair_le_normalizer_inter_of_normalizes hDN) hfixed
  have hDc : Nat.card D = Nat.card (residualPairStabilizer M t) :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have hVc : Nat.card V = 2 * (2 ^ n) ^ 3 :=
    twoCore_card_of_supplement D V J hDV hDi hJc (by simpa only [hDc] using hMcard)
  have hAc := psl2_distinguishedClosure_elementary_card h r hz hzM ht htM hL ⟨e⟩ hn hAL
  have hAcM : Nat.card A = 2 ^ n :=
    (Nat.card_congr (subgroupOfEquivOfLe distinguishedClosure_le).toEquiv).trans hAc.2
  have hKc : Nat.card K = 2 ^ n - 1 :=
    (Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv).trans
      (psl2_local_pair_cyclic_card h r hz hzM ht htM hL hn ⟨e⟩).2
  have hq : 0 < 2 ^ n := pow_pos (by decide) _
  constructor
  · apply nonsquares_of_localization V R B A J hRV hBR hindex subset_normalClosure hdis hJc
      hq hVc hR hAcM _ _ hlocal
    · intro a ha
      apply Subtype.ext
      let : IsElementaryAbelian 2 (closure (Z ∩ (M : Set G))) := hAc.1
      exact elemPow_eq_one_of_isElementaryAbelian
        (A := closure (Z ∩ (M : Set G))) (a : G) ha
    · intro a ha j hj
      apply Subtype.ext
      exact mem_centralizer_iff.mp hj a (hAL ha)
  · have helement := linear_twoCore_element_centralizer_of_localization h hz hzM hJ hR hlocal hAfixed
    have hInv : IsInvariant K V (R.subgroupOf V) := by
      constructor
      intro k v
      change (v : M) ∈ R ↔ (k : M) * (v : M) * (k : M)⁻¹ ∈ R
      exact mem_normalizer_iff.mp
        (show (k : M) ∈ normalizer (R : Set M) from le_normalizer_of_normal (mem_top _)) v
    have hVp : IsPGroup 2 V := pCore_isPGroup
    let : Group.IsNilpotent V := hVp.isNilpotent
    have hodd : Odd (Nat.card K) := by
      have hc : Nat.card K = Nat.card
          (residualPairStabilizer M t ⊓ residualGenerated M z t : Subgroup G) :=
        Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans inf_le_left)).toEquiv
      rw [hc]
      exact pair_inf_proper_residualGenerated_odd h r hz hzM ht htM hL
    have hcop : Nat.Coprime (Nat.card K) (Nat.card V) := by
      obtain ⟨m, hm⟩ := hVp.exists_card_eq
      rw [hm]
      exact hodd.coprime_two_right.pow_right m
    have hQc : Nat.card (V ⧸ R.subgroupOf V) = Nat.card K + 1 := by
      have hc := (R.subgroupOf V).card_mul_index
      rw [index_eq_card, Nat.card_congr (subgroupOfEquivOfLe hRV).toEquiv, hR, hVc] at hc
      have hh : Nat.card (V ⧸ R.subgroupOf V) = 2 ^ n := by
        have hp : 0 < 2 * (2 ^ n) ^ 2 := by positivity
        apply (Nat.mul_left_cancel_iff hp).mp
        calc
          (2 * (2 ^ n) ^ 2) * Nat.card (V ⧸ R.subgroupOf V) = 2 * (2 ^ n) ^ 3 := hc
          _ = (2 * (2 ^ n) ^ 2) * 2 ^ n := by ring
      rw [hh, hKc]
      omega
    have hf : ∀ k : K, k ≠ 1 → ∀ v : V, k • v = v → v ∈ R.subgroupOf V := by
      intro k hk v hv
      have hkn : (k : M) ≠ 1 := fun hh => hk (Subtype.ext hh)
      have hvC : (v : M) ∈ centralizer ({(k : M)} : Set M) := by
        apply mem_centralizer_singleton_iff.mpr
        have hh := congrArg Subtype.val hv
        change (k : M) * (v : M) * (k : M)⁻¹ = v at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm
      have hvJ : (v : M) ∈ J := by
        change (v : M) ∈ (centralizer (residualGenerated M z t : Set G)).subgroupOf M
        rw [← helement k k.property hkn]
        exact ⟨v.property, hvC⟩
      exact (show J ≤ R from subset_normalClosure) hvJ
    let : MulDistribMulAction K (V ⧸ R.subgroupOf V) := quotientMulDistribMulAction _ hInv
    let qV := QuotientGroup.mk' (R.subgroupOf V)
    intro v hv hvR w hw hwR
    have hvr : qV ⟨v, hv⟩ ≠ 1 := fun hh => hvR ((QuotientGroup.eq_one_iff (⟨v, hv⟩ : V)).mp hh)
    have hwr : qV ⟨w, hw⟩ ≠ 1 := fun hh => hwR ((QuotientGroup.eq_one_iff (⟨w, hw⟩ : V)).mp hh)
    obtain ⟨k, hk⟩ := Theory.GroupAction.transitive_nonidentity_quotient_of_fixed_le
      (R.subgroupOf V) hInv inferInstance hcop hf hQc _ hvr _ hwr
    have hmk : qV (k • (⟨v, hv⟩ : V)) = qV ⟨w, hw⟩ :=
      (MulAction.Quotient.smul_coe _ k _).symm.trans hk
    have ha : (k • (⟨v, hv⟩ : V))⁻¹ * (⟨w, hw⟩ : V) ∈ R.subgroupOf V := by
      apply (QuotientGroup.eq_one_iff _).mp
      change qV ((k • (⟨v, hv⟩ : V))⁻¹ * (⟨w, hw⟩ : V)) = 1
      rw [map_mul, map_inv, hmk, inv_mul_cancel]
    refine ⟨k, k.property, ((k : M) * v * (k : M)⁻¹)⁻¹ * w, ha, ?_⟩
    group

/-- Apply the localization, order and root-group action route to the literal
commutator kernel. The three earlier-source inputs remain explicit; this
is not the completed source Lemma 15.7. -/
public theorem linearCommutatorKernel_properties_of_localization_and_orders
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {z t : G} (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤) {n : ℕ} (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hproper : linearCentralizerClosure M z t < pCore 2 M)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (hDN : residualPairStabilizer M t ≤ normalizer (residualGenerated M z t : Set G))
    (hDV : (residualPairStabilizer M t).subgroupOf M ⊔ pCore 2 M = ⊤)
    (hfixed : pCore 2 M ⊓ centralizer
      (((residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M) : Set M) =
      (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (B : Subgroup M) (hBR : B ≤ linearCentralizerClosure M z t)
    (hindex : B.relIndex (linearCentralizerClosure M z t) = 2)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, Commute x y)
    (hnon : ∃ b ∈ B, b ^ 2 ≠ 1)
    (hout : ∀ x ∈ linearCentralizerClosure M z t, x ∉ B → x ^ 2 = 1)
    (hdis : Disjoint B ((centralizer (residualGenerated M z t : Set G)).subgroupOf M))
    (hlocal : pCore 2 M ⊓
      centralizer ((centralizer (residualGenerated M z t : Set G)).subgroupOf M : Set M) ≤
      (closure (Z ∩ (M : Set G))).subgroupOf M ⊔
        (centralizer (residualGenerated M z t : Set G)).subgroupOf M)
    (hAfixed : ∀ k ∈ (residualPairStabilizer M t ⊓ residualGenerated M z t).subgroupOf M,
      k ≠ 1 → (closure (Z ∩ (M : Set G))).subgroupOf M ⊓ centralizer ({k} : Set M) = ⊥)
    (hMcard : Nat.card M = (2 ^ n) ^ 3 * Nat.card (residualPairStabilizer M t)) :
    (linearCommutatorKernel M z t).Normal ∧
      ⁅pCore 2 M, pCore 2 M⁆ ≤ linearCommutatorKernel M z t ∧
      Disjoint (linearCommutatorKernel M z t)
        ((centralizer (residualGenerated M z t : Set G)).subgroupOf M) := by
  obtain ⟨hno, htrans⟩ := linear_torus_nonsquares_of_localization_and_orders
    h r hz hzM ht htM hL hn e hJ hR hAL hDN hDV hfixed
    B hBR hindex hcomm hnon hout hdis hlocal hAfixed hMcard
  exact linearCommutatorKernel_properties_of_torus_and_nonsquares
    h r hz hzM ht htM hL hR hproper hfixed B hBR hindex hcomm hnon hout hdis hno htrans

end BenderSuzuki.ZD
