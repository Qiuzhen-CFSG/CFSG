module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.LocalRecognition.FixedSize
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Counts.Models

/-!
# The centralizer quotient and its two-point factorization

For an involution `v` in the residual pair stabilizer, put `F = Lᵥ` and
`A = ⟨Z ∩ M⟩`. The fixed distinguished subgroup has order at least four,
so coprime four-group action puts the odd core of F in `M ∩ F`. The
residual action centralizes this core. Theorem SE inside the proper local
group identifies the literal odd-core quotient and its Borel; the three
concrete Borel involution counts identify the field parameter with
`|A ∩ C_G(v)|`, including the actual unitary fixed-field convention.

Frattini's argument identifies the F-orbit with the full centralizer orbit.
Fusion control in M supplies an element of `C_G(v)` taking the base coset
to the original coset `tM`. The Borel action is doubly transitive on this
orbit, giving the factorization by the original `D ∩ C_G(v)`.

The local arguments adapt `LocalResidual/NormalComplements/RankOne/
LocalRecognition/{Center,Model,Counts}.lean` without its conflicting Pair
ancestry. Only the independent concrete model-count module is imported.
All normality used in Frattini's argument is relative to the centralizer.

Source: GLS4, Chapter 2, Lemma 12.4(c,e), Corollary 7.13 and Lemma 4.2,
`refs/KGroup/GLS4/Chapter2.tex`; the counts use Chapter 4, Lemma 3.2(b).
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1 Subgroup
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem qf_oddCore_le_of_twoRank {H : Type*} [Group H] [Finite H]
    {Y : Subgroup H} (hs : IsStronglyEmbedded Y) (hrank : TwoRankAtLeastTwo Y) :
    pPrimeCore 2 H ≤ Y := by
  obtain ⟨E, hEcard, hEsq⟩ := TwoRankAtLeastTwo.exists_subgroup hrank
  let U := E.map Y.subtype
  have hUY : U ≤ Y := Subgroup.map_subtype_le E
  have hUcard : Nat.card U = 4 := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hEcard
  have hUsq : ∀ u : U, u ^ 2 = 1 := by
    intro u
    obtain ⟨e, he, heq⟩ := u.property
    apply Subtype.ext
    change (u : H) ^ 2 = 1
    rw [← heq]
    exact congrArg Y.subtype (congrArg E.subtype (hEsq ⟨e, he⟩))
  apply fourGroup_odd_subgroup_le_stronglyEmbedded hs hUY hUcard hUsq
  · rw [Subgroup.normalizer_eq_top]
    exact le_top
  · exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

private theorem qf_rank
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    TwoRankAtLeastTwo (M.comap (centralizerClosure Z v).subtype) := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let A := closure (Z ∩ (M : Set G))
  let C := A ⊓ centralizer ({v} : Set G)
  let F := centralizerClosure Z v
  let B := M.comap F.subtype
  let : IsElementaryAbelian 2 A := hA
  have hCF : C ≤ F := by
    change closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) ≤ centralizerClosure Z v
    rw [← proper_distinguished_centralizer_trace h r ha hz hzM ht htM hL heven v]
    exact closure_mono (fun _ hx => ⟨hx.1, hx.2.2⟩)
  let f : C →* B := {
    toFun x := ⟨⟨x, hCF x.property⟩, distinguishedClosure_le (Z := Z) (M := M) x.property.1⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun x : B => ((x : F) : G)) he)
  obtain ⟨k, hk, hkc⟩ := proper_pair_involution_fixed_exponent h r ha hz hzM ht htM hL heven hvD hv
  have hd : 2 ^ 2 ∣ Nat.card C := by rw [hkc]; exact pow_dvd_pow 2 hk
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 hd
  have hr : TwoRankAtLeastTwo C := by
    refine ⟨E, hE, ?_⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.val.property.1
  exact hr.map_of_injective f hf

private theorem qf_recognition {F : Subgroup G}
    (hs : IsStronglyEmbedded (M.comap F.subtype))
    (hgen : involutionCore F = ⊤)
    (hNB : pPrimeCore 2 F ≤ M.comap F.subtype) :
    IsSimpleBenderGroup (F ⧸ pPrimeCore 2 F) ∧
      IsBorelSubgroup ((M.comap F.subtype).map
        (QuotientGroup.mk' (pPrimeCore 2 F))) := by
  let N := pPrimeCore 2 F
  let B := M.comap F.subtype
  let BQ := B.map (QuotientGroup.mk' N)
  have hodd : Odd (Nat.card N) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hsQ : IsStronglyEmbedded BQ := hs.map_quotient_of_odd_kernel hNB hodd
  have hsimple : IsSimpleGroup (F ⧸ N) := hs.isSimpleGroup_quotient_twoPrimeCore hgen
  have hgenQ : involutionCore (F ⧸ N) = ⊤ := hsQ.involutionCore_eq_top_of_isSimple hsimple
  have hrQ : TwoRankAtLeastTwo (F ⧸ N) := simpleStronglyEmbeddedRankTwo BQ hsimple hsQ
  let e : (F ⧸ N) ≃* involutionCore (F ⧸ N) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hgenQ).symm
  have hr := hrQ.map_of_injective e.toMonoidHom e.injective
  exact recognition_borel_of_simple_theoremSEBenderConclusion BQ hsQ hsimple
    ((theorem_SE BQ hsQ).resolve_left (not_not.mpr hr))

private theorem qf_center
    (ha : ResidualAction Z M) (F : Subgroup G)
    (hs : IsStronglyEmbedded (M.comap F.subtype))
    (hgen : involutionCore F = ⊤)
    (hinv : ∀ x : F, PFAppendixIII.IsInvolution x → (x : G) ∈ Z)
    (hNB : pPrimeCore 2 F ≤ M.comap F.subtype) :
    pPrimeCore 2 F = center F := by
  let N := pPrimeCore 2 F
  let W := N.map F.subtype
  have hWM : W ≤ M := (map_le_iff_le_comap).mpr hNB
  have hWsub : W.subgroupOf F = N := comap_map_eq_self_of_injective Subtype.val_injective _
  have hWnormal : (W.subgroupOf F).Normal := by rw [hWsub]; infer_instance
  have hFN : F ≤ normalizer (W : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le N)).mp hWnormal
  obtain ⟨x, hxM, hx⟩ := hs.exists_involution
  have hodd : Odd (Nat.card W) := by
    rw [card_map_of_injective F.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcentral : W ≤ centralizer ({(x : G)} : Set G) := by
    rcases ha.odd_normalizer x (hinv x hx) hxM W hodd hWM (hFN x.property) with hc | hfix
    · exact hc
    · exfalso
      apply hs.ne_top
      apply top_unique
      intro g _
      have hbeta : W ≤ MulAction.stabilizer G (QuotientGroup.mk (g : G) : G ⧸ M) := by
        rw [conjugateCoset_stabilizer]
        intro w hw
        rw [rightConjugate, Subgroup.conjBy, mem_map]
        have hgn := (normalizer (W : Set G)).inv_mem (hFN g.property)
        have hw' : (g : G)⁻¹ * w * g ∈ W := by
          simpa only [inv_inv] using (mem_normalizer_iff.mp hgn w).mp hw
        exact ⟨(g : G)⁻¹ * w * g, hWM hw', by simp [mul_assoc]⟩
      have heq := (hfix (QuotientGroup.mk (g : G)) hbeta).symm
      change (g : G) ∈ M
      simpa using QuotientGroup.eq.mp heq
  apply le_antisymm
  · apply hs.twoPrimeCore_le_center_of_involutionCore_eq_top hx ?_ hgen
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (hcentral (mem_map_of_mem F.subtype hy)))
  · have hcB : center F ≤ M.comap F.subtype := by
      intro y hy
      exact hs.centralizer_le hxM hx (mem_centralizer_singleton_iff.mpr
        (mem_center_iff.mp hy x).symm)
    exact le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr (hs.normal_le_card_odd hcB)⟩

private theorem qf_involution_count
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t v : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    Nat.card {x : M.comap (centralizerClosure Z v).subtype // PFAppendixIII.IsInvolution x} =
      Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) - 1 := by
  obtain ⟨n, hn, hmodels, hAL, hDN, hlocal, hcore, hnormal, hA, hcard, hZ, hrest⟩ :=
    proper_residualGenerated_structure h r ha hz hzM ht htM hL heven
  let A := closure (Z ∩ (M : Set G))
  let C := A ⊓ centralizer ({v} : Set G)
  let F := centralizerClosure Z v
  let B := M.comap F.subtype
  let : IsElementaryAbelian 2 A := hA
  have hCF : C ≤ F := by
    change closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) ≤ centralizerClosure Z v
    rw [← proper_distinguished_centralizer_trace h r ha hz hzM ht htM hL heven v]
    exact closure_mono (fun _ hx => ⟨hx.1, hx.2.2⟩)
  let f : B →* G := F.subtype.comp B.subtype
  have hf : Function.Injective f := F.subtype_injective.comp B.subtype_injective
  have hC : ∀ x : B, PFAppendixIII.IsInvolution x → f x ∈ C := by
    intro x hx
    have hxi := IsInvolution.map_of_injective hx f hf
    have hxZ := (pair_involution_centralizerClosure_involutions h.disconnected r htM hvD hv
      x.val.property).mp hxi
    exact ⟨subset_closure ⟨hxZ, x.property⟩, centralizerClosure_le Z v x.val.property⟩
  let e : {x : B // PFAppendixIII.IsInvolution x} ≃
      {x : C // PFAppendixIII.IsInvolution x} := {
    toFun x := ⟨⟨f x, hC x x.property⟩,
      IsInvolution.subtype (IsInvolution.map_of_injective x.property f hf) _⟩
    invFun x := ⟨⟨⟨x.val.val, hCF x.val.property⟩, distinguishedClosure_le (Z := Z) (M := M) x.val.property.1⟩,
      ⟨fun he => x.property.ne_one (Subtype.ext
        (congrArg (fun x : B => ((x : F) : G)) he)),
        Subtype.ext (Subtype.ext (congrArg C.subtype x.property.sq_eq_one))⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr e).trans (involution_card_eq_of_exponent_two (fun x : C =>
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property.1)))

/-- Lemma 12.4(c): the literal odd-core quotient, with its field parameter
identified by the involutions in the actual local Borel. -/
public theorem proper_residualGenerated_centralizer_quotient_models
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      pPrimeCore 2 (centralizerClosure Z v) = center (centralizerClosure Z v) ∧
        ∃ k : ℕ, 2 ≤ k ∧
          Nat.card (closure (Z ∩ (M : Set G)) ⊓ centralizer ({v} : Set G) : Subgroup G) = 2 ^ k ∧
          IsSimpleBenderGroupAtExponent k
            (centralizerClosure Z v ⧸ pPrimeCore 2 (centralizerClosure Z v)) := by
  intro v hvD hv
  let F := centralizerClosure Z v
  let B := M.comap F.subtype
  let N := pPrimeCore 2 F
  let q := QuotientGroup.mk' N
  have hs := (pair_involution_centralizerClosure_local h.disconnected r htM hvD hv).2.2
  have hgen := centralizerClosure_involutionCore_eq_top h.disconnected v
  have hNB : N ≤ B := qf_oddCore_le_of_twoRank hs
    (qf_rank h r ha hz hzM ht htM hL heven hvD hv)
  have hc : N = center F := qf_center ha F hs hgen (fun x hx =>
    (pair_involution_centralizerClosure_involutions h.disconnected r htM hvD hv x.property).mp
      (IsInvolution.map_of_injective hx F.subtype F.subtype_injective)) hNB
  obtain ⟨hmodel, hBorel⟩ := qf_recognition hs hgen hNB
  obtain ⟨k, hk, hmodelk⟩ := hmodel.exists_exponent
  have hcount := bender_borel_involution_card_atExponent hk hmodelk hBorel
  have hodd : Odd (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hcountB := involution_card_map_of_central_odd_kernel q
    (QuotientGroup.mk'_surjective _) hodd (by rw [QuotientGroup.ker_mk', hc]) B
    (by rw [QuotientGroup.ker_mk']; exact hNB)
  have htrace := qf_involution_count h r ha hz hzM ht htM hL heven hvD hv
  have hlarge := proper_pair_involution_fixed_card_gt_two h r ha hz hzM ht htM hL heven hvD hv
  refine ⟨hc, k, hk, ?_, hmodelk⟩
  have hpow : 0 < 2 ^ k := pow_pos (by decide) _
  change Nat.card {x : B // PFAppendixIII.IsInvolution x} = _ at htrace
  change Nat.card {x : B.map q // PFAppendixIII.IsInvolution x} = _ at hcount
  omega

private theorem qf_frattini
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {t v : G} (htM : t ∉ M) (hvD : v ∈ residualPairStabilizer M t)
    (hv : PFAppendixIII.IsInvolution v) :
    (centralizer ({v} : Set G) : Set G) = (centralizerClosure Z v : Set G) *
      ((centralizer ({v} : Set G) ⊓ M : Subgroup G) : Set G) := by
  let F := centralizer ({v} : Set G)
  let C := closure (F.subtype ⁻¹' Z)
  let Y := (M.comap F.subtype).comap C.subtype
  have hFM := pair_involution_centralizer_not_le r htM hvD hv
  have hF : F ≠ ⊤ := by
    intro he
    have hvc : v ∈ center G := centralizer_eq_top_iff_subset.mp he (Set.mem_singleton v)
    rcases r.simple.eq_bot_or_eq_top_of_normal (center G) inferInstance with hb | ht
    · exact hv.ne_one (mem_bot.mp (hb ▸ hvc))
    · obtain ⟨w, hw, hwM⟩ := h.nonempty
      have hwc : w ∈ center G := ht ▸ mem_top w
      apply h.proper
      apply top_le_iff.mp
      intro x _
      exact h.centralizer_le hw hwM (mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hwc x))
  have hs0 := (pair_involution_centralizerClosure_local h r htM hvD hv).2.2
  obtain ⟨w, hwM, hw⟩ := hs0.exists_involution
  have hwZ := (pair_involution_centralizerClosure_involutions h r htM hvD hv w.property).mp
    (IsInvolution.map_of_injective hw _ (centralizerClosure Z v).subtype_injective)
  have hne : ∃ w ∈ Z, w ∈ F ∧ w ∈ M :=
    ⟨w, hwZ, centralizerClosure_le Z v w.property, hwM⟩
  have hs : IsStronglyEmbedded Y := r.local_embedding F hF hFM hne
  let : C.Normal := (productDisconnected_subgroup h F hFM hne).closure_normal
  obtain ⟨P, hP⟩ := hs.containsSylowTwo
  let Q : Subgroup F := (P : Subgroup C).map C.subtype
  have hQY : Q ≤ M.comap F.subtype := (map_le_iff_le_comap).mpr hP
  have hCtwo : 2 ∣ Nat.card C := hs.card_even.two_dvd.trans (card_subgroup_dvd_card Y)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := (P : Subgroup C)) 2
    (P.dvd_card_of_dvd_card hCtwo)
  have hxi : PFAppendixIII.IsInvolution x :=
    ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
  let f : C →* G := F.subtype.comp C.subtype
  have hf : Function.Injective f := F.subtype_injective.comp C.subtype_injective
  have hxFv : f (x : C) ∈ centralizerClosure Z v := by
    rw [centralizerClosure_eq_map]
    exact mem_map_of_mem F.subtype (x : C).property
  have hxZ := (pair_involution_centralizerClosure_involutions h r htM hvD hv hxFv).mp
    (IsInvolution.map_of_injective
      (IsInvolution.map_of_injective hxi (P : Subgroup C).subtype Subtype.val_injective) f hf)
  have hn : normalizer (Q : Set F) ≤ M.comap F.subtype := by
    apply normalizer_le (productDisconnected_subgroup h F hFM hne) hQY
    exact ⟨((x : C) : F), hxZ, mem_map_of_mem C.subtype x.property⟩
  have hsup : C ⊔ M.comap F.subtype = ⊤ := by
    apply top_unique
    rw [← Sylow.normalizer_sup_eq_top P]
    exact sup_le (hn.trans le_sup_right) le_sup_left
  have hmul : (C : Set F) * (M.comap F.subtype : Set F) = Set.univ := by
    rw [← Subgroup.normal_mul, hsup]
    rfl
  apply Set.Subset.antisymm
  · intro x hx
    have hh : (⟨x, hx⟩ : F) ∈ (C : Set F) * (M.comap F.subtype : Set F) := by
      rw [hmul]
      trivial
    obtain ⟨a, ha, b, hb, heq⟩ := hh
    refine ⟨a, ?_, b, ⟨b.property, hb⟩, congrArg F.subtype heq⟩
    rw [centralizerClosure_eq_map]
    exact mem_map_of_mem F.subtype ha
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact F.mul_mem (centralizerClosure_le Z v ha) hb.1

private theorem qf_beta_orbit
    (r : SimpleReduction Z M) {t v : G} (ht : PFAppendixIII.IsInvolution t)
    (hvD : v ∈ residualPairStabilizer M t) (hv : PFAppendixIII.IsInvolution v) :
    InOrbit (centralizer ({v} : Set G)) (QuotientGroup.mk 1 : G ⧸ M) (QuotientGroup.mk t) := by
  have hvconj : MulAut.conj t⁻¹ v ∈ M := by
    rw [ht.inv_eq_self]
    have hv' : v ∈ rightConjugate M t := hvD.2
    rw [rightConjugate, Subgroup.conjBy, mem_map] at hv'
    obtain ⟨x, hx, rfl⟩ := hv'
    simpa [MulAut.conj_apply, mul_assoc] using hx
  obtain ⟨S, hSM, hf⟩ := r.fusion
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hv
    (IsInvolution.map_of_injective hv (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective)
    hvD.1 hvconj (isConj_iff.mpr ⟨t⁻¹, rfl⟩)
  have hc : t * (m : G) ∈ centralizer ({v} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    change (m : G) * v * (m : G)⁻¹ = t⁻¹ * v * (t⁻¹)⁻¹ at hm
    rw [inv_inv] at hm
    calc
      (t * (m : G)) * v = t * ((m : G) * v * (m : G)⁻¹) * m := by group
      _ = v * (t * (m : G)) := by rw [hm]; group
  refine ⟨⟨t * m, hc⟩, ?_⟩
  change (QuotientGroup.mk ((t * (m : G)) * 1) : G ⧸ M) = QuotientGroup.mk t
  apply QuotientGroup.eq.mpr
  simpa only [mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel] using M.inv_mem m.property

/-- Lemma 12.4(e), for the original two-point stabilizer in the ambient
coset action. Fusion control puts the original second coset in the orbit. -/
public theorem proper_residualGenerated_centralizer_factorization
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) {z t : G}
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t))) :
    ∀ v ∈ residualPairStabilizer M t, PFAppendixIII.IsInvolution v →
      (centralizer ({v} : Set G) : Set G) = (centralizerClosure Z v : Set G) *
        ((residualPairStabilizer M t ⊓ centralizer ({v} : Set G) : Subgroup G) : Set G) := by
  intro v hvD hv
  let F := centralizerClosure Z v
  let C := centralizer ({v} : Set G)
  let B := M.comap F.subtype
  let N := pPrimeCore 2 F
  let alpha : G ⧸ M := QuotientGroup.mk 1
  let beta : G ⧸ M := QuotientGroup.mk t
  have hs := (pair_involution_centralizerClosure_local h.disconnected r htM hvD hv).2.2
  have hgen := centralizerClosure_involutionCore_eq_top h.disconnected v
  have hNB : N ≤ B := qf_oddCore_le_of_twoRank hs
    (qf_rank h r ha hz hzM ht htM hL heven hvD hv)
  obtain ⟨hmodel, hBorel⟩ := qf_recognition hs hgen hNB
  have hpoint : pointStabilizerIn F alpha = B := by
    ext x
    simp [pointStabilizerIn, alpha, B]
  have htwo : IsTwoTransitiveOn F {omega : G ⧸ M | InOrbit F alpha omega} := by
    apply isTwoTransitiveOn_orbit_of_quotient_image F alpha N
    · rwa [hpoint]
    · rw [hpoint]
      exact simpleBender_borel_coset_twoTransitive hBorel hmodel
  have horbit : ∀ omega : G ⧸ M, InOrbit C alpha omega ↔ InOrbit F alpha omega := by
    intro omega
    apply inOrbit_iff_of_eq_mul_pointStabilizer C F alpha omega (centralizerClosure_le Z v)
    simpa only [alpha, baseCoset_stabilizer] using qf_frattini h.disconnected r htM hvD hv
  have heq := set_eq_mul_twoPointStabilizer_of_twoTransitiveOn C F alpha beta
    (centralizerClosure_le Z v)
    (twoTransitiveOn_orbit_of_orbit_iff C F alpha horbit htwo)
    (qf_beta_orbit r (h.disconnected.involutions t ht) hvD hv)
    (fun he => htM (by simpa using QuotientGroup.eq.mp he.symm))
  have hstab : C ⊓ MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta =
      residualPairStabilizer M t ⊓ C := by
    rw [show MulAction.stabilizer G alpha = M from baseCoset_stabilizer M]
    rw [show MulAction.stabilizer G beta = rightConjugate M t⁻¹ from conjugateCoset_stabilizer M t]
    rw [(h.disconnected.involutions t ht).inv_eq_self]
    ext x
    exact ⟨fun hx => ⟨⟨hx.1.2, hx.2⟩, hx.1.1⟩, fun hx => ⟨⟨hx.2, hx.1.1⟩, hx.1.2⟩⟩
  rwa [hstab] at heq

end BenderSuzuki.ZD
