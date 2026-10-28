module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.BinaryThreeInterval
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Inner
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.SourceAssembly
public import Theory.GroupTheory.NormalSymmetricThreeExtension

/-!
# Source placement of the two binary-three parabolics

Both lifted maximal parabolics have two-residuals strictly larger than
their order-twelve model images. Otherwise their residuals would centralize
the original two-core, contradicting characteristic two in K. Since their
orders have only one factor of three, neither residual is an A₃ product.
This argument applies to every binary-three member of the local family.

For the selected component, M_L cannot equal S_L: its S-orbit would be
a normal two-subgroup of M_Z, placing S_L in Q₁ and forcing a rank-one
block, contrary to the literal core quotient's order 168. Thus M_L is one
maximal member of the Sylow interval. The actual N_S(L) fixes M_L, hence
fixes the other member as well. Their S₃ quotients and residual exclusions
now give the entire source parabolic family. Original (*) places both in
M∩L or M_L. Generation forces those two intersections to occupy opposite
maximal positions, and their literal O^{3′} residuals escape one another.

The original-prime and actual-marker exports retain both source primes,
the FF marking, and both flag images under that same marking. The later
exchanged application retains the same complete parabolic family. No
characteristic-two assumption on G₁ or universal C.1.34 classification is
used. The natural L₃ block reconstruction and its centralizer clauses,
the A₆ branches, general local-family Borel placement and full catalogue
exhaustiveness remain source obligations. Original 15.1.14 stays explicit
in the marker application for its existing producer and assembly owner.

Source: Aschbacher--Smith 15.1.20(2b) and 15.1.22(*),(2), pp.1094--1100.
The concrete binary model retains its ATLAS attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem residual_card_lt_of_characteristic_core
    {D : Type*} [Group D] [Finite D]
    (P : Subgroup G) (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hQ : pCore 2 G ≤ P) (f : P →* D) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 G).subgroupOf P)
    (hne : pResidual 2 D ≠ ⊥) :
    Nat.card (pResidual 2 D) < Nat.card (pResidual 2 P) := by
  let R := pResidual 2 P
  let Q := (pCore 2 G).subgroupOf P
  let g := f.subgroupMap R
  have him : R.map f = pResidual 2 D := map_pResidual_of_surjective 2 f hf
  by_contra hn
  have hinj : Function.Injective g :=
    (f.subgroupMap_surjective R).bijective_of_nat_card_le (by
      rw [him]
      exact Nat.le_of_not_gt hn) |>.1
  have hdis : Disjoint R Q := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hx0 : f x = 1 := by change x ∈ f.ker; rw [hk]; exact hx.2
    have he : g ⟨x,hx.1⟩ = g 1 := by apply Subtype.ext; exact hx0.trans (map_one f).symm
    exact congrArg Subtype.val (hinj he)
  have hcomm : ⁅R,Q⁆ = ⊥ := bot_unique ((commutator_le_inf R Q).trans hdis.le_bot)
  have hRQ : R ≤ Q := by
    intro x hx
    apply hc
    intro y hy
    have hyP := hQ hy
    exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx ⟨y,hyP⟩ hy)
  have hz : R.map f = ⊥ := (Subgroup.map_eq_bot_iff R).mpr (hk.symm ▸ hRQ)
  exact hne (him.symm.trans hz)


private theorem binaryThree_parabolic_residual_size
    (hf : generalizedFitting G = pCore 2 G)
    (e : (G ⧸ pCore 2 G) ≃* Matrix.PSL3Two.SL)
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) < P)
    (hP : IsCoatom P) :
    ¬ 9 ∣ Nat.card P ∧ 12 < Nat.card (pResidual 2 P) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hkS : q.ker ≤ (S : Subgroup G) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  let B := P.map q
  have hBS : (S.mapSurjective hq : Subgroup Matrix.PSL3Two.SL) ≤ B := map_mono hSP.le
  have hB : B ≠ ⊤ := by
    intro he
    have hh := comap_map_eq_self (hkS.trans hSP.le)
    change B.comap q = P at hh
    rw [he,comap_top] at hh
    exact hP.ne_top hh.symm
  have hn : ¬ IsPGroup 2 B := by
    intro hp
    have hp' := hp.comap_of_ker_isPGroup q (hk ▸ pCore_isPGroup)
    rw [comap_map_eq_self (hkS.trans hSP.le)] at hp'
    exact hSP.ne ((S.is_maximal' hp' hSP.le).symm)
  obtain ⟨t,_,ht⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    Matrix.PSL3Two.equiv (S.mapSurjective hq) B hBS hB hn
  let b : B ≃* Matrix.PSL3Two.lineParabolicSL :=
    (t.subgroupMap B).trans (MulEquiv.subgroupCongr ht)
  let f := b.toMonoidHom.comp (q.subgroupMap P)
  have hsurj : Function.Surjective f := b.surjective.comp (q.subgroupMap_surjective P)
  have hker : f.ker = (pCore 2 G).subgroupOf P := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective]
    ext x
    change (⟨q x,_⟩ : B) = 1 ↔ (x : G) ∈ pCore 2 G
    rw [←hk]
    exact Subtype.ext_iff
  have h12 : Nat.card (pResidual 2 Matrix.PSL3Two.lineParabolicSL) = 12 := by
    have hh := Matrix.PSL3Two.MarkedAutomorphisms.card_line_residual
    rw [Matrix.PSL3Two.MarkedAutomorphisms.residual,
      card_map_of_injective Matrix.PSL3Two.lineParabolicSL.subtype_injective] at hh
    exact hh
  have hne : pResidual 2 Matrix.PSL3Two.lineParabolicSL ≠ ⊥ := by
    intro he
    rw [he,card_bot] at h12
    omega
  refine ⟨?_,?_⟩
  · have hc := f.ker.card_mul_index
    rw [index_ker,f.range_eq_top_of_surjective hsurj,card_top,
      Matrix.PSL3Two.card_lineParabolicSL] at hc
    obtain ⟨r,hr⟩ := (show IsPGroup 2 f.ker from hker ▸ pCore_isPGroup.comap_subtype).exists_card_eq
    rw [hr] at hc
    intro hd
    rw [←hc] at hd
    exact (by decide : ¬9 ∣ 24)
      (((by decide : Nat.Coprime 9 2).pow_right r).dvd_of_dvd_mul_left hd)
  · rw [←h12]
    exact residual_card_lt_of_characteristic_core P
      (hf ▸ centralizer_generalizedFitting_le G)
      ((pCore_isPGroup.le_sylow_of_normal S).trans hSP.le) f hsurj hker hne

/-- Characteristic two in the original member rules out A₃-product residuals
in both lifted parabolics, including their entire two-core kernels. -/
theorem BinaryThreeParabolicInterval.not_aThree_products
    {K S : Subgroup G} (i : BinaryThreeParabolicInterval K S)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    ¬ IsAThreeProduct i.left ∧ ¬ IsAThreeProduct i.right := by
  obtain ⟨Q,hQ⟩ := i.sylow
  have one (P : Subgroup G) (hPK : P ≤ K) (hSP : S < P)
      (hmax : IsCoatom (P.subgroupOf K)) : ¬ IsAThreeProduct P := by
    have hSP' : (Q : Subgroup K) < P.subgroupOf K := by
      apply (map_lt_map_iff_of_injective K.subtype_injective).mp
      rw [hQ,map_subgroupOf_eq_of_le hPK]
      exact hSP
    obtain ⟨h9,h12⟩ := binaryThree_parabolic_residual_size hf e Q (P.subgroupOf K) hSP' hmax
    let t : P.subgroupOf K ≃* P := subgroupOfEquivOfLe hPK
    have hc : Nat.card (pResidual 2 (P.subgroupOf K)) = Nat.card (pResidual 2 P) := by
      have hh := congrArg (fun X : Subgroup P => Nat.card X)
        (map_pResidual_of_surjective 2 t.toMonoidHom t.surjective)
      rw [card_map_of_injective t.injective] at hh
      exact hh
    rw [hc] at h12
    rw [Nat.card_congr t.toEquiv] at h9
    intro hA
    have hh := aThreeProduct_residual_card_le P h9 hA
    omega
  exact ⟨one i.left i.left_le i.sylow_left i.left_maximal,
    one i.right i.right_le i.sylow_right i.right_maximal⟩

private theorem marked_orbit_normalized_of_cComponent
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    {K B : Subgroup G} (hK : K ≤ d.G1)
    (hcomp : (K.subgroupOf d.G1).IsCComponent)
    (hinv : d.MZ ⊓ normalizer (K : Set G) ≤ normalizer (B : Set G)) :
    d.MZ ≤ normalizer (conjugateSpanBy B d.S : Set G) := by
  let := h.elementary
  let R := (pResidual 2 d.MZ).map d.MZ.subtype
  have hRM : R ≤ d.MZ := map_subtype_le _
  have hRG : R ≤ d.G1 := hRM.trans inf_le_left
  let e := (subgroupOfEquivOfLe hRG).symm
  have hp : IsPPerfect 2 (R.subgroupOf d.G1) :=
    (isPPerfect_embedded_pResidual 2 d.MZ).of_surjective e.toMonoidHom e.surjective
  have hsqtk : IsSQTK KnownSimple.IsKnownSimple d.G1 :=
    caseI_centralizer_sqtk hG d.Z1 d.Z1_ne_bot
    ((IsElementaryAbelian.isPGroup 2 V).to_le (d.Z1_le_fixed.trans inf_le_left))
  have hquot : IsSQTK KnownSimple.IsKnownSimple (d.G1 ⧸ pCore 2 d.G1) := by
    refine ⟨?_,hsqtk.isKGroup.quotient (pCore 2 d.G1)⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 d.G1) pCore_isPGroup).trans
      (hsqtk.stronglyQuasithin q hq ho)
  have hn0 := Chapter1.Section02.twoPerfect_normalizes_cComponent_source hquot hcomp hp
  have hnK := (map_mono (f := d.G1.subtype) hn0).trans
    ((K.subgroupOf d.G1).le_normalizer_map d.G1.subtype)
  rw [map_subgroupOf_eq_of_le hRG,map_subgroupOf_eq_of_le hK] at hnK
  have hnB : R ≤ normalizer (B : Set G) := (le_inf hRM hnK).trans hinv
  have hnR : d.MZ ≤ normalizer (R : Set G) := d.MZ.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.MZ (pResidual 2 d.MZ))
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  obtain ⟨P,hP⟩ := hSyl
  obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le
    (show d.MZ ≤ d.G1 from inf_le_left) (hP ▸ hSM)
  have he : R ⊔ d.S = d.MZ := by
    have hh := congrArg (map d.MZ.subtype) (pResidual_sup_sylow_eq_top Q)
    simpa only [Subgroup.map_sup,hQ,hP,←MonoidHom.range_eq_map,range_subtype] using hh
  rw [←he]
  exact sup_le (TwoOrbitSpan.normalizes_span _ _ R hnB (hSM.trans hnR))
    (le_normalizer_conjugateSpanBy _ _)


private theorem binaryThree_not_rankOne {K : Type*} [Group K]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.SL) :
    ¬ ((∃ n, IsL2EvenBlock K n) ∨ IsAlternatingBlock K 5) := by
  have hc : Nat.card (K ⧸ pCore 2 K) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_SL
  rintro (⟨n,hn,_,F,_,_,hF,_,r,⟨m⟩,_⟩ | ⟨_,_,r,⟨m⟩,_⟩)
  · rw [Nat.card_congr m.quotientIso.toEquiv,Atlas.card_sl_two,hF] at hc
    have hn3 : 3 ≤ n := by
      by_contra h
      have : n = 2 := by omega
      norm_num [this] at hc
    have hq : 8 ≤ 2^n := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hn3
    have hs : 63 ≤ (2^n)^2-1 := by
      have hh : (8 : ℕ)^2 ≤ (2^n)^2 := Nat.pow_le_pow_left hq 2
      omega
    have hh := Nat.mul_le_mul hq hs
    omega
  · rw [Nat.card_congr m.quotientIso.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc


/-- If the original marked intersection is only the Sylow intersection,
its S-orbit is a normal two-subgroup of M_Z and hence lies in Q₁. -/
theorem sylow_le_radical_of_marked_eq
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : PreparedChosenModule T M V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hSyl : Chapter1.IsSylowIn 2 d.S d.G1)
    (he : d.ML = d.SL) : d.SL ≤ d.Q1 := by
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  let B := conjugateSpanBy d.SL d.S
  have hBS : B ≤ d.S := conjugateSpanBy_le inf_le_left d.S.le_normalizer
  have hn : d.MZ ≤ normalizer (B : Set G) := by
    apply marked_orbit_normalized_of_cComponent d hG h hu hSyl
      d.L_component.1 d.L_component.2
    rw [←he]
    exact (inf_le_inf_right _ d.MZ.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 B := T.isPGroup'.to_le (hBS.trans d.S_le_T)
  have hh := pCoreIn_mono_of_normalizes (hBS.trans hSM) hn (p := 2)
  rw [pCoreIn_eq_self_of_isPGroup 2 B hp] at hh
  exact (le_conjugateSpanBy _ _).trans hh

/-- The binary-three marked intersection strictly exceeds S_L. This uses
normality in M_Z of its literal S-orbit, not a fixed-space classification. -/
theorem PreExclusionSource.constrained_binaryThree_marked_ne_sylow
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL) : d.ML ≠ d.SL := by
  intro he
  exact binaryThree_not_rankOne e
    (s.constrained_rankOne_block_of_sylow_le_radical (h := h) hG hf
      (d.sylow_le_radical_of_marked_eq hG h hu s.centralizer_sylow he))

omit [Finite G] in
private theorem interval_other_fixed
    {K S B P Q : Subgroup G} (i : BinaryThreeParabolicInterval K S)
    (hP : P = i.left ∨ P = i.right) (hQ : Q = i.left ∨ Q = i.right)
    (hne : P ≠ Q) (hBK : B ≤ normalizer (K : Set G))
    (hBS : B ≤ normalizer (S : Set G)) (hBP : B ≤ normalizer (P : Set G)) :
    B ≤ normalizer (Q : Set G) := by
  have hSQ : S < Q := by rcases hQ with rfl | rfl; exact i.sylow_left; exact i.sylow_right
  have hQK : Q < K := by
    have hle : Q ≤ K := by rcases hQ with rfl | rfl; exact i.left_le; exact i.right_le
    refine lt_of_le_of_ne hle ?_
    intro he
    have ht : Q.subgroupOf K = ⊤ := he ▸ subgroupOf_self _
    rcases hQ with he | he
    · exact i.left_maximal.ne_top (he ▸ ht)
    · exact i.right_maximal.ne_top (he ▸ ht)
  intro g hg
  let a := (MulAut.conj g).toMonoidHom
  have hKfix : K.map a = K := mem_normalizer_iff_map_conj_eq.mp (hBK hg)
  have hSfix : S.map a = S := mem_normalizer_iff_map_conj_eq.mp (hBS hg)
  have hPfix : P.map a = P := mem_normalizer_iff_map_conj_eq.mp (hBP hg)
  have hSmap : S < Q.map a := by
    rw [←hSfix]
    exact (map_lt_map_iff_of_injective (MulAut.conj g).injective).mpr hSQ
  have hmapK : Q.map a < K := by
    rw [←hKfix]
    exact (map_lt_map_iff_of_injective (MulAut.conj g).injective).mpr hQK
  have hnot : Q.map a ≠ P := by
    intro he
    rw [←hPfix] at he
    exact hne (map_injective (MulAut.conj g).injective he).symm
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases i.exhaustive (Q.map a) hSmap.le hmapK.le with he | he | he | he
  · exact (hSmap.ne he.symm).elim
  · rcases hQ with hQ | hQ
    · exact he.trans hQ.symm
    · rcases hP with hP | hP
      · exact (hnot (he.trans hP.symm)).elim
      · exact (hne (hP.trans hQ.symm)).elim
  · rcases hQ with hQ | hQ
    · rcases hP with hP | hP
      · exact (hne (hP.trans hQ.symm)).elim
      · exact (hnot (he.trans hP.symm)).elim
    · exact he.trans hQ.symm
  · exact (hmapK.ne he).elim

/-- Fixing the marked maximal member fixes the other member of the
binary-three interval. The acting group is the literal N_S(L). -/
theorem BinaryThreeParabolicInterval.normalized_of_marked_ne_sylow
    {d : CaseIComponentData T M Mc V} (i : BinaryThreeParabolicInterval d.L d.SL)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hm : d.ML = d.SL ∨ d.ML = i.left ∨ d.ML = i.right)
    (hne : d.ML ≠ d.SL) :
    d.sylowNormalizer ≤ normalizer (i.left : Set G) ∧
      d.sylowNormalizer ≤ normalizer (i.right : Set G) := by
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  have hNK : d.sylowNormalizer ≤ normalizer (d.L : Set G) := inf_le_right
  have hNS : d.sylowNormalizer ≤ normalizer (d.SL : Set G) :=
    (inf_le_inf_right _ d.S.le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hNM : d.sylowNormalizer ≤ normalizer (d.ML : Set G) :=
    (inf_le_inf_right _ (hSM.trans d.MZ.le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hpq : i.left ≠ i.right := by
    intro he
    have hh := i.intersection
    rw [he,inf_idem] at hh
    exact i.sylow_right.ne hh.symm
  rcases hm.resolve_left hne with hm | hm
  · have hnL : d.sylowNormalizer ≤ normalizer (i.left : Set G) := hm ▸ hNM
    exact ⟨hnL,interval_other_fixed i (Or.inl rfl) (Or.inr rfl) hpq hNK hNS hnL⟩
  · have hnR : d.sylowNormalizer ≤ normalizer (i.right : Set G) := hm ▸ hNM
    exact ⟨interval_other_fixed i (Or.inr rfl) (Or.inl rfl) hpq.symm hNK hNS hnR,hnR⟩


/-- The original binary-three parabolics satisfy the full source family.
The marked intersection and M∩L are its two different maximal members,
with the prescribed FF marking retained at either source prime. -/
theorem PreExclusionSource.constrained_binaryThree_source_parabolics
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ i : BinaryThreeParabolicInterval d.L d.SL,
        d.IsSourceParabolic i.left ∧ d.IsSourceParabolic i.right ∧
        ((d.ML = i.left ∧ M ⊓ d.L = i.right) ∨
          (d.ML = i.right ∧ M ⊓ d.L = i.left)) := by
  obtain ⟨t,ht,hparM,hparN,i,hm,hn⟩ := s.constrained_binaryThree_interval (h := h)
    hG hempty hM hJ hu hf e
  have hms := s.constrained_binaryThree_marked_ne_sylow (h := h) hG hu hf t
  have hnorm := i.normalized_of_marked_ne_sylow hu hm hms
  have hnot := i.not_aThree_products hf t
  have htwo : IsPGroup 2 d.sylowNormalizer :=
    T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)
  have hleft : d.IsSourceParabolic i.left := by
    obtain ⟨eP⟩ := i.left_quotient
    exact ⟨i.left_le,hnorm.1,i.left_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.1 eP htwo),hnot.1⟩
  have hright : d.IsSourceParabolic i.right := by
    obtain ⟨eP⟩ := i.right_quotient
    exact ⟨i.right_le,hnorm.2,i.right_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.2 eP htwo),hnot.2⟩
  have hplace := s.parabolic_placement_of_constrained (h := h) hG hempty hM hJ hu hf
  have hgen : (M ⊓ d.L) ⊔ d.ML = d.L := by
    apply le_antisymm (sup_le inf_le_right inf_le_right)
    calc
      d.L = i.left ⊔ i.right := i.generated.symm
      _ ≤ (M ⊓ d.L) ⊔ d.ML := sup_le
        ((hplace i.left hleft).elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right))
        ((hplace i.right hright).elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right))
  have hSML : d.SL ≤ d.ML := by
    rcases hm.resolve_left hms with he | he
    · exact he.symm ▸ i.sylow_left.le
    · exact he.symm ▸ i.sylow_right.le
  have hns : M ⊓ d.L ≠ d.SL := by
    intro he
    rw [he,sup_eq_right.mpr hSML] at hgen
    exact d.L_not_le_MZ (hgen ▸ inf_le_left)
  have hne : d.ML ≠ M ⊓ d.L := by
    intro he
    rw [←he,sup_idem] at hgen
    exact d.L_not_le_MZ (hgen ▸ inf_le_left)
  refine ⟨t,ht,hparM,hparN,i,hleft,hright,?_⟩
  rcases hm.resolve_left hms with hm | hm <;>
    rcases hn.resolve_left hns with hn | hn
  · exact (hne (hm.trans hn.symm)).elim
  · exact Or.inl ⟨hm,hn⟩
  · exact Or.inr ⟨hm,hn⟩
  · exact (hne (hm.trans hn.symm)).elim

/-- Both original intersections are now maximal parabolics, generate L,
and have the required literal O^{3′} escape. No intersection-position
premise or whole-block reconstruction is assumed. -/
theorem PreExclusionSource.constrained_binaryThree_parabolic_geometry
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    IsLinearMaximalParabolic ((d.ML.subgroupOf d.L).map
      (QuotientGroup.mk' (pCore 2 d.L))) 3 (ZMod 2) ∧
      IsLinearMaximalParabolic (((M ⊓ d.L).subgroupOf d.L).map
        (QuotientGroup.mk' (pCore 2 d.L))) 3 (ZMod 2) ∧
      (M ⊓ d.L) ⊔ d.ML = d.L ∧ ¬ d.localThreeResidual ≤ d.ML := by
  obtain ⟨_,_,_,_,i,_,_,hp⟩ := s.constrained_binaryThree_source_parabolics (h := h)
    hG hempty hM hJ hu hf e
  have hres := i.cubic_residuals
  rcases hp with ⟨hm,hn⟩ | ⟨hm,hn⟩
  · refine ⟨hm.symm ▸ i.left_parabolic,hn.symm ▸ i.right_parabolic,?_,?_⟩
    · rw [hm,hn,sup_comm,i.generated]
    · change ¬ (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤ d.ML
      rw [hn,hm]
      exact hres.2.2.2
  · refine ⟨hm.symm ▸ i.right_parabolic,hn.symm ▸ i.left_parabolic,?_,?_⟩
    · rw [hm,hn,i.generated]
    · change ¬ (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤ d.ML
      rw [hn,hm]
      exact hres.2.2.1


/-- Either later exchanged plane retains the same marked core quotient and
both complete source-parabolic families. The earlier original-prime proof
above does not use this selection. -/
theorem ExchangedSource.constrained_binaryThree_source_parabolics
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (h : PreparedChosenModule T M V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      d.ConstrainedLinearParabolic t d.ML ∧
      d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
      ∃ i : BinaryThreeParabolicInterval d.L d.SL,
        d.IsSourceParabolic i.left ∧ d.IsSourceParabolic i.right ∧
        (d.ML = i.left ∨ d.ML = i.right) := by
  obtain ⟨t,ht,hparM,hparN,i,hm,_⟩ := s.constrained_binaryThree_interval h hG hempty hM hJ hu hf e
  have hms : d.ML ≠ d.SL := by
    intro he
    exact binaryThree_not_rankOne t
      (s.constrained_rankOne_block_of_sylow_le_radical h hG hf
        (d.sylow_le_radical_of_marked_eq hG h hu s.centralizer_sylow he))
  have hnorm := i.normalized_of_marked_ne_sylow hu hm hms
  have hnot := i.not_aThree_products hf t
  have htwo : IsPGroup 2 d.sylowNormalizer :=
    T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)
  refine ⟨t,ht,hparM,hparN,i,?_,?_,hm.resolve_left hms⟩
  · obtain ⟨eP⟩ := i.left_quotient
    exact ⟨i.left_le,hnorm.1,i.left_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.1 eP htwo),hnot.1⟩
  · obtain ⟨eP⟩ := i.right_quotient
    exact ⟨i.right_le,hnorm.2,i.right_fitting,Or.inl
      (NormalSymmetricThreeExtension.normalized_join _ _ hnorm.2 eP htwo),hnot.2⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the full binary-three parabolic
family and both different source intersections, preserving either prime
and the elementwise FF marking. Original 15.1.14 remains explicit. -/
theorem PreparedChosenModule.source_preExclusion_constrained_binaryThree_source_parabolics
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* Matrix.PSL3Two.SL,
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* Matrix.PSL3Two.SL,
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            d.ConstrainedLinearParabolic t d.ML ∧
            d.ConstrainedLinearParabolic t (M ⊓ d.L) ∧
            ∃ i : CaseIComponentData.BinaryThreeParabolicInterval d.L d.SL,
              d.IsSourceParabolic i.left ∧ d.IsSourceParabolic i.right ∧
              ((d.ML = i.left ∧ M ⊓ d.L = i.right) ∨
                (d.ML = i.right ∧ M ⊓ d.L = i.left))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf e =>
    s.constrained_binaryThree_source_parabolics (h := h) hG hempty hM hJ hu hf e⟩

end CFSG.Quasithin.Chapter15.Section01
