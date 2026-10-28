module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFullNormalization
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PResidual.NormalizerImage
/-!
# One full factor in the original escape action

A cubic normalizing a subgroup of order divisible by three has a fixed
subgroup whose order is also divisible by three, by conjugation orbit
counting. Two independent commuting normalized factors therefore supply
two independent commuting fixed three-elements. Together with the original
cubic outside the centralizer image, they contradict ambient three-rank
at most two. No lift of cubic normalization through a two-core is needed
for this argument.

Apply this to the literal factor images under the existing bijective cover
and ambient embedding of the W/Z_S action. Its image is nontrivial, so its
sole factor is the entire image. The full preimage of this factor inside P
is P itself, and the original P/O₂(P) is isomorphic to S₃, L₃(2), or S₅.
Since the ambient two-core lies in I, it normalizes P and its two-residual.
The residual-normalizer lifting theorem consequently makes every original
cubic normalize O²(P). This uses the literal quotient map and does not
claim normalization of all of P.

The original module model, quotient equations and normalization data remain
on the same witness, including the Chapter 12 application.

This proves the single-factor step of Aschbacher–Smith 6.1.19, printed p.675.
Normalization of P itself by the source torus, the parabolic/amalgam
contradiction, initial 6.1.4–5, omega escape and the remaining geometry still
belong to qt-d-1222-rankone-recognition-natural, which retains final assembly
of unconditional 6.1.27. Quotient normalization alone is not asserted to
normalize the smaller lift P.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative Classical
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section06
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace NaturalSingleFactor
variable {A : Type*} [Group A] [Finite A]

private theorem positive_rank (K : Subgroup A) (hK : 3 ∣ Nat.card K) :
    1 ≤ primeRank 3 K :=
  Nat.one_le_iff_ne_zero.mpr (fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hK)

private theorem two_factors_impossible (I K H : Subgroup A)
    (hKI : K ≤ I) (hHI : H ≤ I) (hd : Disjoint K H)
    (hcomm : K ≤ centralizer (H : Set A))
    (hK : 3 ∣ Nat.card K) (hH : 3 ∣ Nat.card H)
    (c : A) (hc : orderOf c = 3) (hout : c ∉ I)
    (hcK : c ∈ normalizer (K : Set A)) (hcH : c ∈ normalizer (H : Set A))
    (hr : primeRank 3 A ≤ 2) : False := by
  let C := zpowers c
  let X := K ⊓ centralizer (C : Set A)
  let Y := H ⊓ centralizer (C : Set A)
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by
    simpa only [C,Nat.card_zpowers,pow_one] using hc)
  have hfixed (J : Subgroup A) (hJ : 3 ∣ Nat.card J)
      (hn : c ∈ normalizer (J : Set A)) :
      3 ∣ Nat.card (J ⊓ centralizer (C : Set A) : Subgroup A) := by
    have hm := card_modEq_card_inf_centralizer C J hp (zpowers_le.mpr hn)
    exact Nat.modEq_zero_iff_dvd.mp (hm.symm.trans hJ.modEq_zero_nat)
  have hX : 1 ≤ primeRank 3 X := positive_rank X (hfixed K hK hcK)
  have hY : 1 ≤ primeRank 3 Y := positive_rank Y (hfixed H hH hcH)
  have hC : 1 ≤ primeRank 3 C := positive_rank C (by
    rw [show C = zpowers c from rfl,Nat.card_zpowers,hc])
  have hXY : Disjoint X Y := hd.mono inf_le_left inf_le_left
  have hXYc : X ≤ centralizer (Y : Set A) :=
    inf_le_left.trans (hcomm.trans (centralizer_le inf_le_left))
  have hXYI : X ⊔ Y ≤ I := sup_le (inf_le_left.trans hKI) (inf_le_left.trans hHI)
  have hdis : Disjoint (X ⊔ Y) C :=
    (I.disjoint_zpowers_of_prime_order_not_mem c hc hout).mono_left hXYI
  have hcen : X ⊔ Y ≤ centralizer (C : Set A) := sup_le inf_le_right inf_le_right
  have hu := (primeRank_subgroup_le 3 ((X ⊔ Y) ⊔ C : Subgroup A)).trans hr
  rw [primeRank_sup_eq_add_of_disjoint_commuting _ _ hdis hcen,
    primeRank_sup_eq_add_of_disjoint_commuting _ _ hXY hXYc] at hu
  omega

private theorem small_three_dvd {B V : Type*} [Group B] [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) B V}
    {K : Subgroup B} {U : Submodule (ZMod 2) V} (h : SmallFactorModel ρ K U) :
    3 ∣ Nat.card K := by
  rcases h with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
  · let E := e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
    rw [Nat.card_congr E.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
  · let E := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
    rw [Nat.card_congr E.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  · rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    decide
end NaturalSingleFactor

universe v
/-- An outside cubic fixing every factor forces the full marked product to
have at most one factor in ambient three-rank at most two. -/
theorem SmallTransvectionProductModel.factors_subsingleton_of_external_cubic
    {B V : Type v} {A : Type*} [Group B] [AddCommGroup V] [Module (ZMod 2) V]
    [Group A] [Finite A] {ρ : Representation (ZMod 2) B V}
    (product : SmallTransvectionProductModel ρ)
    (f : B →* A) (hf : Function.Injective f)
    (I : Subgroup A) (hI : f.range ≤ I)
    (c : A) (hc : orderOf c = 3) (hout : c ∉ I)
    (hn : ∀ K ∈ product.factors, c ∈ normalizer (K.map f : Set A))
    (hr : primeRank 3 A ≤ 2) :
    product.factors.card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro K hK H hH
  by_contra hne
  have hne' : (⟨K,hK⟩ : {K // K ∈ product.factors}) ≠ ⟨H,hH⟩ :=
    fun he => hne (congrArg Subtype.val he)
  have hd : Disjoint (K.map f) (H.map f) := by
    apply disjoint_iff_inf_le.mpr
    rintro _ ⟨⟨x,hx,rfl⟩,y,hy,he⟩
    have hy' : x ∈ H := hf he ▸ hy
    have hx1 := (product.independent.pairwiseDisjoint hne').le_bot ⟨hx,hy'⟩
    simpa only [show x = 1 from hx1,map_one] using (one_mem (⊥ : Subgroup A))
  have hcomm : K.map f ≤ centralizer (H.map f : Set A) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    exact (map_mul f y x).symm.trans
      ((congrArg f (product.commute hne' x y hx hy).eq.symm).trans (map_mul f x y))
  have hdiv (J : Subgroup B) (hJ : J ∈ product.factors) : 3 ∣ Nat.card (J.map f) := by
    rw [card_map_of_injective hf]
    obtain ⟨U,hU⟩ := product.small J hJ
    exact NaturalSingleFactor.small_three_dvd hU
  exact NaturalSingleFactor.two_factors_impossible I (K.map f) (H.map f)
    ((map_le_range _ _).trans hI) ((map_le_range _ _).trans hI)
    hd hcomm (hdiv K hK) (hdiv H hH) c hc hout (hn K hK) (hn H hH) hr

/-- For a nontrivial product the sole factor is the entire original group. -/
theorem SmallTransvectionProductModel.factors_eq_singleton_top
    {B V : Type v} [Group B] [Nontrivial B] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) B V} (product : SmallTransvectionProductModel ρ)
    (hcard : product.factors.card ≤ 1) : product.factors = {⊤} := by
  classical
  have hne : product.factors.Nonempty := by
    by_contra hh
    have hb : (⨆ K : {K // K ∈ product.factors}, K.val) = ⊥ := by
      apply le_antisymm _ bot_le
      apply iSup_le
      intro K
      exact (hh ⟨K.val,K.property⟩).elim
    have he : (⊤ : Subgroup B) = ⊥ := product.join_eq.symm.trans hb
    exact top_ne_bot he
  obtain ⟨K,hK⟩ := hne
  have hall (H : {K // K ∈ product.factors}) : H.val = K :=
    Finset.card_le_one.mp hcard _ H.property _ hK
  have he : K = ⊤ := by
    apply top_unique
    rw [←product.join_eq]
    exact iSup_le fun H => (hall H).le
  ext H
  simp only [Finset.mem_singleton]
  constructor
  · intro hH
    exact (Finset.card_le_one.mp hcard _ hH _ hK).trans he
  · rintro rfl
    exact he ▸ hK


/-- The original covering group has the type of the sole marked factor,
using the given bijective covering map. -/
theorem SmallTransvectionProductModel.cover_model_of_singleton_top
    {B V : Type v} {H : Type*} [Group B] [Group H]
    [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) B V} (product : SmallTransvectionProductModel ρ)
    (hsingle : product.factors = {⊤}) (φ : H →* B) (hφ : Function.Bijective φ) :
    Nonempty (H ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (H ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 5)) := by
  classical
  have htop : (⊤ : Subgroup B) ∈ product.factors := by rw [hsingle]; simp
  obtain ⟨U,hU⟩ := product.small ⊤ htop
  let eφ := (MulEquiv.ofBijective φ hφ).trans Subgroup.topEquiv.symm
  rcases hU with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
  · exact Or.inl ⟨eφ.trans (e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
      (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)))⟩
  · exact Or.inr (Or.inl ⟨eφ.trans e⟩)
  · exact Or.inr (Or.inr ⟨eφ.trans e⟩)

/-- Quotient normalization lifts to the original two-residual when the
ambient two-core normalizes the original subgroup. -/
theorem original_residual_normalized_of_quotient
    {A : Type*} [Group A] [Finite A] (P I N : Subgroup A)
    (hPN : P ≤ N) (hIP : I ≤ normalizer (P : Set A))
    (hcore : pCore 2 N ≤ I.subgroupOf N)
    (c : N) (hc : QuotientGroup.mk' (pCore 2 N) c ∈ normalizer
      ((P.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N)) : Set (N ⧸ pCore 2 N))) :
    (c : A) ∈ normalizer ((pResidual 2 P).map P.subtype : Set A) := by
  let B := P.subgroupOf N
  let D := (pResidual 2 B).map B.subtype
  let q := QuotientGroup.mk' (pCore 2 N)
  have hNB : pCore 2 N ≤ normalizer (B : Set N) := by
    rw [←subgroupOf_normalizer_eq hPN]
    intro x hx
    exact hIP (hcore hx)
  have hND : q.ker ≤ normalizer (D : Set N) := by
    rw [QuotientGroup.ker_mk']
    exact hNB.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))
  have hk : IsPGroup 2 q.ker := by
    rw [show q.ker = pCore 2 N from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup
  have he := comap_normalizer_map_of_pPerfect q D (isPPerfect_embedded_pResidual 2 B) hk hND
  have hcm : q c ∈ normalizer (D.map q : Set (N ⧸ pCore 2 N)) := by
    change q c ∈ normalizer (((pResidual 2 B).map B.subtype).map q : Set (N ⧸ pCore 2 N))
    rw [map_embedded_pResidual]
    exact normalizer_le_normalizer_characteristic_image (B.map q) (pResidual 2 (B.map q)) hc
  have hcD : c ∈ normalizer (D : Set N) := he ▸ hcm
  have hn : (c : A) ∈ normalizer (D.map N.subtype : Set A) :=
    D.le_normalizer_map N.subtype (mem_map_of_mem N.subtype hcD)
  have hD : D.map N.subtype = (pResidual 2 P).map P.subtype := by
    change ((pResidual 2 B).map B.subtype).map N.subtype = _
    rw [map_embedded_pResidual,show B.map N.subtype = P from map_subgroupOf_eq_of_le hPN]
  rwa [hD] at hn

open CFSG.Quasithin.ChapterE
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- The original W/Z_S action has just one full marked factor. It is the
whole action image, with its S₃, L₃(2), or S₅ module model retained. -/
theorem exists_ambient_single_factor
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
          closure {x : P ⧸ pCore 2 P | x ^ 2 = 1} = ⊤ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∃ product : SmallTransvectionProductModel θ,
            product.factors = {⊤} ∧
            (∃ U : Submodule (ZMod 2) (Additive (W ⧸ Z.subgroupOf W)),
              SmallFactorModel θ ⊤ U) ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            (∀ c : N, c^3=1 → (c : G) ∈ Subgroup.normalizer
              ((pResidual 2 P).map P.subtype : Set G)) ∧
            (∀ K ∈ product.factors,
              (((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) = P) ∧
            (∀ K ∈ product.factors, FactorResidualLift φ j
              ((I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) K ∧
              ∀ c : N ⧸ pCore 2 N, c^3=1 →
                c ∈ Subgroup.normalizer ((((pResidual 2 (K.comap φ)).map
                  (K.comap φ).subtype).map j) : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors,
              ((pResidual 2 I).map (inclusion hIN)).map (QuotientGroup.mk' (pCore 2 N)) ≤
                Subgroup.normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N)) ∧
              (pResidual 2 I).map I.subtype ≤ Subgroup.normalizer
                ((((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) : Set G)) ∧
            (∀ K ∈ product.factors, ∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ Subgroup.normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N))) ∧
            (∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ Subgroup.normalizer (j.range : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors, ∀ c : N, c^3=1 →
              c ∈ Subgroup.normalizer (((K.comap φ).map j).comap
                (QuotientGroup.mk' (pCore 2 N)) : Set N)) ∧
            ∃ e : (∀ K : {K // K ∈ product.factors}, K.val) ≃* (P ⧸ pCore 2 P),
              (∀ x, φ (e x) = product.productEquiv x) ∧
              (∀ K : {K // K ∈ product.factors}, ∀ a : P ⧸ pCore 2 P,
                a ∈ K.val.comap φ ↔ ∃ x : K.val,
                  e (Function.update 1 K x) = a) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,hact,hfull,hrange,hlift,
      e,he,hcoords⟩ := d.exists_ambient_cubic_full_product h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓
    conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let q := QuotientGroup.mk' (pCore 2 N)
  let Q := (I.subgroupOf N).map q
  let := hZ
  let := hX
  let g := σ.comp (inclusion hPI)
  have hEn : (E.subgroupOf I).map σ ≤ g.range := by
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨⟨x,le_conjugateSpanBy E I hx⟩,rfl⟩
  have hnon : g.range ≠ ⊥ := by
    intro hh
    have hle := card_le_of_le hEn
    rw [hh,card_bot] at hle
    exact (not_lt_of_ge hle) (show 1 < Nat.card ((E.subgroupOf I).map σ) from hpos)
  let : Nontrivial g.range := (nontrivial_iff_ne_bot _).mpr hnon
  let eφ := MulEquiv.ofBijective φ hφ
  let f := j.comp eφ.symm.toMonoidHom
  have hf : Function.Injective f := hj.comp eφ.symm.injective
  have hmap (K : Subgroup g.range) : K.map f = (K.comap φ).map j := by
    have he : K.comap φ = K.map eφ.symm.toMonoidHom :=
      comap_equiv_eq_map_symm eφ K
    rw [he,map_map]
  have hjQ : j.range ≤ Q := by
    rintro _ ⟨p,rfl⟩
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) p
    rw [hje]
    exact mem_map_of_mem q (show inclusion hPN p ∈ I.subgroupOf N from hPI p.property)
  have hfQ : f.range ≤ Q := by
    rintro _ ⟨b,rfl⟩
    exact hjQ ⟨eφ.symm b,rfl⟩
  obtain ⟨_,hr,c,_,_,_,hc,hout⟩ :=
    natural_four_ambient_quotient_cubic (hn ▸ h) (hn ▸ hnat)
  have hcard : product.factors.card ≤ 1 :=
    product.factors_subsingleton_of_external_cubic f hf Q hfQ (q c) hc hout
      (fun K hK => by
        rw [hmap]
        exact hfull K hK (q c) (hc ▸ pow_orderOf_eq_one (q c))) hr
  have hsingle := product.factors_eq_singleton_top hcard
  have htop : (⊤ : Subgroup g.range) ∈ product.factors := by rw [hsingle]; simp
  have horiginal : ∀ c : N, c^3=1 → (c : G) ∈ Subgroup.normalizer
      ((pResidual 2 P).map P.subtype : Set G) := by
    intro c hc3
    apply original_residual_normalized_of_quotient P I N hPN
      (le_normalizer_conjugateSpanBy E I)
      (natural_four_ambient_quotient_cubic (hn ▸ h) (hn ▸ hnat)).1 c
    have him : (P.subgroupOf N).map q = j.range := by
      apply le_antisymm
      · rintro _ ⟨p,hp,rfl⟩
        exact ⟨QuotientGroup.mk' (pCore 2 P) ⟨p,hp⟩,hje _⟩
      · rintro _ ⟨x,rfl⟩
        obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) x
        rw [hje]
        exact mem_map_of_mem q p.property
    rw [him]
    exact hrange (q c) (by rw [←map_pow,hc3,map_one])
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hsingle,product.small ⊤ htop,
    product.cover_model_of_singleton_top hsingle φ hφ,horiginal,?_,
    hres,hact,hfull,hrange,hlift,e,he,hcoords⟩
  intro K hK
  rw [hsingle,Finset.mem_singleton] at hK
  rw [hK,comap_top,comap_top,←MonoidHom.range_eq_map,range_subtype]

end NaturalEscapeGraph.OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
