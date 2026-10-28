module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalStructure
public import CFSG.Quasithin.ChapterF.Section01.RankOneOddPrime
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.GroupTheory.SimpleSectionSolvableReduction
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOddTernaryRecognition

/-!
# Every odd quadratic-prime container in the original Cartan sieve

The actual seed image in Y/O₂(Y) is PSL₂(p) when its proper containing
component has quotient PSL₂(p²). The literal two-group kernel identifies
this with the intrinsic seed quotient. A moved seed is PSL₂(4). For a fixed
seed, compare the original residual with the genuine E.2.2 component: its
simple prime-field quotient has two-rank two, excluding both diagram rows
through the actual source map. The remaining rank-one model forces p = 5.
The previously proved original PSL₂(25) exclusion removes the whole family.

Together with the prime-field exclusion, this eliminates every odd PSL₂
constructor of Theorem C on the same selected container. Both Hall
conditions, original Sylow, quotient maps and complete binary-triality
endpoint are retained. The other simple carriers, nonquasisimple branches
and binary-triality exclusion still belong to SourceLocalCartanEscape.

The internal import reuses the intrinsic source comparison in this proof
family, preserving its existing private boundary. Source: Aschbacher--Smith
A.3.12(8), E.2.2 and 5.1.12--13, printed pp.47--48,215--216,635--637,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

private theorem prime_rank {Q : Type*} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p) (hm : ClassicalGroup.IsPSL Q 2 p) :
    primeRank 2 Q = 2 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,hF,ZMod.card])
  rw [primeRank_equiv 2 (e.trans (GorensteinWalter.psl2RingEquiv a))]
  exact Theory.PSL2.primeField_two_rank hgt

private theorem simple_quotient_rank {Q Z : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group Z] [Finite Z]
    (f : Q →* Z) (hf : Function.Surjective f) (hr : primeRank 2 Q = 2) :
    primeRank 2 Z ≤ 2 := by
  rcases subsingleton_or_nontrivial Z with hs | hn
  · let := hs
    have hz : primeRank 2 Z = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by simp)
    omega
  · let := hn
    let e := MulEquiv.ofBijective f ⟨f.injective_of_surjective_of_simple hf,hf⟩
    rw [←primeRank_equiv 2 e,hr]

/-- The odd-prime PSL₂ model of the original normal residual forces prime five. -/
theorem residual_prime_parameter
    {T : Sylow 2 G} {L W H : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hR : (pResidual 2 H).IsCComponent)
    (hp : p.Prime) (ho : Odd p) (hgt : 3 < p)
    (hm : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 p) :
    p = 5 := by
  have hs : IsSimpleGroup ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    exact e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  let := hs
  have hr := prime_rank hp hgt hm
  let S := T.subtype hH.1.1.2
  have hP := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
  let M := ChapterB.minimalParabolicMax S hP
  obtain ⟨K,f,hK,hqs,_,hf,hcases⟩ :=
    ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape.source_binary_cases_generating_knownSimple
      (Chapter3.sqtk_of_mem_H h.qtke hH.1.1.1) S hP hgen
  have hKR : K = pResidual 2 H := by
    apply hK.eq_of_le hR
    let := hK.perfect
    apply le_sInf
    rintro N ⟨hn,hN⟩
    let := hn
    let : Group.IsNilpotent (H ⧸ N) := hN.isNilpotent
    exact (le_solvableResidual_of_isPerfect K).trans (solvableResidual_le_of_solvable_quotient N)
  subst K
  obtain ⟨v,hv⟩ := intrinsic_source_surjection hK (twoCore_le_sourceKernel S hP)
  have hb := simple_quotient_rank v hv hr
  cases hcases with
  | exchanged hc hm =>
    obtain ⟨t,_,hne,_⟩ := hc.exchanged_product
    exact (hne (mem_normalizer_iff_map_conj_eq.mp
      (show t⁻¹ ∈ normalizer (pResidual 2 H : Set H) by
        rw [normalizer_eq_top]; exact mem_top _)).symm).elim
  | diagram hc hd =>
    rcases hd with ⟨F,_,_,_,_,hF,e,_,_⟩ | ⟨F,_,_,_,_,hF,e,_,_⟩
    · rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by omega) hF] at hb
      omega
    · rw [primeRank_equiv 2 e,
        Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derived_rank hF (by omega)] at hb
      omega
  | bender hc hd =>
    have hmodel := Prime.single_bender_component_quotient hK hqs
      (twoCore_le_sourceKernel S hP) hc hd
    have hns : ¬ Group.IsSolvable ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) := by
      let := hK.perfect
      let : Group.IsPerfect ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
        Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
      exact Group.IsPerfect.not_isSolvable _
    exact hmodel.odd_prime_parameter hns hp ho hgt hm

/-- The odd quadratic containing row forces its prime to be five, for the same source seed. -/
theorem quadratic_container_parameter
    {T : Sylow 2 G} {L W H A K Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ 2)) : p = 5 := by
  let S := T.subtype (hH.1.1.2.trans hY.2)
  let q := QuotientGroup.mk' (pCore 2 Y)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  let Kbar := (K.subgroupOf Y).map q
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isNilpotent
  have hlocal : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hH.1.1.2.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hKL⟩
  have hlocalbar : Kbar ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt := seed_image_lt_container h.qtke hKH hH.1.1.2 hKL horbit hY hescape C hC hKC
  obtain ⟨hgt,hsmall⟩ := ChapterA.Section03.SourceEmbeddings.proper_quadraticPSL2_models
    P hlocalbar (hC.map_quotient _) hlt.le hlt.ne hp ho
    (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hC).symm)
  have hns : ¬ Group.IsSolvable Kbar := by
    intro hs
    let := hs
    exact hlocalbar.not_isSolvable
      (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show Kbar ≤ Kbar ⊔ (P : Subgroup (Y ⧸ pCore 2 Y)) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
  have hs : IsSimpleGroup Kbar := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hsmall
    exact e.isSimpleGroup_congr.mpr
      (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  let := hs
  have hz : pCore 2 Kbar = ⊥ := by
    apply (inferInstance : (pCore 2 Kbar).Normal).eq_bot_or_eq_top.resolve_right
    intro he
    let : Group.IsNilpotent (⊤ : Subgroup Kbar) := he ▸ pCore_isNilpotent (p := 2) (G := Kbar)
    exact hns (Group.isSolvable_of_surjective
      (f := (topEquiv (G := Kbar)).toMonoidHom) (topEquiv (G := Kbar)).surjective)
  let r := q.subgroupMap (K.subgroupOf Y)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := (subgroupOfEquivOfLe (hKH.trans hY.2)).symm
  let e₁ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let e₃ : (Kbar ⧸ pCore 2 Kbar) ≃* Kbar :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let eK := e₁.trans (e₂.trans e₃)
  have hprime : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p := hsmall.of_mulEquiv eK
  by_cases he : K = residual H
  · subst K
    have hR : (pResidual 2 H).IsCComponent := by
      simpa only [residual,subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hK
    let aR := (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
    exact residual_prime_parameter h hH hgen hR hp ho hgt
      (hprime.of_mulEquiv (QuotientGroup.congr _ _ aR (pCore_map_iso 2 aR)))
  · have hfour := moved_seed_linear_four_of_escape h.qtke hKL hKT horbit he hY hescape
    have hmodel : ChapterF.Source.IsRankOneModel (K ⧸ pCore 2 K) :=
      .linear 2 (by decide) hfour
    exact hmodel.odd_prime_parameter
      (fun hh => hns (by
        let := hh
        exact Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective))
      hp ho hgt hprime

/-- The full original Cartan escape excludes every odd quadratic-prime PSL₂ container. -/
theorem not_quadratic_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ 2) := by
  intro hm
  have hp5 := quadratic_container_parameter h hH hgen hKH hK hKT hKL horbit hY hescape C hC hKC hp ho hm
  subst p
  exact not_twentyFive_container h hH hgen c hKH hK hKT hKL horbit hY hescape C hC hKC hm

/-- The entire odd PSL₂ family in Theorem C is impossible on the same
original selected container, with no residual or cubic marking assumed. -/
theorem not_odd_linear_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n p e : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hKT : K ⊔ (T : Subgroup G) = H) (hKL : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hp : p.Prime) (ho : Odd p) (he : e = 1 ∨ e = 2) :
    ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ e) := by
  rcases he with rfl | rfl
  · simpa only [pow_one] using not_prime_container h hH hgen c
      hKH hK hqs hKT hKL horbit hY hescape C hC hKC hp ho
  · exact not_quadratic_container h hH hgen c hKH hK hKT hKL horbit
      hY hescape C hC hKC hp ho

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The original same-container reduction excludes both odd PSL₂ exponents,
retaining every structural alternative and the entire binary-triality endpoint. -/
theorem localCartan_escape_seed_oddLinear_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          n = 2 ∧ Nat.card A = 3 ∧ A ≤ C.map Y.subtype ∧
          localBorel T L ≤ omegaCentralizer T ∧
          IsOneOrTwoA5Modules L (layer L W) ∧ Nat.card B = 7 ∧
          B ≤ centralizer
            (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        C.Normal ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 p ∨
            ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 p ∨
            IsSL (C ⧸ pCore 2 C) 3 p ∨ IsSU (C ⧸ pCore 2 C) 3 p)) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Janko4.Model) ∧
        ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) ∧
        (Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M23) →
          K = residual H ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 4 ∧
          Nat.card B = 3) ∧
        (∀ p e : ℕ, p.Prime → Odd p → (e = 1 ∨ e = 2) →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 (p ^ e)) ∧
        let I := C.map (QuotientGroup.mk' (pCore 2 Y))
        Chapter1.Section02.A36Common I ∧
          ((IsSimpleGroup I ∧ TheoremCModel I) ∨
            Chapter1.Section02.A36Natural I ∨ Chapter1.Section02.A36Nilpotent I) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,hstructure⟩ :=
    localCartan_escape_seed_structure_reduction h hH hgen c hY hescape
  exact ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,
    hprime,h25,hCn,hJ,hOdd,hJ4,hM22,hM23,
    fun _ _ hp ho he => LocalSieve.not_odd_linear_container h hH hgen c
      hKH hK hqs hKT hKL hR hY hescape C hC hKC hp ho he,hstructure⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
