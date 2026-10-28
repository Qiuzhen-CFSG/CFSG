module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuCoverPoints
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyFour
public import Theory.Mathieu.M24.LocalGeometry.OctadOrder

/-!
# Excluding the Mathieu local subgroup in the original J₄ comparison

For the chosen flag of 11.4.2, the original point section cannot be a local
section of M₂₄ normalized by a full Sylow two-subgroup. We exhaust the full
11.1.1 catalogue, using the native seven-section comparison and the
PSL₂(11) automorphism-rank bound. Descent through the actual binary kernel
of J₄'s Mathieu local subgroup then excludes simultaneous containment of
the point image and the full Sylow, including after conjugation.

This supplies the Mathieu-local exclusion in the A.3.12 comparison used by
Aschbacher–Smith, *The Classification of Quasithin Groups*, 11.4.2,
printed pp. 776–777. All model data come from the imported native modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem mathieuTwentyFour_fixed_twoLocal_not_eleven
    (N : Subgroup Sporadic.Mathieu.M24) (hN : IsMaximalTwoLocal N)
    (hSN : Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate ≤ N) :
    ¬ 11 ∣ Nat.card N := by
  open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry in
  open PairOvergroups PairOvergroups.QuotientConstruction in
  let S : Sylow 2 M24 := Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]; decide +kernel)
  obtain ⟨R,hR,hnR,heR,hNR⟩ := exists_normal_elementary_normalizer_of_sylow_le S hN hSN
  obtain ⟨i,hi⟩ := MainConverse.M24Even.normalElementaryCatalogue R hR hnR heR
  have he : N = EvenCatalogue.localGroup i := by rw [hNR,hi]; rfl
  rw [he]
  intro hd
  rcases EvenCatalogue.normalizerOvergroups i with ⟨O,hO⟩ | ⟨k,hk⟩
  · have hh := hd.trans (card_dvd_of_le hO)
    rw [octadStabilizer_card O] at hh
    norm_num at hh
  · have hh := hd.trans (card_dvd_of_le hk)
    fin_cases k
    · change 11 ∣ Nat.card (EvenCandidates.localGroup 0) at hh
      rw [Nat.card_congr EvenCatalogue.NormalSeeds.trioNormalizerEquiv.toEquiv] at hh
      let q := affineQuotient affineCoverage
      obtain ⟨n,hn⟩ := (affineQuotient_kernel_isPGroup affineCoverage).exists_card_eq
      have hc := q.ker.card_mul_index
      rw [index_ker,hn] at hc
      have hr : Nat.card q.range ∣ 1008 := by
        have h := q.range.card_subgroup_dvd_card
        rw [Nat.card_prod,Matrix.PSL3Two.card_SL] at h
        simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,
          show Nat.factorial 3 = 6 from rfl] using h
      have h11 : 11 ∣ 2^n*1008 := (hc ▸ hh).trans (Nat.mul_dvd_mul_left _ hr)
      have := ((by decide : Nat.Coprime 11 2).pow_right n).dvd_of_dvd_mul_left h11
      norm_num at this
    · change 11 ∣ Nat.card (EvenCandidates.localGroup 1) at hh
      rw [Nat.card_congr EvenCatalogue.NormalSeeds.sextetNormalizerEquiv.toEquiv,
        SextetCore.stabilizer_card] at hh
      norm_num at hh

private theorem mathieuTwentyFour_twoLocal_not_eleven
    (S : Sylow 2 Sporadic.Mathieu.M24) (N : Subgroup Sporadic.Mathieu.M24)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup Sporadic.Mathieu.M24) ≤ N) :
    ¬ 11 ∣ Nat.card N := by
  open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry in
  let P : Sylow 2 M24 := Sylow.ofCard SylowNormalizer.candidate (by
    rw [SylowNormalizer.candidate_card,m24_order]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S P
  let e := MulAut.conj g
  have hP : (S : Subgroup M24).map e.toMonoidHom = SylowNormalizer.candidate :=
    congrArg Sylow.toSubgroup hg
  have hN' : IsMaximalTwoLocal (N.map e.toMonoidHom) := by
    exact Theory.Quasithin.isMaximalTwoLocal_map e hN
  have hPN : SylowNormalizer.candidate ≤ N.map e.toMonoidHom := hP ▸ map_mono hSN
  simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using
    mathieuTwentyFour_fixed_twoLocal_not_eleven _ hN' hPN

/-- The native full Sylow of M₂₄ cannot normalize a local PSL₂(11) section. -/
theorem mathieuTwentyFour_not_eleven
    (S : Sylow 2 Sporadic.Mathieu.M24) (C : Subgroup Sporadic.Mathieu.M24)
    (hC : C ∈ localCComponents S)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hn : (S : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (C : Set _))
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 11) : False := by
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hm
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hcard : Nat.card (C ⧸ pCore 2 C) = 660 := by
    rw [Nat.card_congr b.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
    norm_num
  have hc : pCore 2 C = ⊥ := by
    by_contra hc
    obtain ⟨N,hN,hCN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local S C hn hc
    have hd := (card_quotient_dvd_card (pCore 2 C)).trans (card_dvd_of_le hCN)
    rw [hcard] at hd
    exact mathieuTwentyFour_twoLocal_not_eleven S N hN hSN ((by decide : 11 ∣ 660).trans hd)
  let v : C ≃* (C ⧸ pCore 2 C) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv v.symm
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.m24_evenCharacteristic S) hC hn
  let a := C.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfaith]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ C.normalizerMonoidHom.ker at hx
    rwa [normalizerMonoidHom_ker] at hx
  let : Fintype F := Fintype.ofFinite F
  let r : F ≃+* ZMod 11 := FiniteField.ringEquivOfCardEq
    (show Fintype.card F = Fintype.card (ZMod 11) by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := v.trans (b.trans (Atlas.fieldEquivPSL 2 r))
  have hh := Theory.GroupTheory.primeRank_le_of_injective 2 a hi
  rw [primeRank_equiv 2 (MulAut.congr e),←S.primeRank_eq] at hh
  have := Sporadic.Mathieu.m24_six_le_twoRank
  have := Theory.PSL2.primeField_automorphism_two_rank (p := 11) (by decide)
  omega

private def MathieuPointComparison (A : Type*) [Group A] : Prop :=
  Exceptional.IsModel A ∨
    (7 ∣ Nat.card A ∧ Nat.card A ≠ 20160 ∧ Nat.card A ≠ 244823040 ∧ 168 < Nat.card A) ∨
    ClassicalGroup.IsPSL A 2 11

private theorem comparison_of_card {A : Type*} [Group A]
    {n : ℕ} (hn : Nat.card A = n) (h7 : 7 ∣ n) (h1 : n ≠ 20160)
    (h2 : n ≠ 244823040) (h3 : 168 < n) : MathieuPointComparison A := by
  exact .inr (.inl (hn ▸ ⟨h7,h1,h2,h3⟩))

private theorem fieldFour_mathieuLocal_lie {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2)
    (hd : Nat.card A ∣ 244823040) : MathieuPointComparison A := by
  cases hm with
  | sl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hcenter : Nat.card (center SL(3,F)) = 3 := by
      apply Matrix.SL3.card_center_eq_three_of_ne_bot F
      intro hz
      have hx := (Matrix.SL3.center_eq_bot_iff_card_mod_three F).mp hz
      rw [hF] at hx
      norm_num at hx
    have hproj : Nat.card PSL(3,F) = 20160 := by
      rw [Matrix.PSL3.LinearThree.card_projective,hF]; norm_num
    have hc : Nat.card A = 60480 := by
      rw [Nat.card_congr e.toEquiv,←(center SL(3,F)).card_mul_index,index_eq_card,hcenter,hproj]
    exact comparison_of_card hc (by decide) (by decide) (by decide) (by decide)
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
    let r : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F,show 2^2 = 4 from rfl] using hF)
    exact .inl (.inr (.inr ⟨e.trans (Atlas.fieldEquivPSL 3 r)⟩))
  | sp4 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Theory.SpecificGroups.SymplecticFour.card_sp F,hF] at hd
    norm_num at hd
  | g2 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Atlas.G2.card_Model,hF] at hd
    norm_num at hd
  | ree m hm he _ => omega
  | triality hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
    rw [Nat.card_congr e.toEquiv] at hd
    have hu := (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters 2 (by decide))).card_subgroup_dvd_card
    rw [Triality.Standard.ConcreteBruhat.FixedCellCount.card_unipotent,
      Triality.Standard.binaryParameters_q] at hu
    exact (by norm_num : ¬ (2^2)^12 ∣ 244823040) (hu.trans hd) |>.elim
  | trialityCube m hm he _ => omega

private theorem fieldFour_mathieuLocal_cases {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 244823040) : MathieuPointComparison A := by
  have hb := Nat.le_of_dvd (by decide : 0 < 244823040) hd
  cases hm with
  | alternating hm =>
    have he : Nat.card A = 2520 := by
      rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact comparison_of_card he (by decide) (by decide) (by decide) (by decide)
  | alternatingCover hm =>
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    have he : Nat.card A = 7560 := by
      rw [←(center A).card_mul_index,index_eq_card,hz,
        Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact comparison_of_card he (by decide) (by decide) (by decide) (by decide)
  | primeLinear p hp hm =>
    have hpd : p ∣ Nat.card A := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have ho : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp.1,ho,by decide,by simpa using hF⟩,hF]
      have he : 2 ∣ p^2-1 := by
        obtain ⟨a,ha⟩ := ho
        refine ⟨2*a*(a+1),?_⟩
        nlinarith [Nat.sub_add_cancel (show 1 ≤ p^2 by have := hp.1.two_le; nlinarith)]
      apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right he p)).mpr
      simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) he
    have hpN := hpd.trans hd
    rw [show 244823040 = 2^10*3^3*5*7*11*23 by decide] at hpN
    simp only [hp.1.dvd_mul,or_assoc] at hpN
    have he : p = 11 := by
      rcases hpN with h | h | h | h | h | h
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_two h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_three h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_five).mp h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 7)).mp h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · exact (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 11)).mp h
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 23)).mp h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
    exact .inr (.inr (he ▸ hm))
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm =>
    obtain ⟨hdiv,hl,_⟩ := odd_ternary_five_card_bounds u hm
    have hh : Nat.card A ∣ 30240 := by
      rcases hdiv with hdiv | hdiv
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
    have := Nat.le_of_dvd (by decide : 0 < 30240) hh
    omega
  | m22 hm =>
    have he : Nat.card A = 443520 := (Nat.card_congr hm.some.toEquiv).trans Sporadic.Mathieu.m22_order
    exact comparison_of_card he (by decide) (by decide) (by decide) (by decide)
  | m22Cover hm =>
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    have he : Nat.card A = 1330560 := by
      rw [←(center A).card_mul_index,index_eq_card,hz,
        Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]
    exact comparison_of_card he (by decide) (by decide) (by decide) (by decide)
  | m23 hm => exact .inl (.inr (.inl hm))
  | j1 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | j2 hm => exact .inl (.inl hm)
  | j4 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hb
    omega
  | hs hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hd
    norm_num at hd
  | ru hm =>
    rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card] at hb
    omega
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

private theorem mathieuTwentyFour_no_point_comparison
    (hsq : IsSQTK KnownSimple.IsKnownSimple Sporadic.Mathieu.M24)
    (S : Sylow 2 Sporadic.Mathieu.M24) (B : Subgroup Sporadic.Mathieu.M24)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (B : Set _))
    [IsQuasisimple (B ⧸ pCore 2 B)] (hm : MathieuPointComparison (B ⧸ pCore 2 B)) : False := by
  rcases hm with hex | ⟨h7,h1,h2,h3⟩ | h11
  · exact Exceptional.not_mathieu_twentyFour S B hB hn hex (MulEquiv.refl _)
  · rcases JankoMathieu.mathieu_local_models (MulEquiv.refl _) hsq S B hB hn inferInstance h7 with
      hsmall | hfour | hmathieu
    · omega
    · apply h1
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hfour
      let : Fintype F := Fintype.ofFinite F
      let r : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
      let a := e.trans ((Atlas.fieldEquivPSL 4 r).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
      rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · exact h2 ((Nat.card_congr hmathieu.some.toEquiv).trans Sporadic.Mathieu.m24_order)
  · exact mathieuTwentyFour_not_eleven S B hB hn h11

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The full original point catalogue cannot occur as a full-Sylow-normalized
local section of native M₂₄. This retains the point's intrinsic two-core quotient. -/
theorem ofFlag_not_mathieuTwentyFour_section
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hdegree : S.field.degree = 2)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Sporadic.Mathieu.M24)
    (P : Sylow 2 Sporadic.Mathieu.M24) (B : Subgroup Sporadic.Mathieu.M24)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (B : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (B ⧸ pCore 2 B)) : False := by
  let := IsQuasisimple.of_mulEquiv a
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 244823040 := by
    rw [Nat.card_congr a.toEquiv,←Sporadic.Mathieu.m24_order]
    exact (card_quotient_dvd_card _).trans B.card_subgroup_dvd_card
  have hm : MathieuPointComparison ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
    cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
    | equal he =>
      exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
    | lie hm =>
      rw [hdegree] at hm
      exact fieldFour_mathieuLocal_lie hm hd
    | four _ hm => exact fieldFour_mathieuLocal_cases (pCore_quotient_pCore_eq_bot 2) hm hd
  apply mathieuTwentyFour_no_point_comparison hsq P B hB hn
  rcases hm with hex | ⟨h7,h1,h2,h3⟩ | h11
  · exact .inl (hex.of_equiv a.symm)
  · exact .inr (.inl (by
      rw [←Nat.card_congr a.toEquiv]
      exact ⟨h7,h1,h2,h3⟩))
  · exact .inr (.inr (h11.of_mulEquiv a.symm))

open Janko4 Janko4.Cardinality Janko4.LocalStructure in
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel

/-- The original point section and the full normalizing Sylow cannot both
lie in J₄'s actual M₂₄ local subgroup. The binary kernel is removed by the
literal quotient map and both intrinsic two-core quotients are preserved. -/
theorem ofFlag_jankoFour_not_pair_le_mathieuLocal
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hdegree : S.field.degree = 2)
    (hsq : IsSQTK KnownSimple.IsKnownSimple Janko4.Model)
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (B ⧸ pCore 2 B))
    (hBM : B ≤ Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    (hPM : (P : Subgroup Janko4.Model) ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) : False := by
  open Janko4 Janko4.Cardinality Janko4.LocalStructure in
  open FiveLocalFF.SolvableQuotients in
  let M := max1Subgroup matrixA_mul_self matrixB_pow_four
  let K := localKernel matrixA_mul_self matrixB_pow_four
  let q := QuotientGroup.mk' K
  let b := localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
  let g := b.toMonoidHom.comp q
  have hg : Function.Surjective g := b.surjective.comp (QuotientGroup.mk'_surjective K)
  have hker : g.ker = K := by
    rw [MonoidHom.ker_comp_of_injective _ _ b.injective,QuotientGroup.ker_mk']
  have hp : IsPGroup 2 K := by
    let := localKernel_elementary matrixA_mul_self matrixB_pow_four
    exact IsElementaryAbelian.isPGroup 2 K
  let : Group.IsSolvable g.ker := by
    rw [hker]
    let := hp.isNilpotent
    infer_instance
  have hkB : IsPGroup 2 (g.subgroupMap (B.subgroupOf M)).ker := by
    rw [ker_subgroupMap,hker]
    exact hp.comap_subtype
  let d := subgroupOfEquivOfLe hBM
  let a' := a.trans ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans
    ((g.subgroupMap (B.subgroupOf M)).pCoreQuotientEquiv (g.subgroupMap_surjective _) hkB))
  have hn' : (P.subtype hPM : Subgroup M) ≤ normalizer (B.subgroupOf M : Set M) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Janko4.Model)
  exact ofFlag_not_mathieuTwentyFour_section S f X z H h hne hlinear h1132 e hdegree
    ((ChapterE.Structure.sqtk_two_quotient (hsq.subgroup M) K hp).knownSimple_of_equiv b)
    ((P.subtype hPM).mapSurjective hg) ((B.subgroupOf M).map g)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker (local_restrict hB hBM) g)
    ((map_mono hn').trans ((B.subgroupOf M).le_normalizer_map g)) a'

/-- Every literal point image in the J₄ containing quotient avoids all
conjugates of the actual Mathieu local subgroup, together with its full Sylow.
The source field-four and point-quasisimplicity premises are discharged here. -/
theorem ofFlag_jankoFour_point_avoids_mathieuLocal
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J)
    (b : (J ⧸ pCore 2 J) ≃* Janko4.Model)
    (P : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents P)
    (hn : (P : Subgroup Janko4.Model) ≤ normalizer (B : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (B ⧸ pCore 2 B)) :
    ∀ g : Janko4.Model, ¬
      (B.map (MulAut.conj g).toMonoidHom ≤
          Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∧
        (P : Subgroup Janko4.Model).map (MulAut.conj g).toMonoidHom ≤
          Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four) := by
  let := point_quasisimple_in_jankoFour h hJ hlt b
  have hd := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  have hl := (Chapter1.Section02.Adequate.mem_L_iff_mainForward T J).mp hJ
  obtain ⟨_,_,_,_,hsq⟩ := MainForward.localComponents_local_setup S.source.simpleQTKE T hl
  have hs : IsSQTK KnownSimple.IsKnownSimple J :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))).mp
      (hsq.subgroup (J.subgroupOf (J ⊔ (T : Subgroup G))))
  have hq := (ChapterE.Structure.sqtk_two_quotient hs (pCore 2 J) pCore_isPGroup).knownSimple_of_equiv b
  intro g ⟨hBM,hPM⟩
  let v := MulAut.conj g
  let d := v.subgroupMap B
  let aq := a.trans (QuotientGroup.congr _ _ d (pCore_map_iso 2 d))
  let : Group.IsSolvable v.toMonoidHom.ker := by
    rw [v.toMonoidHom.ker_eq_bot v.injective]
    infer_instance
  exact ofFlag_jankoFour_not_pair_le_mathieuLocal S f X z H h hne hlinear h1132 e hd hq
    (P.mapSurjective (f := v.toMonoidHom) v.surjective) (B.map v.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB v.toMonoidHom)
    ((map_mono hn).trans (B.le_normalizer_map v.toMonoidHom)) aq hBM hPM

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
