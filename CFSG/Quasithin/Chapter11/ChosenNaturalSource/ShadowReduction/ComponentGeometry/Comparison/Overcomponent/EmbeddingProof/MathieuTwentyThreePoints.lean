module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuPoints
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable.PointComparison

/-!
# The M₂₃ proper pairs in source 11.4.2

The complete point catalogue, compared with the actual order of M₂₃,
leaves PSL₃(4), A₇, PSL₂(11), M₂₂ or M₂₃. The last possibility violates
properness. For PSL₂(11), the native heptad and triple two-local orders
kill the point image's two-core. Even characteristic then makes the
full Sylow act faithfully, contradicting the prime-field automorphism
two-rank bound. Thus exactly the three printed Mathieu pairs remain.

The argument retains the original containing quotient, point image and
intrinsic two-cores. Comparison.Overcomponent supplies its actual
chosen-module consumer. The triple M₂₂ containing cover and J₄ comparison,
inner radical placement, strict omega-center containment and equality
remain with this owner. The positive normalized-module input retains
qt-d-1222-normalized-nonff, and earlier-source discharge retains
qt-d-1222-shadow-components. This does not assert unconditional 11.4.2.
Source: Aschbacher--Smith A.3.12 and 11.4.2, printed pp.47--48,776--777.
Imported native carrier results retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No new enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem mathieuTwentyThree_twoLocal_not_eleven
    (S : Sylow 2 Sporadic.Mathieu.M23) (N : Subgroup Sporadic.Mathieu.M23)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup Sporadic.Mathieu.M23) ≤ N) :
    ¬ 11 ∣ Nat.card N := by
  open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry in
  open SylowTwoLocals in
  obtain ⟨i,⟨e⟩⟩ := sylow_maximal_twoLocal_coverage S N hN hSN
  rw [Nat.card_congr e.toEquiv]
  fin_cases i
  · change ¬ 11 ∣ Nat.card heptadStabilizer
    rw [heptadStabilizer_card]
    decide
  · change ¬ 11 ∣ Nat.card tripleStabilizer
    open TripleSolvable in
    obtain ⟨g,hg⟩ := exists_triple_transport
    let a : tripleStabilizer ≃* markedStabilizer :=
      MulAction.stabilizerEquivStabilizer hg.symm
    rw [Nat.card_congr a.toEquiv]
    have hc : Nat.card markedPointStabilizer = 1920 := by
      rw [←Nat.card_congr firstEquivMarkedPoint.toEquiv]
      exact m22PairStabilizer_card
    have hi : markedPointStabilizer.index ≤ 3 := by
      rw [MulAction.index_stabilizer]
      have ho : MulAction.orbit markedStabilizer (9 : Fin 23) ⊆
          (markedTriple : Set (Fin 23)) := by
        intro x hx
        obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hx
        have hm : (9 : Fin 23) ∈ markedTriple := by simp [m22M23AugmentedBlock]
        have hh := Finset.smul_mem_smul_finset (a := g.val) hm
        rwa [show g.val • markedTriple = markedTriple from g.property] at hh
      have hh := Set.ncard_le_ncard ho
      have ht : markedTriple.card = 3 := by decide +kernel
      simpa only [Set.ncard_coe_finset,ht] using hh
    intro hd
    rw [←markedPointStabilizer.card_mul_index,hc] at hd
    rcases (by decide : Nat.Prime 11).dvd_mul.mp hd with hd | hd
    · norm_num at hd
    · have hh := Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite) hd
      omega

/-- The full Sylow of M₂₃ cannot normalize a local PSL₂(11) section.
The two-core is killed by the actual two-local orders, then the faithful
Sylow action contradicts the prime-field automorphism rank bound. -/
theorem mathieuTwentyThree_not_eleven
    (S : Sylow 2 Sporadic.Mathieu.M23) (C : Subgroup Sporadic.Mathieu.M23)
    (hC : C ∈ localCComponents S)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hn : (S : Subgroup Sporadic.Mathieu.M23) ≤ normalizer (C : Set _))
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
    exact mathieuTwentyThree_twoLocal_not_eleven S N hN hSN ((by decide : 11 ∣ 660).trans hd)
  let v : C ≃* (C ⧸ pCore 2 C) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv v.symm
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.m23_evenCharacteristic S) hC hn
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
  have := Sporadic.Mathieu.m23_four_le_twoRank
  have := Theory.PSL2.primeField_automorphism_two_rank (p := 11) (by decide)
  omega

private theorem fieldFour_mathieuTwentyThree_cases {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 10200960) :
    (IsAlternating A 7 ∨ ClassicalGroup.IsPSL A 2 11) ∨ (Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ Nonempty (A ≃* Sporadic.Mathieu.M23)) := by
  have hb := Nat.le_of_dvd (by decide : 0 < 10200960) hd
  cases hm with
  | alternating hm => exact .inl (.inl hm)
  | alternatingCover hm =>
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
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
    rw [show 10200960 = 2^7*3^2*5*7*11*23 by decide] at hpN
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
    exact .inl (.inr (he ▸ hm))
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm =>
    obtain ⟨hdiv,hl,_⟩ := odd_ternary_five_card_bounds u hm
    have hh : Nat.card A ∣ 10080 := by
      rcases hdiv with hdiv | hdiv
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
    have := Nat.le_of_dvd (by decide : 0 < 10080) hh
    omega
  | m22 hm => exact .inr (.inl hm)
  | m22Cover hm =>
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  | m23 hm => exact .inr (.inr hm)
  | j1 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | j2 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
    norm_num at hd
  | j4 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hb
    omega
  | hs hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hb
    omega
  | ru hm =>
    rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card] at hb
    omega
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim

private theorem fieldFour_lie_mathieuTwentyThree
    {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2)
    (hd : Nat.card A ∣ 10200960) : ClassicalGroup.IsPSL A 3 4 := by
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
    rw [Nat.card_congr e.toEquiv,←(center SL(3,F)).card_mul_index,index_eq_card,
      hcenter,hproj] at hd
    norm_num at hd
  | psl3 hm => exact hm
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
    exact (by norm_num : ¬ (2^2)^12 ∣ 10200960) (hu.trans hd) |>.elim
  | trialityCube m hm he _ => omega


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The M₂₃ containing row of the complete source catalogue gives
exactly the original PSL₃(4), A₇ or M₂₂ proper pair. All models refer
to the original intrinsic two-core quotients. -/
theorem ofFlag_mathieuTwentyThree_proper_pair
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
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23)) :
    QuasisimplePair (ofFlag S f X z H).Kz J := by
  obtain ⟨b⟩ := hm
  let := point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inr (.inr ⟨b⟩))))
  obtain ⟨P,C,hC,hproper,hPC,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt b
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv a
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 10200960 := by
    rw [Nat.card_congr a.toEquiv,←Sporadic.Mathieu.m23_order]
    exact (card_quotient_dvd_card (pCore 2 C)).trans C.card_subgroup_dvd_card
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ hlt).1
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
  | lie hm =>
    rw [hdegree] at hm
    exact .linearFourMathieu (fieldFour_lie_mathieuTwentyThree hm hd) ⟨b⟩
  | four _ hm =>
    rcases fieldFour_mathieuTwentyThree_cases (pCore_quotient_pCore_eq_bot 2) hm hd with
      (hseven | heleven) | (htwo | hself)
    · exact .alternatingMathieu hseven ⟨b⟩
    · exact (mathieuTwentyThree_not_eleven P C hC hPC (heleven.of_mulEquiv a.symm)).elim
    · exact .mathieu htwo ⟨b⟩
    · exfalso
      apply hproper
      apply C.eq_top_of_card_eq
      apply le_antisymm (Nat.card_le_card_of_injective C.subtype C.subtype_injective)
      rw [←Nat.card_congr (a.symm.trans hself.some).toEquiv]
      exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
        (QuotientGroup.mk'_surjective _)

/-- The complete source comparison now gives a proved proper embedding,
or one of the two remaining containing rows. Both point-quasisimplicity
branches and the original quintic extension pair are retained. -/
theorem ofFlag_proper_embedding_or_cover_or_jankoFour
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
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨
        IsM22Cover (J ⧸ pCore 2 J) ∨ Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  by_cases hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
  · obtain ⟨hd,hcover | hmathieu | hjanko⟩ := ofFlag_quasisimple_point_cover_or_large_container
      S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
    · exact ⟨hd,.inr (.inl hcover)⟩
    · have hp := ofFlag_mathieuTwentyThree_proper_pair
        S f X z H h hne hlinear h1132 e hJ.1 hlt hmathieu
      have hq := ofFlag_proper_overcomponent_quasisimple
        S f X z H h hne hlinear h1132 e hcent hJ hlt
      exact ⟨hd,.inl (.quasisimple hp hq)⟩
    · exact ⟨hd,.inr (.inr hjanko)⟩
  · obtain ⟨hd,_,_,hp⟩ := ofFlag_nonquasisimple_proper_pair
      S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
    exact ⟨hd,.inl hp⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
