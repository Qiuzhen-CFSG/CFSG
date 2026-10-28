module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.JankoOnePoints
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.MathieuTwentyTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.JankoFirstCentralizer
public import Theory.Mathieu.TwoRankLower
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.Triality.ConcreteBruhat.FixedCellCount

/-!
# Excluding the M₂₂ containing quotient in 11.4.2

The actual full-Sylow two-locals of M₂₂ have orders dividing 5760, by
the native pair/hexad placement. Thus the A₇ and PSL₂(11) point rows
have trivial two-core. Even characteristic makes the full Sylow act
faithfully, contradicting their automorphism order or rank. The existing
index-22 calculation excludes the PSL₃(4) row. Order divisibility excludes
all remaining rows of the complete point catalogue, retaining the odd
extensions and covers; an equal-order image contradicts properness.

The original chosen-module application in Comparison.Overcomponent now
leaves only the triple M₂₂ cover, M₂₃ and J₄ as quasisimple-point
containers. Their remaining comparisons, inner radical placement, strict
omega-center containment and final equality stay with this owner.
The positive normalized-module input retains qt-d-1222-normalized-nonff;
earlier-source discharge stays with qt-d-1222-shadow-components.
This is a proper-container comparison, not unconditional 11.4.2.
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

private theorem mathieuTwoLocal_order (S : Sylow 2 Sporadic.Mathieu.M22)
    (Y : Subgroup Sporadic.Mathieu.M22) (hY : IsMaximalTwoLocal Y)
    (hSY : (S : Subgroup Sporadic.Mathieu.M22) ≤ Y) : Nat.card Y ∣ 5760 := by
  open Sporadic.Mathieu MulAction in
  obtain ⟨A,hA,hEA,hYA⟩ := exists_elementary_normalizer_of_isMaximalTwoLocal hY
  let := hEA
  have hAY : A ≤ Y := hYA.symm ▸ A.le_normalizer
  let E := A.subgroupOf Y
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hAY).mpr (hYA ▸ le_rfl)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hAY
  have hE : E ≠ ⊥ := by
    intro h
    apply hA
    rw [←map_subgroupOf_eq_of_le hAY,show A.subgroupOf Y = E from rfl,h,Subgroup.map_bot]
  rcases M22SolvableSylow.coverage_of_not_pretransitive Y ⟨S,hSY⟩
    (M22TwoLocalOrders.not_pretransitive_of_normal_elementary Y E hE) with
      ⟨B,hB,hYB⟩ | ⟨B,hB,hYB⟩
  · have hd := card_dvd_of_le hYB
    rwa [m22Hexad_stabilizer_card hB] at hd
  · obtain ⟨g,hg⟩ := M22SolvableSylow.LocalClassification.exists_smul_pair_eq_standard hB
    have hmap := map_mono (f := (MulAut.conj g).toMonoidHom) hYB
    rw [←stabilizer_smul_eq_stabilizer_map_conj g B,hg] at hmap
    have hd := card_dvd_of_le hmap
    change Nat.card (Y.map (MulAut.conj g).toMonoidHom) ∣ Nat.card m22PairStabilizer at hd
    rw [card_map_of_injective (MulAut.conj g).injective,m22PairStabilizer_card] at hd
    exact hd.trans (by decide)

private theorem mathieuPoint_core (S : Sylow 2 Sporadic.Mathieu.M22)
    (C : Subgroup Sporadic.Mathieu.M22)
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (C : Set _))
    (hd : ¬ Nat.card (C ⧸ pCore 2 C) ∣ 5760) : pCore 2 C = ⊥ := by
  by_contra hc
  obtain ⟨N,hN,hCN,hSN⟩ := FiveLocalFF.SolvableQuotients.exists_maximal_two_local S C hn hc
  exact hd ((card_quotient_dvd_card _).trans ((card_dvd_of_le hCN).trans
    (mathieuTwoLocal_order S N hN hSN)))

private theorem mathieuPoint_aut_embedding (S : Sylow 2 Sporadic.Mathieu.M22)
    (C : Subgroup Sporadic.Mathieu.M22) (hC : C ∈ localCComponents S)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (C : Set _))
    (hd : ¬ Nat.card (C ⧸ pCore 2 C) ∣ 5760) :
    ∃ a : S →* MulAut (C ⧸ pCore 2 C), Function.Injective a := by
  have hc := mathieuPoint_core S C hn hd
  let e : C ≃* (C ⧸ pCore 2 C) := QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hc).symm
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  have hfaith := sylow_centralizer_eq_bot_of_evenCharacteristic S
    (MainConverse.m22_evenCharacteristic S) hC hn
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
  exact ⟨(MulAut.congr e).toMonoidHom.comp a,(MulAut.congr e).injective.comp hi⟩

private theorem mathieuPoint_not_small (S : Sylow 2 Sporadic.Mathieu.M22)
    (C : Subgroup Sporadic.Mathieu.M22) (hC : C ∈ localCComponents S)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (C : Set _))
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 11) : False := by
  rcases hm with hseven | hm
  · let e := hseven.some
    have hc : Nat.card (C ⧸ pCore 2 C) = 2520 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    obtain ⟨a,ha⟩ := mathieuPoint_aut_embedding S C hC hn (by rw [hc]; decide)
    let b : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        7 (by decide) (by decide))
    have hd := card_dvd_of_injective a ha
    rw [Nat.card_congr (MulAut.congr e).toEquiv,←Nat.card_congr b.toEquiv,
      Nat.card_perm,Nat.card_fin] at hd
    have h128 : 128 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 7) (by
      rw [Sporadic.Mathieu.m22_order]; decide)
    exact (by decide : ¬128 ∣ Nat.factorial 7) (h128.trans hd)
  · obtain ⟨F,_,_,hF,⟨b⟩⟩ := hm
    let : Fact (Nat.Prime 11) := ⟨by decide⟩
    have hc : Nat.card (C ⧸ pCore 2 C) = 660 := by
      rw [Nat.card_congr b.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
      norm_num
    let : Fintype F := Fintype.ofFinite F
    let r : F ≃+* ZMod 11 := FiniteField.ringEquivOfCardEq
      (show Fintype.card F = Fintype.card (ZMod 11) by
        simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let e := b.trans (Atlas.fieldEquivPSL 2 r)
    obtain ⟨a,ha⟩ := mathieuPoint_aut_embedding S C hC hn (by rw [hc]; decide)
    have hh := Theory.GroupTheory.primeRank_le_of_injective 2 a ha
    rw [primeRank_equiv 2 (MulAut.congr e),←S.primeRank_eq] at hh
    have := Sporadic.Mathieu.m22_four_le_twoRank
    have := Theory.PSL2.primeField_automorphism_two_rank (p := 11) (by decide)
    omega

/-- The full Sylow action excludes the two small simple point sections in M₂₂. -/
theorem mathieuPoint_not_small_section (S : Sylow 2 Sporadic.Mathieu.M22)
    (C : Subgroup Sporadic.Mathieu.M22) (hC : C ∈ localCComponents S)
    [IsQuasisimple (C ⧸ pCore 2 C)]
    (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (C : Set _))
    (hm : IsAlternating (C ⧸ pCore 2 C) 7 ∨ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 11) : False :=
  mathieuPoint_not_small S C hC hn hm

private theorem fieldFour_mathieuPoint_cases {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 443520) :
    (IsAlternating A 7 ∨ ClassicalGroup.IsPSL A 2 11) ∨ Nonempty (A ≃* Sporadic.Mathieu.M22) := by
  have hb := Nat.le_of_dvd (by decide : 0 < 443520) hd
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
    rw [show 443520 = 2^7*3^2*5*7*11 by decide] at hpN
    simp only [hp.1.dvd_mul,or_assoc] at hpN
    have he : p = 11 := by
      rcases hpN with h | h | h | h | h
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_two h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_three h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_five).mp h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · have he := (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 7)).mp h
        have hx := hp.2.1; rw [he] at hx; norm_num at hx
      · exact (Nat.prime_dvd_prime_iff_eq hp.1 (by decide : Nat.Prime 11)).mp h
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
  | m22 hm => exact .inr hm
  | m22Cover hm =>
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  | m23 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hb
    omega
  | j1 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | j2 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hb
    omega
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

private theorem fieldFour_lie_mathieuPoint_card
    {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2)
    (hd : Nat.card A ∣ 443520) : Nat.card A = 20160 := by
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
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF]
    norm_num
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
    exact (by norm_num : ¬ (2^2)^12 ∣ 443520) (hu.trans hd) |>.elim
  | trialityCube m hm he _ => omega

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The native M₂₂ quotient cannot properly contain the source point.
The proof exhausts its literal point catalogue and full Sylow action. -/
theorem ofFlag_not_mathieuTwentyTwo_overcomponent
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
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M22) := by
  rintro ⟨b⟩
  let := point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inl ⟨b⟩)))
  obtain ⟨P,C,hC,hproper,hPC,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt b
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_mulEquiv a
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 443520 := by
    rw [Nat.card_congr a.toEquiv,←Sporadic.Mathieu.m22_order]
    exact (card_quotient_dvd_card (pCore 2 C)).trans C.card_subgroup_dvd_card
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ hlt).1
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact (h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he
  | lie hm =>
    rw [hdegree] at hm
    have hc := fieldFour_lie_mathieuPoint_card hm hd
    rw [Nat.card_congr a.toEquiv] at hc
    exact Exceptional.not_mathieu_twentyTwo_of_section_card P C hPC hc (MulEquiv.refl _)
  | four _ hm =>
    rcases fieldFour_mathieuPoint_cases (pCore_quotient_pCore_eq_bot 2) hm hd with hm | hm
    · apply mathieuPoint_not_small P C hC hPC
      rcases hm with hseven | hm
      · exact .inl ⟨a.symm.trans hseven.some⟩
      · exact .inr (hm.of_mulEquiv a.symm)
    · obtain ⟨aM⟩ := hm
      apply hproper
      apply C.eq_top_of_card_eq
      apply le_antisymm (Nat.card_le_card_of_injective C.subtype C.subtype_injective)
      rw [←Nat.card_congr (a.symm.trans aM).toEquiv]
      exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
        (QuotientGroup.mk'_surjective _)

/-- The complete containing catalogue now leaves only the triple M₂₂
cover, M₂₃ and J₄ in the quasisimple-point branch. No reduced catalogue
is assumed, and every model is on the original two-core quotient. -/
theorem ofFlag_quasisimple_point_cover_or_large_container
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
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
      (IsM22Cover (J ⧸ pCore 2 J) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.Mathieu.M23) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  obtain ⟨hd,hm⟩ := ofFlag_quasisimple_point_mathieu_jankoFour_containers
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  refine ⟨hd,?_⟩
  rcases hm with hm | hm
  · exact (ofFlag_not_mathieuTwentyTwo_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt hm).elim
  · exact hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
