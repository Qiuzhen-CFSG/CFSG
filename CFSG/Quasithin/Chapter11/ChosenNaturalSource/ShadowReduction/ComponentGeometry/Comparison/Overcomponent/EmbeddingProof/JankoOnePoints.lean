module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SectionOrderPoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstJankoModels
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Excluding the J₁ containing quotient in 11.4.2

The full point catalogue in a J₁ containing quotient reduces by order and
rank to a prime-field PSL₂ quotient or J₁ itself. Equal orders exclude the
latter for the literal proper point image. In the prime-field case,
perfectness and J₁'s elementary abelian Sylows kill the image's two-core.
Its order cannot divide the order 120 of an involution centralizer, so the
full Sylow acts faithfully. Its rank three contradicts the automorphism
rank bound two for prime-field PSL₂. The original quotients and the full
Sylow normalization are retained throughout.

Comparison.Overcomponent applies this to the actual chosen module. The
remaining Mathieu/J₄ comparisons, inner radical placement, strict
omega-center containment and equality stay with this comparison owner.
The positive normalized-module implication retains its independent producer
qt-d-1222-normalized-nonff; earlier-source discharge stays with
qt-d-1222-shadow-components. This does not assert full 11.4.2.
Source: Aschbacher--Smith A.3.12 and 11.4.2, printed pp.47--48,776--777.
Imported J₁ carrier calculations retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No new carrier data is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem fieldFour_lie_rank_four
    {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2) : 4 ≤ primeRank 2 A := by
  cases hm with
  | sl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e]
    have hh := primeRank_quotient_le_of_coprime 2 (center SL(3,F))
      (Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center F))
    change primeRank 2 PSL(3,F) ≤ _ at hh
    rw [Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF] at hh
    omega
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF]
  | sp4 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by decide)]
    decide
  | g2 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Atlas.G2.EvenTwoRank.two_rank F hF]
    decide
  | ree m hm he _ => omega
  | triality hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
    rw [primeRank_equiv 2 e]
    exact le_trans (by decide : 4 ≤ 3 * 2)
      (Triality.Standard.TwoRank.twoRank_ge_three_mul 2 (by decide))
  | trialityCube m hm he _ => omega

private theorem fieldFour_jankoOne_prime_or_self
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 175560) :
    (∃ p, Source.ExceptionalPrime p ∧ ClassicalGroup.IsPSL A 2 p) ∨
      Nonempty (A ≃* Janko1.Model) := by
  have hb : Nat.card A ≤ 175560 := Nat.le_of_dvd (by decide) hd
  cases hm with
  | alternating hm =>
    rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
  | alternatingCover hm =>
    have hh := (card_quotient_dvd_card (center A)).trans hd
    rw [Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  | primeLinear p hp hm => exact .inl ⟨p,hp,hm⟩
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm =>
    obtain ⟨hdiv,hl,hu⟩ := odd_ternary_five_card_bounds u hm
    have hh : Nat.card A ∣ 840 := by
      rcases hdiv with hdiv | hdiv
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
      · have hh := Nat.dvd_gcd hd hdiv
        norm_num at hh
        exact hh.trans (by decide)
    have := Nat.le_of_dvd (by decide : 0 < 840) hh
    omega
  | m22 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order] at hb
    omega
  | m22Cover hm =>
    have hh := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center A))
      (QuotientGroup.mk'_surjective (center A))
    rw [Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hh
    omega
  | m23 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hb
    omega
  | j1 hm => exact .inr hm
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


private theorem jankoOne_perfect_core (B : Subgroup Janko1.Model) [Group.IsPerfect B] :
    pCore 2 B = ⊥ := by
  let P : Sylow 2 B := default
  let R := (P : Subgroup B).map B.subtype
  let : IsMulCommutative R := Janko1.two_subgroup_isMulCommutative R
    (P.isPGroup'.map B.subtype)
  have hP : IsMulCommutative P := by
    exact ⟨⟨fun x y => Subtype.ext (Subtype.ext (congrArg
      (fun z : R => (z : Janko1.Model))
      (mul_comm (⟨x,mem_map_of_mem B.subtype x.property⟩ : R)
        ⟨y,mem_map_of_mem B.subtype y.property⟩)))⟩⟩
  apply bot_unique
  intro x hx
  have hh := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨Janko1.perfect_subgroup_pCore_two_le_center B hx,
      Group.IsPerfect.mem_commutator⟩,pCore_isPGroup.le_sylow_of_normal P hx⟩
  rwa [commutator_self_eq_bot_iff.mpr hP] at hh

private theorem jankoOne_involution_centralizer_card (a : Janko1.Model)
    (ha : orderOf a = 2) : Nat.card (centralizer ({a} : Set Janko1.Model)) = 120 := by
  obtain ⟨g,hg⟩ := Janko1.involution_fusion_of_card Janko1.card_model a ha
  let e := MulAut.conj g
  have hc : (centralizer ({a} : Set Janko1.Model)).map e.toMonoidHom =
      centralizer ({Janko1.a} : Set Janko1.Model) := by
    ext x
    rw [mem_map_equiv,mem_centralizer_singleton_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hh := congrArg e hx
      simpa only [map_mul,e.apply_symm_apply,show e a = Janko1.a from hg] using hh
    · intro hx
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply,show e a = Janko1.a from hg] using hx
  rw [←card_map_of_injective (f := e.toMonoidHom) e.injective,hc,
    Nat.card_congr Janko1.InvolutionCentralizer.productEquiv.toEquiv]
  change Nat.card (Multiplicative (ZMod 2) × alternatingGroup (Fin 5)) = 120
  rw [Nat.card_prod,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem jankoOne_not_prime_section (P : Sylow 2 Janko1.Model)
    (C : Subgroup Janko1.Model) [Group.IsPerfect C]
    (hn : (P : Subgroup Janko1.Model) ≤ normalizer (C : Set Janko1.Model))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) : False := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hlarge : 3 < p := by have := hp.2.1; have := hp.1.two_le; omega
  have hc := jankoOne_perfect_core C
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let a : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e : C ≃* PSL(2,ZMod p) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hc).symm).trans
      (b.trans (Atlas.fieldEquivPSL 2 a))
  have hpd : p ∣ Nat.card C := by
    have ho : Odd p := hp.1.odd_of_ne_two (by omega)
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula (ZMod p)
      ⟨p,1,hp.1,ho,by decide,by simp⟩,Nat.card_zmod]
    have he : 2 ∣ p^2-1 := by
      obtain ⟨a,ha⟩ := ho
      refine ⟨2*a*(a+1),?_⟩
      nlinarith [Nat.sub_add_cancel (show 1 ≤ p^2 by have := hp.1.two_le; nlinarith)]
    apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right he p)).mpr
    simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) he
  have hfaith : (P : Subgroup Janko1.Model) ⊓ centralizer (C : Set Janko1.Model) = ⊥ := by
    apply AlternatingFive.sylow_centralizer_eq_bot_of_no_involution P C
    intro z hz hz2
    have hCz : C ≤ centralizer ({z} : Set Janko1.Model) := by
      intro c hc
      exact mem_centralizer_singleton_iff.mpr (hz c hc)
    have hd := hpd.trans (card_dvd_of_le hCz)
    rw [jankoOne_involution_centralizer_card z hz2,
      show 120 = 2^3*3*5 by decide] at hd
    simp only [hp.1.dvd_mul] at hd
    rcases hd with (hd | hd) | hd
    · have := Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_two hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_three).mp hd; omega
    · have he := (Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_five).mp hd
      have hm := hp.2.1
      rw [he] at hm
      norm_num at hm
  let α := C.normalizerMonoidHom.comp (inclusion hn)
  have hi : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [←hfaith]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ C.normalizerMonoidHom.ker at hx
    rwa [normalizerMonoidHom_ker] at hx
  have hupper := Theory.GroupTheory.primeRank_le_of_injective 2 α hi
  rw [primeRank_equiv 2 (MulAut.congr e)] at hupper
  have hlower : 3 ≤ primeRank 2 P := by
    let : IsElementaryAbelian 2 P := Janko1.SylowTwo.elementary P
    let : IsElementaryAbelian 2 (⊤ : Subgroup P) :=
      IsElementaryAbelian.of_surjective (topEquiv (G := P)).symm.toMonoidHom
        (topEquiv (G := P)).symm.surjective
    exact IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup P)
      (by rw [card_top,Janko1.SylowTwo.card]; decide)
  have := Theory.PSL2.primeField_automorphism_two_rank (p := p) hlarge
  omega


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The original point cannot lie properly in a J₁ containing quotient.
The complete point catalogue is reduced by actual orders and the remaining
prime-field row contradicts the elementary full Sylow action. -/
theorem ofFlag_not_jankoOne_overcomponent
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
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* Janko1.Model) := by
  rintro ⟨b⟩
  let := point_quasisimple_in_small_sporadic h hJ hlt (.inl ⟨b⟩)
  obtain ⟨P,C,hC,hproper,hPC,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt b
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 175560 := by
    rw [Nat.card_congr a.toEquiv,←Janko1.card_model]
    exact (card_quotient_dvd_card (pCore 2 C)).trans C.card_subgroup_dvd_card
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ hlt).1
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact (h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he
  | lie hm =>
    rw [hdegree] at hm
    have hl := fieldFour_lie_rank_four hm
    have hu : primeRank 2 ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≤ 3 :=
      primeRank_le_of_prime_pow_not_dvd (fun hh => (by decide : ¬ 2^4 ∣ 175560) (hh.trans hd))
    omega
  | four _ hm =>
    rcases fieldFour_jankoOne_prime_or_self (pCore_quotient_pCore_eq_bot 2) hm hd with
      ⟨p,hp,hm⟩ | hself
    · let := FiveLocalFF.SolvableQuotients.local_perfect hC
      exact jankoOne_not_prime_section P C hPC hp (hm.of_mulEquiv a.symm)
    · obtain ⟨aJ⟩ := hself
      apply hproper
      apply C.eq_top_of_card_eq
      apply le_antisymm (Nat.card_le_card_of_injective C.subtype C.subtype_injective)
      rw [←Nat.card_congr (a.symm.trans aJ).toEquiv]
      exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
        (QuotientGroup.mk'_surjective _)

/-- After the J₁ comparison, only the three Mathieu rows and J₄ remain.
This disjunction is derived from the full original containing catalogue. -/
@[expose] def MathieuJankoFourPointContainer (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ IsM22Cover A ∨
  Nonempty (A ≃* Sporadic.Mathieu.M23) ∨ Nonempty (A ≃* Janko4.Model)

/-- The remaining containing quotient on the same chosen flag, with J₁
excluded through its full Sylow action and no added source hypothesis. -/
theorem ofFlag_quasisimple_point_mathieu_jankoFour_containers
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
    S.field.degree = 2 ∧ MathieuJankoFourPointContainer (J ⧸ pCore 2 J) := by
  obtain ⟨hd,hm⟩ := ofFlag_quasisimple_point_mathieu_janko_containers
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  refine ⟨hd,?_⟩
  rcases hm with hm | hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact (ofFlag_not_jankoOne_overcomponent S f X z H h hne hlinear h1132 e hJ.1 hlt hm).elim
  · exact .inr (.inr (.inr hm))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
