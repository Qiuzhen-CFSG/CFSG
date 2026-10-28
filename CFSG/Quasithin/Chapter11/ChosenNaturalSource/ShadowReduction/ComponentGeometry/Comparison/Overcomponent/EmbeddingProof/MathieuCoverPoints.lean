module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.MathieuTwentyThreePoints
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.PerfectCenterFrattini

/-!
# Excluding the triple M₂₂ containing cover in source 11.4.2

Map the literal point image through the containing group's center. Its
local membership, full Sylow normalization and properness survive. The
intrinsic two-core quotients are linked by the induced surjection, so their
simple central quotients agree. The full source point catalogue and the
order of 3.M₂₂ leave only central markings by PSL₃(4), A₇, PSL₂(11) or M₂₂.
Comparison with the order of M₂₂ kills the remaining covering centers.
The native local-section and Sylow-action theorems exclude the first three
rows; the last violates properness.

The chosen-module consumer in Comparison.Overcomponent retains every
proved quintic and M₂₃ proper pair, with only J₄ left for comparison.
J₄, inner radical placement, strict omega-center containment and final
equality remain with qt-d-1222-shadow-component-comparison. The positive
normalized-module input retains qt-d-1222-normalized-nonff; earlier-source
discharge retains qt-d-1222-shadow-components. No unconditional 11.4.2
conclusion is asserted here.
Source: Aschbacher--Smith A.3.12 and 11.4.2, printed pp.47--48,776--777.
Imported carrier results retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No new carrier enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem local_core_quotient_nontrivial {A : Type*} [Group A] [Finite A]
    {S C : Subgroup A} (hC : C ∈ localCComponents S) : Nontrivial (C ⧸ pCore 2 C) := by
  have ht : (⊤ : Subgroup C).IsCComponent := by
    simpa only [subgroupOf_self] using hC.subgroupOf_of_le le_rfl le_sup_left
  let := pCore_isNilpotent (p := 2) (G := C)
  have hq : (⊤ : Subgroup (C ⧸ pCore 2 C)).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 C))] using
      ht.map_quotient (pCore 2 C)
  let : Nontrivial (⊤ : Subgroup (C ⧸ pCore 2 C)) := (nontrivial_iff_ne_bot _).mpr hq.ne_bot
  exact (topEquiv : (⊤ : Subgroup (C ⧸ pCore 2 C)) ≃* (C ⧸ pCore 2 C)).symm.nontrivial

private theorem core_quotient_surjection {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    ∃ q : (A ⧸ pCore 2 A) →* (B ⧸ pCore 2 B), Function.Surjective q := by
  have hc : pCore 2 A ≤ (pCore 2 B).comap f :=
    map_le_iff_le_comap.mp (le_sSup ⟨Normal.map inferInstance f hf,pCore_isPGroup.map f⟩)
  exact ⟨QuotientGroup.map _ _ f hc,QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hf) hc⟩

private theorem central_image_marking {A B R : Type*}
    [Group A] [Finite A] [IsQuasisimple A] [Group B] [Finite B]
    [Group R] [Finite R] [Nontrivial R]
    (q : A →* R) (hq : Function.Surjective q) (e : (A ⧸ center A) ≃* B)
    {n : ℕ} (hA : Nat.card A ∣ n) (hR : Nat.card R ∣ 443520)
    (hn : Nat.gcd n 443520 = Nat.card B) : Nonempty (R ≃* B) := by
  let a := (IsQuasisimple.centralQuotientEquiv q hq).symm.trans e
  have hd : Nat.card R ∣ Nat.card B := by
    rw [←hn]
    exact Nat.dvd_gcd ((card_dvd_of_surjective q hq).trans hA) hR
  have hu : Nat.card R ≤ Nat.card (R ⧸ center R) := by
    rw [Nat.card_congr a.toEquiv]
    exact Nat.le_of_dvd (Nat.card_pos (α := B)) hd
  let b := MulEquiv.ofBijective (QuotientGroup.mk' (center R))
    ((QuotientGroup.mk'_surjective _).bijective_of_nat_card_le hu)
  exact ⟨b.trans a⟩

private def center_quotient_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

private def simple_center_marking {A B : Type*} [Group A] [IsQuasisimple A]
    [Group B] [IsSimpleGroup B] (e : A ≃* B) : (A ⧸ center A) ≃* B := by
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  exact (center_quotient_equiv e).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)


private def MathieuCentralPoint (A : Type*) [Group A] : Prop :=
  (ClassicalGroup.IsPSL (A ⧸ center A) 3 4 ∧ Nat.card A ∣ 60480) ∨
  (IsAlternating (A ⧸ center A) 7 ∧ Nat.card A ∣ 7560) ∨
  (ClassicalGroup.IsPSL (A ⧸ center A) 2 11 ∧ Nat.card A ∣ 660) ∨
  (Nonempty ((A ⧸ center A) ≃* Sporadic.Mathieu.M22) ∧ Nat.card A ∣ 1330560)

private theorem seven_central_point {A : Type*} [Group A] [IsQuasisimple A]
    (hm : IsAlternating A 7) : MathieuCentralPoint A := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine .inr (.inl ⟨⟨simple_center_marking hm.some⟩,?_⟩)
  rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem eleven_central_point {A : Type*} [Group A] [IsQuasisimple A]
    (hm : ClassicalGroup.IsPSL A 2 11) : MathieuCentralPoint A := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  refine .inr (.inr (.inl ⟨⟨F,inferInstance,inferInstance,hF,⟨simple_center_marking e⟩⟩,?_⟩))
  rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
    ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
  norm_num

private theorem fieldFour_mathieuCover_lie {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hm : LocalGeometry.Components.LieOvergroup A 2)
    (hd : Nat.card A ∣ 1330560) : MathieuCentralPoint A := by
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
    refine .inl ⟨⟨F,inferInstance,inferInstance,hF,⟨center_quotient_equiv e⟩⟩,?_⟩
    rw [Nat.card_congr e.toEquiv,←(center SL(3,F)).card_mul_index,index_eq_card,hcenter,hproj]
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    refine .inl ⟨⟨F,inferInstance,inferInstance,hF,⟨simple_center_marking e⟩⟩,?_⟩
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
    exact (by norm_num : ¬ (2^2)^12 ∣ 1330560) (hu.trans hd) |>.elim
  | trialityCube m hm he _ => omega

private theorem fieldFour_mathieuCover_cases {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 1330560) :
    MathieuCentralPoint A := by
  have hb := Nat.le_of_dvd (by decide : 0 < 1330560) hd
  cases hm with
  | alternating hm => exact seven_central_point hm
  | alternatingCover hm =>
    refine .inr (.inl ⟨hm.2.2,?_⟩)
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
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
    rw [show 1330560 = 2^7*3^3*5*7*11 by decide] at hpN
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
    exact eleven_central_point (he ▸ hm)
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
    let := Sporadic.Mathieu.m22_isSimpleGroup
    refine .inr (.inr (.inr ⟨⟨simple_center_marking hm.some⟩,?_⟩))
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order]
    decide
  | m22Cover hm =>
    refine .inr (.inr (.inr ⟨hm.2.2,?_⟩))
    have hz : Nat.card (center A) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center A).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]
  | m23 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hb
    omega
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


private theorem mathieu_no_central_point {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (S : Sylow 2 Sporadic.Mathieu.M22) (C : Subgroup Sporadic.Mathieu.M22)
    (hl : C ∈ localCComponents S) (hn : (S : Subgroup Sporadic.Mathieu.M22) ≤ normalizer (C : Set Sporadic.Mathieu.M22))
    (hp : C ≠ ⊤) (q : A →* (C ⧸ pCore 2 C)) (hq : Function.Surjective q)
    (hm : MathieuCentralPoint A) : False := by
  let := local_core_quotient_nontrivial hl
  let : IsQuasisimple (C ⧸ pCore 2 C) := IsQuasisimple.of_surjective q hq
  have hd : Nat.card (C ⧸ pCore 2 C) ∣ 443520 := by
    rw [←Sporadic.Mathieu.m22_order]
    exact (card_quotient_dvd_card _).trans C.card_subgroup_dvd_card
  rcases hm with ⟨hm,ha⟩ | ⟨hm,ha⟩ | ⟨hm,ha⟩ | ⟨hm,ha⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc : Nat.card PSL(3,F) = 20160 := by
      rw [Matrix.PSL3.LinearThree.card_projective,hF]; norm_num
    obtain ⟨a⟩ := central_image_marking q hq e ha hd (by rw [hc]; decide)
    apply Exceptional.not_mathieu_twentyTwo_of_section_card S C hn _ (MulEquiv.refl _)
    exact (Nat.card_congr a.toEquiv).trans hc
  · obtain ⟨a⟩ := central_image_marking q hq hm.some ha hd (by
      rw [nat_card_alternatingGroup]; norm_num [Nat.factorial])
    exact mathieuPoint_not_small_section S C hl hn (.inl ⟨a⟩)
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc : Nat.card PSL(2,F) = 660 := by
      rw [GorensteinWalter.psl2_card_formula F
        ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
      norm_num
    obtain ⟨a⟩ := central_image_marking q hq e ha hd (by rw [hc]; decide)
    exact mathieuPoint_not_small_section S C hl hn
      (.inr ⟨F,inferInstance,inferInstance,hF,⟨a⟩⟩)
  · obtain ⟨a⟩ := central_image_marking q hq hm.some ha hd (by
      rw [Sporadic.Mathieu.m22_order]; decide)
    apply hp
    apply C.eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective C.subtype C.subtype_injective)
    rw [←Nat.card_congr a.toEquiv]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 C))
      (QuotientGroup.mk'_surjective _)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- A full-Sylow-normalized local subgroup of the genuine triple M₂₂ cover
with the original point quotient is the whole cover. The central projection
and full source catalogue are retained; field four is the earlier derived input. -/
theorem ofFlag_mathieuCover_point_eq_top
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
    (P : Sylow 2 Sporadic.Mathieu.M22TripleCover)
    (C : Subgroup Sporadic.Mathieu.M22TripleCover)
    (hC : C ∈ localCComponents P)
    (hPC : (P : Subgroup Sporadic.Mathieu.M22TripleCover) ≤ normalizer (C : Set _))
    (a : ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≃*
      (C ⧸ pCore 2 C)) : C = ⊤ := by
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 1330560 := by
    rw [Nat.card_congr a.toEquiv,←Sporadic.Mathieu.M22TripleCover.card]
    exact (card_quotient_dvd_card _).trans C.card_subgroup_dvd_card
  have hmodel : MathieuCentralPoint ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
    cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
    | equal he =>
      exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
    | lie hm =>
      rw [hdegree] at hm
      exact fieldFour_mathieuCover_lie hm hd
    | four _ hm => exact fieldFour_mathieuCover_cases (pCore_quotient_pCore_eq_bot 2) hm hd
  let π := Janko4.InvolutionCentralizers.First.QuotientExtension.coverCentralProjection
  have hπ : Function.Surjective π :=
    Sporadic.Mathieu.M22TripleCover.centralQuotientEquiv.surjective.comp
      (QuotientGroup.mk'_surjective _)
  have hk : π.ker = center Sporadic.Mathieu.M22TripleCover :=
    Janko4.InvolutionCentralizers.First.QuotientExtension.coverCentralProjection_ker
  let : Group.IsSolvable π.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y
  have hfull : C.map π = ⊤ := by
    by_contra hproper
    obtain ⟨q,hq⟩ := core_quotient_surjection (π.subgroupMap C) (π.subgroupMap_surjective C)
    exact mathieu_no_central_point (P.mapSurjective hπ) (C.map π)
      (localCComponents_map_of_solvable_ker hC π)
      ((map_mono (f := π) hPC).trans (C.le_normalizer_map π)) hproper
      (q.comp a.toMonoidHom) (hq.comp a.surjective) hmodel
  apply top_unique
  apply le_of_map_le_of_perfect π hk.le ⊤ C
  rw [hfull]
  exact le_top

/-- The genuine triple cover of M₂₂ cannot properly contain the original
point component. Descent retains both intrinsic two-core quotients; the
full point catalogue supplies the simple central quotient markings. -/
theorem ofFlag_not_mathieuTwentyTwo_cover_overcomponent
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
    (hlt : (ofFlag S f X z H).Kz < J) : ¬ IsM22Cover (J ⧸ pCore 2 J) := by
  intro hm
  let := point_quasisimple_in_small_sporadic h hJ hlt (.inr (.inr (.inr (.inl hm))))
  let Q := J ⧸ pCore 2 J
  let : IsQuasisimple Q := hm.1
  obtain ⟨P,C,hC,hproper,hPC,⟨a⟩,_⟩ := proper_local_model_image h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt (MulEquiv.refl Q)
  have hcard : Nat.card Q = 1330560 := by
    have hz : Nat.card (center Q) = 3 := by
      rw [Nat.card_congr hm.2.1.some.toEquiv]; exact Nat.card_zmod 3
    rw [←(center Q).card_mul_index,index_eq_card,hz,
      Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order]
  have hd : Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 1330560 := by
    rw [Nat.card_congr a.toEquiv,←hcard]
    exact (card_quotient_dvd_card _).trans C.card_subgroup_dvd_card
  have hdegree := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne
    hlinear h1132 e hJ hlt).1
  have hmodel : MathieuCentralPoint ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) := by
    cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
    | equal he =>
      exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
    | lie hm =>
      rw [hdegree] at hm
      exact fieldFour_mathieuCover_lie hm hd
    | four _ hm => exact fieldFour_mathieuCover_cases (pCore_quotient_pCore_eq_bot 2) hm hd
  let π := hm.2.2.some.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hπ : Function.Surjective π := hm.2.2.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : π.ker = center Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ hm.2.2.some.injective,QuotientGroup.ker_mk']
  let : Group.IsSolvable π.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y
  have hproper' : C.map π ≠ ⊤ := by
    intro ht
    apply hproper
    apply top_unique
    apply le_of_map_le_of_perfect π hk.le ⊤ C
    rw [ht]
    exact le_top
  obtain ⟨q,hq⟩ := core_quotient_surjection (π.subgroupMap C) (π.subgroupMap_surjective C)
  exact mathieu_no_central_point (P.mapSurjective hπ) (C.map π)
    (localCComponents_map_of_solvable_ker hC π)
    ((map_mono (f := π) hPC).trans (C.le_normalizer_map π)) hproper'
    (q.comp a.toMonoidHom) (hq.comp a.surjective) hmodel

/-- The complete point and containing catalogues now leave a proved
proper pair or the J₄ containing row. The quintic extension pair and
all three M₂₃ pairs remain on the original quotients. -/
theorem ofFlag_proper_embedding_or_jankoFour
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
      (ProperEmbedding (ofFlag S f X z H).Kz J ∨ Nonempty ((J ⧸ pCore 2 J) ≃* Janko4.Model)) := by
  obtain ⟨hd,hp | hc | hj⟩ := ofFlag_proper_embedding_or_cover_or_jankoFour
    S f X z H h hne hlinear h1132 e hcent hJ hlt
  · exact ⟨hd,.inl hp⟩
  · exact (ofFlag_not_mathieuTwentyTwo_cover_overcomponent
      S f X z H h hne hlinear h1132 e hJ.1 hlt hc).elim
  · exact ⟨hd,.inr hj⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
