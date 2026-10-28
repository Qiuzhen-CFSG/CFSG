module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryModule
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.MathieuTwentyFour
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Held
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal
public import Theory.SpecificGroups.Triality.BinaryMovedElementary
public import Theory.SpecificGroups.ReeF4.LinearLocalFixer
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree
public import Theory.SpecificGroups.Tits.FiniteSimple
public import Theory.Mathieu.M24.Properties.InvolutionFixedOrders
public import Theory.SpecificGroups.Held.SylowOrderBound
public import Theory.SpecificGroups.Held.TwoLocalCandidates.OrderObstruction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Exhausting ordinary carriers before full-normalizer identification

Apply the actual central-quotient catalogue to the original component. The
unchanged full Sylow, local subgroup, full moved module and fixed-radical action
exclude every carrier except nonbinary symplectic, J₄ and Rudvalis. Binary
triality uses its genuine graph-field carrier and moved-module calculation;
Ree uses actual parabolic placement. Every quotient and action retains the
original inclusions.

SourceSelectionOrdinarySporadic discharges the final two sporadic cases.
The surviving symplectic normalizer and unconditional source selection remain
with qt-d-1222-rankone-global-uniqueness; this is not global uniqueness.
Source: Aschbacher–Smith A.2.4, p.33, C.3.1, pp.149–151, and 4.3.6, p.614.
The row proofs extend OrdinaryRecognitionCatalogue/Remaining to OutsideChoice.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (c : OutsideChoice T L) (D : ChosenModule T L V)
  (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (K : Subgroup c.H) (ho : IsComponent c.H K)
  (hLK : L ≤ K.map c.H.subtype)
  (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
include D h ho hLK hout hKN
open ChapterA.Section02 ChapterA.Section03.SourceEmbeddings FiveLocalFF ClassificationModels

/-- The original normalized module excludes all four small sporadic rows. -/
theorem ordinary_no_small_sporadic
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (name : SporadicName) (hname : name = .m11 ∨ name = .m12 ∨ name = .j2 ∨ name = .hs)
    (e : (K ⧸ center K) ≃* name.Carrier) : False := by
  let : Finite name.Carrier := Finite.of_equiv (K ⧸ center K) e.toEquiv
  obtain ⟨S,E,hE,_,hS,_,_,hb⟩ := c.ordinary_model_module_data D h K ho hLK hout hKN hn hpsl e
  have h16 : 16 ≤ Nat.card E :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ 2*n)).trans hb
  rcases hname with rfl | rfl | rfl | rfl
  · exact SporadicSieve.not_mathieuEleven S E hE hS h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_mathieuTwelve E hE h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_jankoTwo S E hE hS h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_higmanSims S E hE hS h16 (MulEquiv.refl _)

/-- The moved module forces a two-part too large for G₂(2)′. -/
theorem ordinary_no_g2_derived
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := c.ordinary_model_moved_order_dvd D h K ho hLK hout hKN hn hpsl e
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  have hh := (pow_dvd_pow 2 (by omega : 6 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
  norm_num at hh

omit hout hKN in
/-- The Tits row contradicts the original local two-core and rank-one quotient. -/
theorem ordinary_no_tits
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Tits.ParrottGroup) : False := by
  let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
  have hd := c.ordinary_model_local_order_dvd D h K ho hLK e hpsl
  have hdG : 2^n * ((2^n)^2-1) ∣ 17971200 := by
    rw [←Tits.parrottGroup_card]
    exact hd.trans B.card_subgroup_dvd_card
  have hd2 : 2^n ∣ 17971200 := (dvd_mul_right _ _).trans hdG
  have hn12 : n < 12 := by
    by_contra! hh
    have h := (Nat.pow_dvd_pow 2 hh).trans hd2
    norm_num at h
  have hn2 : n = 2 := by
    interval_cases n <;> first | rfl | norm_num at hdG
  have hN : B ≤ normalizer (B.pCoreIn 2 : Set Tits.ParrottGroup) :=
    B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hne : B.pCoreIn 2 ≠ ⊥ := fun he => c.ordinary_model_local_core_ne_bot D h K ho hLK e
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  apply Tits.normalizer_fifteen_free (B.pCoreIn 2) hne (isPGroup_pCoreIn 2 B)
  exact (by norm_num [hn2] : 15 ∣ 2^n * ((2^n)^2-1)).trans
    (hd.trans (card_dvd_of_le hN))

/-- The binary triality local geometry excludes the original fully moved module. -/
theorem ordinary_no_triality_binary
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  obtain ⟨S,E,hE,hSB,_,hEcore,hm,hb⟩ := c.ordinary_model_module_data D h K ho hLK hout hKN hn hpsl e
  have hEB : E ≤ B := hEcore.trans (B.pCoreIn_le 2)
  have hEne : E ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hb
    have hbig := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 2*n)
    omega
  let := hE
  let := (c.ordinaryLocal_perfect h K hLK)
  let : Group.IsPerfect B := Group.IsPerfect.map f
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr (by
    intro he
    exact hEne (bot_unique (he ▸ hEB)))
  obtain ⟨_,_,_,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  exact Triality.Standard.BinaryLocalSections.no_moved_elementary
    (MulEquiv.refl _) S B E hproper (Group.IsPerfect.not_isSolvable B) hSB hEB hEne hm

omit c D h K ho hLK hout hKN in
private theorem three_dvd_rankOne_order (n : ℕ) : 3 ∣ 2^n * ((2^n)^2-1) := by
  have hm : (2^n)^2 % 3 = 1 := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num [Nat.pow_mod]
  have hp : 0 < (2^n)^2 := by positivity
  exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _

/-- The actual Ree residual marking is incompatible with the original R₀ action. -/
theorem ordinary_no_ree
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {m : ℕ} (hm : 1 ≤ m) (e : (K ⧸ center K) ≃* ReeF4.Model m) : False := by
  let := ho.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsQuasisimple (K ⧸ center K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (ReeF4.Model m) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (ReeF4.Model m) := e.isSimpleGroup_congr.mp inferInstance
  have ht : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent :=
    (show IsComponent (ReeF4.Model m) ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hl,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨g,s,hg⟩ := ChapterA.Section03.SourceEmbeddings.ReeLocal.local_placement hm ht S
    ((c.ordinaryLocal K).map f) hl hproper
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hB : (c.ordinaryLocal K).map (e'.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      ReeF4.Parabolics.localFactor m s := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  cases s with
  | linear =>
    obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e'
    rw [hB] at hfix
    have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hz := ReeF4.LinearLocalFixer.eq_one_of_fixes_linearLocal hm a
      (by apply MulEquiv.ext; intro x; exact congrArg (fun b : MulAut (ReeF4.Model m) => b x) ha2) hfix
    simp only [hz,orderOf_one] at ha
    omega
  | suzuki =>
    have hd := c.ordinary_model_local_order_dvd D h K ho hLK e' hpsl
    rw [hB] at hd
    have hfree := ReeF4.ConverseParabolics.suzuki_parabolic_three_free hm
    rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hfree
    exact hfree ((three_dvd_rankOne_order n).trans
        (hd.trans (card_dvd_of_le (ReeF4.Parabolics.localFactor_le_parabolic m .suzuki))))

omit hout hKN in
private theorem local_five
     {J : Type*} [Group J] [Finite J]
    (e : (K ⧸ center K) ≃* J)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2)) :
    let B := (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv D h K ho hLK e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨b.trans d⟩

/-- Both possible original field degrees are excluded in M₂₄. -/
theorem ordinary_no_m24
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Sporadic.Mathieu.M24) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  have hd := c.ordinary_model_moved_order_dvd D h K ho hLK hout hKN hn hpsl e
  rw [Sporadic.Mathieu.m24_order] at hd
  have hn4 : n < 4 := by
    by_contra! hh
    have h := (pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
    norm_num at h
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.local_five D h K ho hLK e hpsl
    obtain ⟨P,hP,hl,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans ((c.ordinaryLocal K).le_normalizer_map f)
      rw [hP]
      exact (c.ordinary_component_sylow_normalizes_local D K)
    exact FiveLocalFF.MathieuTwentyFour.not_section (MulEquiv.refl _) S B hl hSN
      (c.ordinary_model_local_core_ne_bot D h K ho hLK e) a
  · obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D h hpsl K ho hLK hout hKN e
    have hB : B ≤ r.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup r b).mpr (hfix b hb)
    have h9 : 9 ∣ Nat.card B := (by decide : 9 ∣ 2^3*((2^3)^2-1)).trans
      (c.ordinary_model_local_order_dvd D h K ho hLK e hpsl)
    exact Sporadic.Mathieu.m24_involution_not_nine_dvd_fixed_card r hr
      (h9.trans (card_dvd_of_le hB))

/-- Both possible original field degrees are excluded in Held. -/
theorem ordinary_no_held
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (K ⧸ center K) ≃* Held.He) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := (c.ordinaryLocal K).map f
  have hd := c.ordinary_model_moved_order_dvd D h K ho hLK hout hKN hn hpsl e
  have hn4 : n < 4 := by
    by_contra! hh
    exact Held.not_two_pow_twelve_dvd_card
      ((pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd))
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.local_five D h K ho hLK e hpsl
    obtain ⟨P,hP,hl,_⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Held.He) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans ((c.ordinaryLocal K).le_normalizer_map f)
      rw [hP]
      exact (c.ordinary_component_sylow_normalizes_local D K)
    exact FiveLocalFF.Held.not_section (MulEquiv.refl _) S B hl hSN
      (c.ordinary_model_local_core_ne_bot D h K ho hLK e) a
  · obtain ⟨S,E,hE,_,hSN,_,hm,hb⟩ := c.ordinary_model_module_data D h K ho hLK hout hKN hn hpsl e
    let := hE
    have hne : E ≠ ⊥ := by intro he; rw [he,card_bot] at hb; norm_num at hb
    have hBN : B ≤ normalizer (E : Set Held.He) :=
      le_normalizer_iff_commutator_le_left.mpr hm.le
    apply Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal S _
      ⟨E,hne,IsElementaryAbelian.isPGroup 2 E,rfl⟩ hSN
    exact (by decide : 63 ∣ 2^3*((2^3)^2-1)).trans
      ((c.ordinary_model_local_order_dvd D h K ho hLK e hpsl).trans (card_dvd_of_le hBN))

/-- Full-Sylow properness excludes the complete actual Bender catalogue. -/
theorem ordinary_no_bender
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hm : IsBenderModel (K ⧸ center K)) : False := by
  let := ho.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : IsQuasisimple (K ⧸ center K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let e := MulEquiv.refl (K ⧸ center K)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  obtain ⟨P,_,hl,hproper⟩ := c.ordinary_model_local_data D h hpsl K ho hLK hout hKN e
  exact FiveLocalFF.CarrierSieve.not_bender_model
    (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _)))
    ((c.ordinaryLocal K).map f) hl hproper hm

/-- Actual source application of the catalogue, all completed exclusions and
quotient transports. Only the displayed genuine remaining quotient rows are retained. -/
theorem ordinary_symplectic_or_remaining_rows
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    (∃ m : ℕ, 1 < m ∧ IsPSp (K ⧸ center K) 2 (2 ^ m)) ∨
      Triality.Standard.IsTrialityGroupAt 2 (K ⧸ center K) ∨
      (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ center K) ≃* ReeF4.Model m)) ∨
      Nonempty ((K ⧸ center K) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∨
      Nonempty ((K ⧸ center K) ≃* Tits.ParrottGroup) ∨
      (∃ name : SporadicName,
        (name = .m11 ∨ name = .m12 ∨ name = .m24 ∨ name = .j2 ∨ name = .j4 ∨
          name = .hs ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((K ⧸ center K) ≃* name.Carrier)) := by
  let := ho.2
  have hm := quasisimple_center_quotient_theoremC_model ((c.c28 D h).sqtk.subgroup K)
  cases hm with
  | alternating d hd e => exact (c.ordinary_no_alternating D h K ho hLK hout hKN hn hpsl hd e.some).elim
  | odd hm => exact ((c.c28 D h).no_ordinary_component_of_theoremC_odd_model K ho hm).elim
  | bender hm => exact (c.ordinary_no_bender D h K ho hLK hout hKN hpsl hm).elim
  | linear_binary d hd hm => exact (c.ordinary_no_higher_binary_linear D h K ho hLK hout hKN hn hpsl hd hm).elim
  | rank_two f hr =>
    cases hr with
    | linear hf hm =>
      by_cases h1 : f = 1
      · exact (c.ordinary_no_pslThree_binary D h K ho hLK hn hpsl (by simpa [h1] using hm)).elim
      · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
        let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
        exact (c.ordinary_no_pslThree D h hpsl K ho hLK hout hKN (by omega) hF e).elim
    | symplectic hf hm =>
      exact Or.inl ⟨f,by omega,hm⟩
    | g2 hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      have hq : 2 < Nat.card F := by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hf)
      exact (c.ordinary_no_g2 D h hpsl K ho hLK hout hKN hq e).elim
    | triality hf hm =>
      by_cases h1 : f = 1
      · exact Or.inr (Or.inl (by simpa [h1] using hm))
      · obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ f hf).mp hm
        have hq : 2 < 2 ^ f := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
          (Nat.pow_le_pow_right (by decide) (by omega))
        exact (c.ordinary_no_triality_large D h hpsl K ho hLK hout hKN f hf hq e).elim
    | ree_f4 m hm _ e => exact Or.inr (Or.inr (Or.inl ⟨m,hm,e⟩))
    | symplectic_derived _ e =>
      exact (c.ordinary_no_alternating D h K ho hLK hout hKN hn hpsl (by decide : 6 ≤ 8)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).elim
    | g2_derived _ e => exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    | tits _ e => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  | sporadic hm =>
    rcases hm with ⟨name,hname,⟨e⟩⟩ | ⟨e⟩
    · cases name with
      | m22 => exact (c.ordinary_no_m22 D h K ho hLK hout hKN hn hpsl e).elim
      | m23 => exact (c.ordinary_no_m23 D h K ho hLK hout hKN hn hpsl e).elim
      | j3 => exact (hname rfl).elim
      | m11 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m11,by simp,⟨e⟩⟩))))
      | m12 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m12,by simp,⟨e⟩⟩))))
      | m24 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.m24,by simp,⟨e⟩⟩))))
      | j2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.j2,by simp,⟨e⟩⟩))))
      | j4 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.j4,by simp,⟨e⟩⟩))))
      | hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.hs,by simp,⟨e⟩⟩))))
      | he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.he,by simp,⟨e⟩⟩))))
      | ru => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨.ru,by simp,⟨e⟩⟩))))
    · exact ((c.c28 D h).no_ordinary_component_janko_central_quotient K ho e.some).elim
/-- The original hypotheses now leave only the actual J₄ and Rudvalis central
quotients besides a genuine symplectic quotient. SourceSelectionOrdinarySporadic
excludes both remaining sporadic rows at this same source boundary. -/
theorem ordinary_symplectic_or_jankoFour_or_rudvalis
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    (∃ m : ℕ, 1 < m ∧ IsPSp (K ⧸ center K) 2 (2 ^ m)) ∨
      Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∨
      Nonempty ((K ⧸ center K) ≃* Rudvalis.Model) := by
  rcases c.ordinary_symplectic_or_remaining_rows D h K ho hLK hout hKN hn hpsl with
    hmark | htriality | ⟨m,hm,⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩ | ⟨name,hname,⟨e⟩⟩
  · exact Or.inl hmark
  · have ht : Triality.Standard.IsTrialityGroupAt (2^1) (K ⧸ center K) := htriality
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp ht
    exact (c.ordinary_no_triality_binary D h K ho hLK hout hKN hn hpsl e).elim
  · exact (c.ordinary_no_ree D h K ho hLK hout hKN hpsl hm e).elim
  · exact (c.ordinary_no_g2_derived D h K ho hLK hout hKN hn hpsl e.some).elim
  · exact (c.ordinary_no_tits D h K ho hLK hn hpsl e.some).elim
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (c.ordinary_no_small_sporadic D h K ho hLK hout hKN hn hpsl .m11 (by simp) e).elim
    · exact (c.ordinary_no_small_sporadic D h K ho hLK hout hKN hn hpsl .m12 (by simp) e).elim
    · exact (c.ordinary_no_m24 D h K ho hLK hout hKN hn hpsl e).elim
    · exact (c.ordinary_no_small_sporadic D h K ho hLK hout hKN hn hpsl .j2 (by simp) e).elim
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact (c.ordinary_no_small_sporadic D h K ho hLK hout hKN hn hpsl .hs (by simp) e).elim
    · exact (c.ordinary_no_held D h K ho hLK hout hKN hn hpsl e).elim
    · exact Or.inr (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OutsideChoice
