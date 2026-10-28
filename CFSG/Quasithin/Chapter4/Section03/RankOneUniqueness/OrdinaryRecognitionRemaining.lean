module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionModule
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryRecognitionCatalogue
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

/-!
# Ten further ordinary quotient-row exclusions

The original full module and Sylow bounds exclude M₁₁, M₁₂, J₂ and HS.
Its two-part together with the local quotient excludes G₂(2)′. In binary
triality, actual local placement bounds the same moved elementary subgroup
by 32 while its SL₂(8) action requires 64. The Tits two-local order bound
excludes its only possible rank-one field degree.

For large Ree groups the original local subgroup is an actual parabolic
residual. Three-divisibility removes the Suzuki side; the unchanged R₀
involution contradicts the linear residual's automorphism fixer. For M₂₄
and Held the order divisor leaves degrees two and three. The full-Sylow A₅
section exclusions handle degree two; the involution and two-local order
bounds handle degree three. No local placement or action callback is assumed.

The final theorem applies all these exclusions to the original source
catalogue. Only actual J₄ and Rudvalis central quotients remain alongside
the complete symplectic marking. Their exclusion and final assembly remain
with qt-d-1222-rankone-ordinary-symplectic-marking.
Source: Aschbacher--Smith C.3.1, pp.149--151, and 4.3.6, p.614,
using the native A.3.12 local geometries, pp.47--48.
-/

public section
open Subgroup Theory.GroupTheory ClassicalGroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open ChapterA.Section03.SourceEmbeddings FiveLocalFF ClassificationModels

/-- The original normalized module excludes all four small sporadic rows. -/
theorem ordinary_no_small_sporadic (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (name : SporadicName) (hname : name = .m11 ∨ name = .m12 ∨ name = .j2 ∨ name = .hs)
    (e : (c.K ⧸ center c.K) ≃* name.Carrier) : False := by
  let : Finite name.Carrier := Finite.of_equiv (c.K ⧸ center c.K) e.toEquiv
  obtain ⟨S,E,hE,_,hS,_,_,hb⟩ := c.ordinary_model_module_data D ho hn hpsl e
  have h16 : 16 ≤ Nat.card E :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 4 ≤ 2*n)).trans hb
  rcases hname with rfl | rfl | rfl | rfl
  · exact SporadicSieve.not_mathieuEleven S E hE hS h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_mathieuTwelve E hE h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_jankoTwo S E hE hS h16 (MulEquiv.refl _)
  · exact SporadicSieve.not_higmanSims S E hE hS h16 (MulEquiv.refl _)

/-- The moved module forces a two-part too large for G₂(2)′. -/
theorem ordinary_no_g2_derived (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := c.ordinary_model_moved_order_dvd D ho hn hpsl e
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  have hh := (pow_dvd_pow 2 (by omega : 6 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
  norm_num at hh

/-- The Tits row contradicts the original local two-core and rank-one quotient. -/
theorem ordinary_no_tits (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Tits.ParrottGroup) : False := by
  let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
  have hd := c.ordinary_model_local_order_dvd ho e hpsl
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
  have hne : B.pCoreIn 2 ≠ ⊥ := fun he => c.ordinary_model_local_core_ne_bot ho e
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  apply Tits.normalizer_fifteen_free (B.pCoreIn 2) hne (isPGroup_pCoreIn 2 B)
  exact (by norm_num [hn2] : 15 ∣ 2^n * ((2^n)^2-1)).trans
    (hd.trans (card_dvd_of_le hN))

/-- The binary triality local geometry excludes the original fully moved module. -/
theorem ordinary_no_triality_binary (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  obtain ⟨S,E,hE,hSB,_,hEcore,hm,hb⟩ := c.ordinary_model_module_data D ho hn hpsl e
  have hEB : E ≤ B := hEcore.trans (B.pCoreIn_le 2)
  have hEne : E ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hb
    have hbig := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 2*n)
    omega
  let := hE
  let := c.ordinaryLocal_perfect
  let : Group.IsPerfect B := Group.IsPerfect.map f
  let : Nontrivial B := B.nontrivial_iff_ne_bot.mpr (by
    intro he
    exact hEne (bot_unique (he ▸ hEB)))
  obtain ⟨_,_,_,hproper⟩ := c.ordinary_model_local_data D ho e
  exact Triality.Standard.BinaryLocalSections.no_moved_elementary
    (MulEquiv.refl _) S B E hproper (Group.IsPerfect.not_isSolvable B) hSB hEB hEne hm

private theorem three_dvd_rankOne_order (n : ℕ) : 3 ∣ 2^n * ((2^n)^2-1) := by
  have hm : (2^n)^2 % 3 = 1 := by
    rw [←pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num [Nat.pow_mod]
  have hp : 0 < (2^n)^2 := by positivity
  exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _

/-- The actual Ree residual marking is incompatible with the original R₀ action. -/
theorem ordinary_no_ree (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    {m : ℕ} (hm : 1 ≤ m) (e : (c.K ⧸ center c.K) ≃* ReeF4.Model m) : False := by
  let := ho.2
  let : IsSimpleGroup (c.K ⧸ center c.K) := IsQuasisimple.simple
  let : IsQuasisimple (c.K ⧸ center c.K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center c.K)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (ReeF4.Model m) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (ReeF4.Model m) := e.isSimpleGroup_congr.mp inferInstance
  have ht : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent :=
    (show IsComponent (ReeF4.Model m) ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  obtain ⟨P,_,hl,hproper⟩ := c.ordinary_model_local_data D ho e
  let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨g,s,hg⟩ := ChapterA.Section03.SourceEmbeddings.ReeLocal.local_placement hm ht S
    (c.ordinaryLocal.map f) hl hproper
  let e' := e.trans (MulAut.conj g)
  have he : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by ext; rfl
  have hB : c.ordinaryLocal.map (e'.toMonoidHom.comp (QuotientGroup.mk' (center c.K))) =
      ReeF4.Parabolics.localFactor m s := by
    simpa only [f,map_map,he,MonoidHom.comp_assoc] using hg
  cases s with
  | linear =>
    obtain ⟨a,ha,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e'
    rw [hB] at hfix
    have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    have hz := ReeF4.LinearLocalFixer.eq_one_of_fixes_linearLocal hm a
      (by apply MulEquiv.ext; intro x; exact congrArg (fun b : MulAut (ReeF4.Model m) => b x) ha2) hfix
    simp only [hz,orderOf_one] at ha
    omega
  | suzuki =>
    have hd := c.ordinary_model_local_order_dvd ho e' hpsl
    rw [hB] at hd
    have hfree := ReeF4.ConverseParabolics.suzuki_parabolic_three_free hm
    rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hfree
    exact hfree ((three_dvd_rankOne_order n).trans
        (hd.trans (card_dvd_of_le (ReeF4.Parabolics.localFactor_le_parabolic m .suzuki))))

private theorem local_five (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) {J : Type*} [Group J] [Finite J]
    (e : (c.K ⧸ center c.K) ≃* J)
    (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ 2)) :
    let B := c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K)))
    Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨a⟩ := c.ordinary_model_local_quotient_equiv ho e
  obtain ⟨F,_,_,hF,⟨b⟩⟩ := hpsl.of_mulEquiv a.symm
  obtain ⟨d⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨b.trans d⟩

/-- Both possible original field degrees are excluded in M₂₄. -/
theorem ordinary_no_m24 (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Sporadic.Mathieu.M24) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  have hd := c.ordinary_model_moved_order_dvd D ho hn hpsl e
  rw [Sporadic.Mathieu.m24_order] at hd
  have hn4 : n < 4 := by
    by_contra! hh
    have h := (pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd)
    norm_num at h
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.local_five ho e hpsl
    obtain ⟨P,hP,hl,_⟩ := c.ordinary_model_local_data D ho e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Sporadic.Mathieu.M24) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans (c.ordinaryLocal.le_normalizer_map f)
      rw [hP]
      exact c.ordinary_component_sylow_normalizes_local D
    exact FiveLocalFF.MathieuTwentyFour.not_section (MulEquiv.refl _) S B hl hSN
      (c.ordinary_model_local_core_ne_bot ho e) a
  · obtain ⟨r,hr,hfix⟩ := c.ordinary_exists_quotient_involutory_fixer D ho e
    have hB : B ≤ r.fixedSubgroup := fun b hb => (MulAut.mem_fixedSubgroup r b).mpr (hfix b hb)
    have h9 : 9 ∣ Nat.card B := (by decide : 9 ∣ 2^3*((2^3)^2-1)).trans
      (c.ordinary_model_local_order_dvd ho e hpsl)
    exact Sporadic.Mathieu.m24_involution_not_nine_dvd_fixed_card r hr
      (h9.trans (card_dvd_of_le hB))

/-- Both possible original field degrees are excluded in Held. -/
theorem ordinary_no_held (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (e : (c.K ⧸ center c.K) ≃* Held.He) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))
  let B := c.ordinaryLocal.map f
  have hd := c.ordinary_model_moved_order_dvd D ho hn hpsl e
  have hn4 : n < 4 := by
    by_contra! hh
    exact Held.not_two_pow_twelve_dvd_card
      ((pow_dvd_pow 2 (by omega : 12 ≤ 3*n)).trans ((dvd_mul_right _ _).trans hd))
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with rfl | rfl
  · obtain ⟨a⟩ := c.local_five ho e hpsl
    obtain ⟨P,hP,hl,_⟩ := c.ordinary_model_local_data D ho e
    let S := P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hSN : (S : Subgroup Held.He) ≤ normalizer (B : Set _) := by
      apply (map_mono ?_).trans (c.ordinaryLocal.le_normalizer_map f)
      rw [hP]
      exact c.ordinary_component_sylow_normalizes_local D
    exact FiveLocalFF.Held.not_section (MulEquiv.refl _) S B hl hSN
      (c.ordinary_model_local_core_ne_bot ho e) a
  · obtain ⟨S,E,hE,_,hSN,_,hm,hb⟩ := c.ordinary_model_module_data D ho hn hpsl e
    let := hE
    have hne : E ≠ ⊥ := by intro he; rw [he,card_bot] at hb; norm_num at hb
    have hBN : B ≤ normalizer (E : Set Held.He) :=
      le_normalizer_iff_commutator_le_left.mpr hm.le
    apply Held.TwoLocalCandidates.not_sixtythree_dvd_card_twoLocal S _
      ⟨E,hne,IsElementaryAbelian.isPGroup 2 E,rfl⟩ hSN
    exact (by decide : 63 ∣ 2^3*((2^3)^2-1)).trans
      ((c.ordinary_model_local_order_dvd ho e hpsl).trans (card_dvd_of_le hBN))

/-- The original hypotheses now leave only the actual J₄ and Rudvalis central
quotients besides the complete symplectic marking. Their exclusion and final
assembly remain with the ordinary-marking owner. -/
theorem ordinary_marking_or_jankoFour_or_rudvalis (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {n : ℕ} (hn : 1 < n) (hpsl : IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    Nonempty (OrdinarySymplecticMarking c n) ∨
      Nonempty ((c.K ⧸ center c.K) ≃* Janko4.Model) ∨
      Nonempty ((c.K ⧸ center c.K) ≃* Rudvalis.Model) := by
  rcases c.ordinary_marking_or_remaining_rows D ho hn hpsl with
    hmark | htriality | ⟨m,hm,⟨e⟩⟩ | ⟨e⟩ | ⟨e⟩ | ⟨name,hname,⟨e⟩⟩
  · exact Or.inl hmark
  · have ht : Triality.Standard.IsTrialityGroupAt (2^1) (c.K ⧸ center c.K) := htriality
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp ht
    exact (c.ordinary_no_triality_binary D ho hn hpsl e).elim
  · exact (c.ordinary_no_ree D ho hpsl hm e).elim
  · exact (c.ordinary_no_g2_derived D ho hn hpsl e.some).elim
  · exact (c.ordinary_no_tits ho hn hpsl e.some).elim
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (c.ordinary_no_small_sporadic D ho hn hpsl .m11 (by simp) e).elim
    · exact (c.ordinary_no_small_sporadic D ho hn hpsl .m12 (by simp) e).elim
    · exact (c.ordinary_no_m24 D ho hn hpsl e).elim
    · exact (c.ordinary_no_small_sporadic D ho hn hpsl .j2 (by simp) e).elim
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact (c.ordinary_no_small_sporadic D ho hn hpsl .hs (by simp) e).elim
    · exact (c.ordinary_no_held D ho hn hpsl e).elim
    · exact Or.inr (Or.inr ⟨e⟩)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceConfiguration
