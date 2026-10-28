module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.MathieuTwentyThree
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.HSNatural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.Held
public import Theory.SpecificGroups.Janko4.Model.FullyMovedCentralizer
public import Theory.SpecificGroups.BinaryLinear.FullyMovedCentralizer
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.FullyMovedSection

/-!
# Containing-carrier comparisons without component irreducibility

The original moved subgroup has a nonzero fully moved elementary image in
the containing central quotient. Its order is at least eight, and the
original two-core still centralizes it. In the binary degree-five, M₂₄ and
J₄ carriers the small centers of involution-centralizer two-cores force the
local image to have odd centralizer. The opposite moved involutions then
fix the whole containing component. The native HS comparison uses the same
elementary image and its full Sylow normalizer.

These arguments apply to every original module row, including quiet action,
fixed kernels and nonsplit extensions. Quasisimple.Completion applies them
to every original quotient whose order is divisible by 168. Source: Aschbacher--Smith A.3.12
and 10.2.9, printed pp.47--48,750--751.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} (c : EscapingComponent D t v I)
include D c

/-- The original moved image and its full Sylow, with no action marking. -/
theorem marked_fully_moved_data [Group.IsPerfect I]
    {H : Type*} [Group H] [Finite H] (e : (I ⧸ center I) ≃* H) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (center I))
    let B := (L.subgroupOf I).map q
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    ∃ P : Sylow 2 H, Group.IsPerfect B ∧ IsPPerfect 2 B ∧
      (P : Subgroup H) ≤ normalizer (B : Set H) ∧
      (P : Subgroup H) ≤ normalizer (E : Set H) ∧
      IsElementaryAbelian 2 E ∧ E ≤ B ∧ 8 ≤ Nat.card E ∧
      B.pCoreIn 2 ≤ centralizer (E : Set H) ∧ ⁅E,B⁆ = E := by
  obtain ⟨S,_,_,hSB,hSE,_,_,hE,_,hne,hmove⟩ := center_quotient_data D c
  let q := QuotientGroup.mk' (center I)
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp q)
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  let P := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPB : (P : Subgroup H) ≤ normalizer (B : Set H) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    dsimp only [B]
    rw [←map_map]
    exact (map_mono hSB).trans (le_normalizer_map e.toMonoidHom)
  have hPE : (P : Subgroup H) ≤ normalizer (E : Set H) := by
    change ((R : Subgroup (I ⧸ center I)).map e.toMonoidHom) ≤ _
    dsimp only [E]
    rw [←map_map]
    exact (map_mono hSE).trans (le_normalizer_map e.toMonoidHom)
  have hEp : IsElementaryAbelian 2 E := by
    let := hE
    change IsElementaryAbelian 2
      (((⁅D.fullModule,L⁆).subgroupOf I).map (e.toMonoidHom.comp q))
    rw [←Subgroup.map_map]
    exact IsElementaryAbelian.map (p := 2)
      (A := ((⁅D.fullModule,L⁆).subgroupOf I).map q) e.toMonoidHom
  have hEB : E ≤ B := map_mono (comap_mono (source_full_moved_le_component D))
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := markedLocalHom c.strict.le e) (markedLocalHom_surjective c.strict.le e)
  let := hEp
  have hmov : ⁅E,B⁆ = E := by
    simpa only [E,B,map_commutator,map_map] using congrArg (map e.toMonoidHom) hmove
  let F := E.subgroupOf B
  let : F.Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_iff_commutator_le_left.mpr hmov.le)
  have hFmov : ⁅F,(⊤ : Subgroup B)⁆ = F := by
    apply map_injective B.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hEB,←MonoidHom.range_eq_map,
      range_subtype,hmov]
  have hFne : F ≠ ⊥ := by
    intro hf
    have heq : E = ⊥ := by
      rw [←map_subgroupOf_eq_of_le hEB]
      change F.map B.subtype = ⊥
      rw [hf,Subgroup.map_bot]
    apply hne
    apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
    simpa only [E,←map_map] using heq
  have hcard : 8 ≤ Nat.card E := by
    have hh := commutator_card_ge_eight_of_isPerfect (⊤ : Subgroup B) F
      ((IsElementaryAbelian.isPGroup 2 E).comap_of_injective B.subtype B.subtype_injective)
      (hFmov.symm ▸ hFne)
    rwa [hFmov,Nat.card_congr (subgroupOfEquivOfLe hEB).toEquiv] at hh
  exact ⟨P,inferInstance,
    (Chapter1.Section02.Adequate.mem_L_isPPerfect D.maximal.1).of_surjective
      (markedLocalHom c.strict.le e) (markedLocalHom_surjective c.strict.le e),
    hPB,hPE,hEp,hEB,hcard,marked_moved_core_centralizes D c.strict.le e,hmov⟩

/-- Lift the actual quotient fixer through the perfect containing component. -/
theorem common_centralizer_of_marked_fixer [Group.IsPerfect I]
    {H : Type*} [Group H] (e : (I ⧸ center I) ≃* H)
    (hfixer : ∀ a : MulAut H, a ^ 2 = 1 →
      (∀ x ∈ (L.subgroupOf I).map
        (e.toMonoidHom.comp (QuotientGroup.mk' (center I))), a x = x) → a = 1) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (I : Set G) := by
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  let U := (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩
  have ha2 : a ^ 2 = 1 := by
    change (I.normalizerMonoidHom ⟨u,partner_normalizes D c hu⟩) ^ 2 = 1
    rw [←map_pow]
    have he : (⟨u,partner_normalizes D c hu⟩ : normalizer (I : Set G)) ^ 2 = 1 :=
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := U) u hu)
    rw [he,map_one]
  have hfix : ∀ x ∈ B, MulAut.centralQuotientAction e a x = x := by
    intro x hx
    obtain ⟨l,hl⟩ := markedLocalHom_surjective c.strict.le e ⟨x,hx⟩
    have hxval := congrArg Subtype.val hl
    change e (QuotientGroup.mk' (center I) (inclusion c.strict.le l)) = x at hxval
    rw [←hxval,MulAut.centralQuotientAction_apply]
    have hal : a (inclusion c.strict.le l) = inclusion c.strict.le l := by
      apply Subtype.ext
      change u*l.val*u⁻¹=l.val
      exact mul_inv_eq_iff_eq_mul.mpr (c.crossed hu l.val l.property).symm
    rw [hal]
  have hqa : MulAut.centralQuotientAction e a = 1 :=
    hfixer _ (by rw [←map_pow,ha2,map_one]) hfix
  have ha : a = 1 := MulAut.centralQuotientAction_injective e
    (hqa.trans (map_one _).symm)
  intro i hi
  have hh := congrArg (fun b : MulAut I => (b ⟨i,hi⟩ : G)) ha
  change u*i*u⁻¹=i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem not_jankoFour_of_fully_moved [IsQuasisimple I]
    (e : (I ⧸ center I) ≃* Janko4.Model) : False := by
  obtain ⟨P,hperfect,hB,hPB,hPE,hE,hEB,hcard,hcore,hmov⟩ := marked_fully_moved_data D c e
  let := hperfect
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hodd := Janko4.centralizer_odd_of_fully_moved_section P _ _ hB hPB hPE
    hE hEB (lt_of_lt_of_le (by decide : 2 < 8) hcard) hcore hmov
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (common_centralizer_of_marked_fixer D c e
      (Janko4.eq_one_of_fixes_odd_centralizer center_eq_bot_of_simple_perfect _ hodd))

theorem not_mathieuTwentyFour_of_fully_moved [IsQuasisimple I]
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M24) : False := by
  obtain ⟨P,hperfect,hB,hPB,hPE,hE,hEB,hcard,hcore,hmov⟩ := marked_fully_moved_data D c e
  let := hperfect
  have hodd := Sporadic.Mathieu.M24InvolutionCentralizers.centralizer_odd_of_fully_moved_section
    P _ _ hB hPB hPE hE hEB (lt_of_lt_of_le (by decide : 2 < 8) hcard) hcore hmov
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (common_centralizer_of_marked_fixer D c e
      (Sporadic.Mathieu.M24InvolutionCentralizers.eq_one_of_fixes_odd_centralizer _ hodd))

theorem not_binary_five_of_fully_moved [IsQuasisimple I]
    (h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* BinaryLinear.OuterCyclic.LinearGroup 5) : False := by
  obtain ⟨P,hperfect,hB,hPB,hPE,hE,hEB,hcard,hcore,hmov⟩ := marked_fully_moved_data D c e
  let := hperfect
  let : IsSimpleGroup (I ⧸ center I) := IsQuasisimple.simple
  let : IsSimpleGroup (BinaryLinear.OuterCyclic.LinearGroup 5) := e.symm.isSimpleGroup
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 5) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hodd := BinaryLinear.centralizer_odd_of_fully_moved_section
    (V := Fin 5 → ZMod 2)
    (by simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]; decide)
    (by rw [Module.finrank_pi,Fintype.card_fin]; decide)
    P _ _ hB hPB hPE hE hEB (lt_of_lt_of_le (by decide : 2 < 8) hcard) hcore hmov
  have h7B : 7 ∣ Nat.card B := by
    have hh := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hh ▸ h7).trans (card_quotient_dvd_card (pCore 2 B))
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (common_centralizer_of_marked_fixer D c e
      (BinaryLinear.five_eq_one_of_fixes_odd_centralizer center_eq_bot_of_simple_perfect B hodd h7B))

theorem not_binary_five_model_of_fully_moved [IsQuasisimple I]
    (h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L))
    (hI : ClassicalGroup.IsPSL (I ⧸ center I) 5 2) : False := by
  obtain ⟨F,_,_,hF,⟨eI⟩⟩ := hI
  let := Fintype.ofFinite F
  let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact not_binary_five_of_fully_moved D c h7
    ((eI.trans (Atlas.fieldEquivPSL 5 f)).trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)))

theorem not_higmanSims_of_fully_moved [IsQuasisimple I]
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  obtain ⟨P,_,_,hPB,hPE,hE,_,hcard,_,hmov⟩ := marked_fully_moved_data D c e
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have h168B : 168 ∣ Nat.card B := by
    have hh := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hh ▸ h168).trans (card_quotient_dvd_card (pCore 2 B))
  exact source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (common_centralizer_of_marked_fixer D c e
      (Sporadic.LeechRelated.HS.eq_one_of_fixes_normalized_large_section P B _ hPB hPE
        (le_normalizer_iff_commutator_le_left.mpr hmov.le) hE hcard h168B))

/-- The native Held comparison needs only this divisor of the original quotient. -/
theorem not_held_of_fully_moved [Group.IsPerfect I]
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* _root_.Held.He) : False := by
  obtain ⟨P,_,_,hPB,_⟩ := marked_fully_moved_data D c e
  let B := (L.subgroupOf I).map (e.toMonoidHom.comp (QuotientGroup.mk' (center I)))
  have hnoncentral := marked_core_center_not_central D c.strict.le e
  apply hnoncentral
  apply held_core_center_central P B hPB
  · intro hz
    apply hnoncentral
    rintro _ ⟨z,_,rfl⟩
    have he : (z : B) = 1 := mem_bot.mp (hz ▸ z.property)
    change (z : B) ∈ center B
    rw [he]
    exact one_mem _
  · have hh := Nat.card_congr (markedCoreQuotientEquiv D c.strict.le e).toEquiv
    exact (hh ▸ h168).trans (card_quotient_dvd_card (pCore 2 B))

/-- The M₂₃ moved-normalizer comparison also needs only the intrinsic divisor. -/
theorem not_mathieuTwentyThree_of_fully_moved [IsQuasisimple I]
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L))
    (e : (I ⧸ center I) ≃* Sporadic.Mathieu.M23) : False :=
  source_a5_point_component_common_centralizer_impossible D c.t_mem c.moved_normalizer
    I c.escapes (mathieuTwentyThree_common_centralizer D c h168 e)

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple.Other
