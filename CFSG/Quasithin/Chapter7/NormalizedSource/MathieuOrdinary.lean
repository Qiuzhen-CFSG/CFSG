module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPointControl
public import Theory.GroupTheory.PerfectSimpleImageKernel
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.PushingUpComponents
/-!
# Ordinary components above a normal M22 residual

A perfect group with quotient M22 modulo its two-core acts nontrivially on
the image of its nonzero moved elementary module in a containing central
quotient. The action has solvable kernel. Eleven therefore divides the
order of the image automorphism group, forcing dimension at least ten.
This argument retains the module's central kernel.

In the genuine C.2.8 configuration the original normal M22 residual and
its moved module now exclude the rank-one and rank-two Lie alternatives.
The actual ordinary component has central quotient J4. If the original
module has order 2048 and contains a nonidentity central vector, its
quotient image has order 1024 and its entire kernel is that vector's line.

The chosen-module application is NonFFSourceMathieuOrdinary. Excluding
this full J4 central two-cover still requires the two-primary consequence
of I.1.3; source 8.1.1 and ambient J4 assembly remain with
qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith C.3.1, I.1.3 and8.1.1, printed pp.149--151,
407 and712--713, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open Sporadic.Mathieu MathieuCode
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs

private theorem eleven_free_small_automorphisms
    (E : Type*) [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hc : Nat.card E ≤ 2 ^ 9) : ¬ 11 ∣ Nat.card (MulAut E) := by
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hb : d ≤ 9 := by
    rw [hd] at hc
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E d hd]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

/-- A nonzero moved elementary module for an M22 residual forces a
large elementary image in the containing group's central quotient. -/
theorem m22_residual_elementary_image_card
    {G : Type*} [Group G] [Finite G]
    (F K W : Subgroup G) [Group.IsPerfect F] [IsElementaryAbelian 2 W]
    (hFK : F ≤ K) (hWF : W ≤ F) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* M22) :
    1024 ≤ Nat.card ((W.subgroupOf K).map (QuotientGroup.mk' (center K))) := by
  let q := QuotientGroup.mk' (center K)
  let A := F.subgroupOf K
  let U := W.subgroupOf K
  have hWK := hWF.trans hFK
  let w : U ≃* W := subgroupOfEquivOfLe hWK
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective w.toMonoidHom w.injective
  let E := U.map q
  let B := A.map q
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map q
  have hmove : E = ⁅E,B⁆ := by
    change U.map q = ⁅U.map q,A.map q⁆
    rw [←map_commutator]
    apply congrArg (map q)
    apply map_injective K.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hFK]
    exact hcomm
  have hEne : E ≠ ⊥ := by
    intro hb
    have hc : U ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff U).mp hb
    have hWC : W ≤ centralizer (F : Set G) := by
      intro v hv f hf
      exact congrArg K.subtype (mem_center_iff.mp (hc (show (⟨v,hWK hv⟩ : K) ∈ U from hv))
        ⟨f,hFK hf⟩)
    exact hne (hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr hWC))
  let r : F →* (K ⧸ center K) := q.comp (inclusion hFK)
  have hr : r.range = B := by
    rw [MonoidHom.range_comp]
    congr 1
    ext k
    constructor
    · rintro ⟨f,rfl⟩; exact f.property
    · intro hk; exact ⟨⟨k,hk⟩,rfl⟩
  have hn : B ≤ normalizer (E : Set (K ⧸ center K)) :=
    le_normalizer_iff_commutator_le_left.mpr hmove.symm.le
  let t : F →* normalizer (E : Set (K ⧸ center K)) := r.codRestrict _
    (fun f => hn (hr ▸ (show r f ∈ r.range from ⟨f,rfl⟩)))
  let act : F →* MulAut E := E.normalizerMonoidHom.comp t
  have hact : act ≠ 1 := by
    intro he
    apply hEne
    rw [hmove]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro v hv b hb
    obtain ⟨f,hf⟩ := hr.symm ▸ hb
    have hh := congrArg (fun z : MulAut E => ((z ⟨v,hv⟩ : E) : K ⧸ center K))
      (DFunLike.congr_fun he f)
    change r f * v * (r f)⁻¹ = v at hh
    rw [mul_inv_eq_iff_eq_mul] at hh
    simpa only [hf] using hh
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let := m22_isSimpleGroup
  let : Group.IsPerfect M22 := pairResidual_m22_perfect
  let : Group.IsSolvable π.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
    infer_instance
  let : Group.IsSolvable act.ker :=
    solvable_ker_of_nontrivial_hom_of_simple_quotient π hπ act hact
  have h11 : 11 ∣ Nat.card (MulAut E) :=
    (by rw [m22_order]; decide : 11 ∣ Nat.card M22).trans
      (SimpleSection.card_dvd_of_solvable_representation
        (Group.IsPerfect.not_isSolvable M22) π hπ act)
  obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
  have hb : 10 ≤ d := by
    by_contra hb
    have hc : Nat.card E ≤ 2^9 := by
      rw [hd]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact eleven_free_small_automorphisms E hc h11
  change 1024 ≤ Nat.card E
  rw [hd]
  exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb

/-- The image bound applies to the literal containing central quotient. -/
theorem m22_residual_central_quotient_twoRank
    {G : Type*} [Group G] [Finite G]
    (F K W : Subgroup G) [Group.IsPerfect F] [IsElementaryAbelian 2 W]
    (hFK : F ≤ K) (hWF : W ≤ F) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* M22) :
    10 ≤ primeRank 2 (K ⧸ center K) := by
  let U := W.subgroupOf K
  let w : U ≃* W := subgroupOfEquivOfLe (hWF.trans hFK)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective w.toMonoidHom w.injective
  let E := U.map (QuotientGroup.mk' (center K))
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hl := m22_residual_elementary_image_card F K W hFK hWF hne hcomm e
  by_contra hb
  have hc : Nat.card E ≤ 2^9 :=
    (primeRank_le_iff_elementary_card_le (K ⧸ center K)).mp (by omega) E inferInstance
  change 1024 ≤ Nat.card E at hl
  norm_num at hc
  omega


/-- The ordinary branch of a normal M22 pushing-up seed has central quotient J4.
The elementary module is allowed to meet the component center. -/
theorem m22_seed_ordinary_central_quotient
    {G : Type*} [Group G] [Finite G] {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (e : (F ⧸ pCore 2 F) ≃* M22)
    (K : Subgroup H) (hK : IsComponent H K) :
    Nonempty ((K ⧸ center K) ≃* Janko4.Model) := by
  let J := K.map H.subtype
  have hFJ : F ≤ J := by
    intro f hf
    exact ⟨⟨f,h.component_le.trans h.local_le hf⟩,
      h.ordinary_component_contains_original K hK hf,rfl⟩
  let a : J ≃* K := (K.equivMapOfInjective H.subtype H.subtype_injective).symm
  let z := QuotientGroup.congr (center J) (center K) a (FixedElementary.map_center a)
  have hspan : conjugateSpanBy F M = F :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy F M)
  let : Group.IsPerfect F := hspan ▸ h.span_perfect
  let := h.module_elementary
  have hWF : W ≤ F := hspan ▸ h.module_le
  have hmove : W = ⁅W,F⁆ := hspan ▸ h.module_commutator
  have hne : W ≠ ⊥ := h.module_nontrivial
  have hWFcore : W ≤ F.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 W) hWF
    (le_normalizer_iff_commutator_le_left.mpr hmove.symm.le)
  let := hK.2
  have hs := h.sqtk.subgroup K
  have hmodel := ChapterA.Section02.quasisimple_centralQuotient_theoremBModel
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremB_knownSimple
    hs.stronglyQuasithin.quasithin hs.isKGroup
  have hr : 10 ≤ primeRank 2 (K ⧸ center K) := by
    have hh := m22_residual_central_quotient_twoRank F J W hFJ hWF hne hmove e
    rwa [primeRank_congr 2 z] at hh
  have hnb : ¬ ClassificationModels.IsBenderModel (K ⧸ center K) := by
    intro hb
    exact Chapter4.Section04.NormalizedRankOneOddControl.no_bender_of_residual_module
      J F W hFJ hWFcore hne hmove (hb.of_mulEquiv z)
  rcases MathieuGeneration.rankTwo_or_jankoFour_of_mathieu_rank hmodel hr hnb with
    ⟨n,hm⟩ | hj
  · exfalso
    let := m22_isSimpleGroup
    let : IsQuasisimple M22 :=
      { toIsPerfect := pairResidual_m22_perfect
        simple := ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
          QuotientGroup.quotientBot).isSimpleGroup }
    let c : (M22 ⧸ center M22) ≃* M22 :=
      (QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans QuotientGroup.quotientBot
    let π : F →* (M22 ⧸ center M22) := c.symm.toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F)))
    have hπ : Function.Surjective π := c.symm.surjective.comp
      (e.surjective.comp (QuotientGroup.mk'_surjective _))
    exact MathieuGeneration.no_rankTwo_of_mathieu_residual F J W hFJ hWFcore hne hmove
      (Or.inr (Or.inl ⟨c⟩)) π hπ (hm.of_mulEquiv z)
  · exact hj

/-- A distinguished central vector is the entire kernel on the original
2048-element module. The quotient image has order 1024. -/
theorem m22_residual_eleven_space_kernel
    {G : Type*} [Group G] [Finite G]
    (F K W : Subgroup G) [Group.IsPerfect F] [IsElementaryAbelian 2 W]
    (hFK : F ≤ K) (hWF : W ≤ F) (hne : W ≠ ⊥) (hcomm : W = ⁅W,F⁆)
    (e : (F ⧸ pCore 2 F) ≃* M22) (hcard : Nat.card W = 2048)
    (x : W) (hx : x ≠ 1) (hz : inclusion (hWF.trans hFK) x ∈ center K) :
    let f := (QuotientGroup.mk' (center K)).comp (inclusion (hWF.trans hFK))
    Nat.card f.range = 1024 ∧ Nat.card f.ker = 2 ∧ f.ker = zpowers x := by
  let f := (QuotientGroup.mk' (center K)).comp (inclusion (hWF.trans hFK))
  have hfr : f.range = (W.subgroupOf K).map (QuotientGroup.mk' (center K)) := by
    rw [MonoidHom.range_comp]
    congr 1
    ext k
    constructor
    · rintro ⟨w,rfl⟩; exact w.property
    · intro hk; exact ⟨⟨k,hk⟩,rfl⟩
  have hr : 1024 ≤ Nat.card f.range := hfr ▸
    m22_residual_elementary_image_card F K W hFK hWF hne hcomm e
  have hxk : x ∈ f.ker := (QuotientGroup.eq_one_iff _).mpr hz
  let : Nontrivial f.ker := ⟨⟨⟨x,hxk⟩,1,fun he => hx (congrArg Subtype.val he)⟩⟩
  have hk : 2 ≤ Nat.card f.ker := Finite.one_lt_card
  have hc := f.ker.card_mul_index
  rw [index_ker,hcard] at hc
  have heR : Nat.card f.range = 1024 := by nlinarith
  have heK : Nat.card f.ker = 2 := by nlinarith
  refine ⟨heR,heK,?_⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hxk) ?_).symm
  rw [Nat.card_zpowers,heK]
  have ho : orderOf x = 2 := orderOf_eq_prime
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) x.property)) hx
  exact ho.symm.le

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairs
