module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMixedQuotient
public import Theory.GroupTheory.Commutator.SmallNormalizedImage
public import Theory.GroupTheory.Commutator.FixedPointFree
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# The original natural layer inside the mixed right two-core

Let J be the right parabolic of the actual A5/S3 source pair. A two-group
with a fixed-free cubic has trivial image under every homomorphism to S3:
its image has order at most two, so the cubic centralizes that image.
Applying this to the marked right quotient puts the original natural layer
in O2(J). The other coordinate identifies O2(J) inside C_T(Z_S).

The J-conjugate span of the layer stays in O2(J), and its commutator with
O2(J) lies in the literal Z_S. It strictly enlarges the layer, since otherwise
that nontrivial two-group would be normal in the whole generated source pair,
contradicting the exact F.1.1 two-core condition. Removing the Borel supplement
identifies this span with the B-conjugate span. Thus the source abelian-closure
assumption makes it an actual elementary subgroup of order at least 32;
the marked quotient orders then give |T| at least 64.

The application retains the same escaping subgroup, full overlap, quotient
markings and unitary exclusions. These are local constraints for whole
mixed-amalgam recognition. Recognition, S5 parabolic escape, initial 6.1.4–5,
omega escape and the remaining geometry through unconditional 6.1.27 stay
with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.1–12
(`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
local notation "S3" => Equiv.Perm (Fin 3)

private theorem fixed_free_two_group_killed {H : Type*} [Group H] [Finite H]
    (f : H →* S3) (A : Subgroup H) (hp : IsPGroup 2 A)
    (c : H) (hc : c ∈ normalizer (A : Set H))
    (hfree : ∀ a ∈ A, Commute c a → a=1) : A ≤ f.ker := by
  obtain ⟨S,hS⟩ := (hp.map f).exists_le_sylow
  have hcard : Nat.card S=2 := by
    rw [S.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hle : Nat.card (A.map f) ≤ 2 := (card_le_of_le hS).trans_eq hcard
  have hh := commutator_le_ker_of_normalized_image_card_le_two f (zpowers c) A
    (zpowers_le.mpr hc) hle
  rw [commutator_comm,
    commutator_eq_of_fixedPointFree A (zpowers c) (zpowers_le.mpr hc) c
      (mem_zpowers c) hfree] at hh
  exact hh

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R B : Subgroup G}

/-- The original natural layer lies in the full right-parabolic two-core. -/
theorem natural_cubic_amalgam_layer_le_right_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* S3)
    (hr : NaturalCubicRightQuotientData T L R B e) :
    layer L R ≤ (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1).pCoreIn 2 := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let V := layer L R
  let Z := ZS (T : Subgroup G) L R
  obtain ⟨hBJ,hJN,a,eZ,hs,hk,ha,hcard,d,hd⟩ := hr
  let b := eZ.toMonoidHom.comp (Z.normalizerMonoidHom.comp (inclusion hJN))
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_left
  have hVJ : V ≤ J := h.layer_le_T.trans hTJ
  obtain ⟨c,hcL,hcTL,hcN,hc3,hcf⟩ := natural_four_exists_cubic h hnat
  have hJE := (natural_cubic_amalgam_overlap h hnat hF e hcL hcTL hc3).2.1
  have hcJ : c ∈ J := by change c ∈ ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1; rw [hJE]; exact mem_sup_right (mem_sup_left (mem_zpowers c))
  let cJ : J := ⟨c,hcJ⟩
  have hcV : cJ ∈ normalizer (V.subgroupOf J : Set J) := by
    apply mem_normalizer_iff.mpr
    intro v
    change (v : G) ∈ V ↔ c*(v : G)*c⁻¹ ∈ V
    exact mem_normalizer_iff.mp (normalizer_commutator_ge_right R L hcL) v
  have hfree : ∀ v ∈ V.subgroupOf J, Commute cJ v → v=1 := by
    intro v hv hcv
    apply Subtype.ext
    apply hnat.cubic_fixed_eq_one hcL hc3 hv
    exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val hcv.eq)
  have hak := fixed_free_two_group_killed a (V.subgroupOf J)
    (T.isPGroup'.to_le h.layer_le_T).comap_subtype cJ hcV hfree
  intro v hv
  have hb : b ⟨v,hVJ hv⟩=1 := by
    change eZ _ = 1
    rw [←eZ.map_one]
    apply congrArg eZ
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change v*(z : G)*v⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr ((h.layer_centralizes_ZS hv) z z.property).symm
  have hker : (⟨v,hVJ hv⟩ : J) ∈ (a.prod b.rangeRestrict).ker := by
    apply Prod.ext (hak hv)
    exact Subtype.ext hb
  change (a.prod b.rangeRestrict).ker = pCore 2 J at hk
  exact mem_map.mpr ⟨⟨v,hVJ hv⟩,hk ▸ hker,rfl⟩

omit [Finite G] in
/-- The entire right core is in the original Sylow and centralizes Z_S. -/
theorem natural_cubic_amalgam_right_core_le_line_sylow
    (e : (B ⧸ pCore 2 B) ≃* S3)
    (hr : NaturalCubicRightQuotientData T L R B e) :
    (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let Z := ZS (T : Subgroup G) L R
  obtain ⟨hBJ,hJN,a,eZ,hs,hk,ha,hcard,d,hd⟩ := hr
  let b := eZ.toMonoidHom.comp (Z.normalizerMonoidHom.comp (inclusion hJN))
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right.trans le_sup_left
  have hQT : J.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := J.pCoreIn_le_sylow (T.subtype hTJ)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] at hh
  refine le_inf hQT ?_
  rintro x ⟨y,hy,rfl⟩
  change (a.prod b.rangeRestrict).ker = pCore 2 J at hk
  have hyk : y ∈ (a.prod b.rangeRestrict).ker := hk.symm ▸ hy
  have hh : (a.prod b.rangeRestrict) y=1 := hyk
  have hb : b y=1 := congrArg (fun z => (z.2 : S3)) hh
  have he : Z.normalizerMonoidHom (inclusion hJN y)=1 :=
    eZ.injective (hb.trans eZ.map_one.symm)
  intro z hz
  have hf := congrArg Subtype.val (DFunLike.congr_fun he (⟨z,hz⟩ : Z))
  change (y : G)*z*(y : G)⁻¹=z at hf
  exact (mul_inv_eq_iff_eq_mul.mp hf).symm

/-- The right conjugate span lies in the same two-core and is central
modulo the original Z_S under that whole core. It strictly enlarges the layer. -/
theorem natural_cubic_amalgam_right_span
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* S3)
    (hr : NaturalCubicRightQuotientData T L R B e) :
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    let U := conjugateSpanBy (layer L R) J
    layer L R < U ∧ U ≤ J.pCoreIn 2 ∧
      ⁅U,J.pCoreIn 2⁆ ≤ ZS (T : Subgroup G) L R := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let V := layer L R
  let Z := ZS (T : Subgroup G) L R
  let Q := J.pCoreIn 2
  let U := conjugateSpanBy V J
  have hJQ : J ≤ normalizer (Q : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hVQ := natural_cubic_amalgam_layer_le_right_core h hnat hF e hr
  have hQI := natural_cubic_amalgam_right_core_le_line_sylow e hr
  have hJN : J ≤ normalizer (Z : Set G) := hr.choose_spec.choose
  have hUQ : U ≤ Q := conjugateSpanBy_le hVQ hJQ
  have hVcomm : ⁅V,Q⁆ ≤ Z := (commutator_mono le_rfl hQI).trans
    (natural_central_line_sylow_commutator h hnat).le
  have hQN : Q ≤ normalizer (Z : Set G) :=
    (hQI.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hUP : U ≤ commutatorPreimage Q Q Z := conjugateSpanBy_le
    (le_commutatorPreimage hVQ hVcomm)
    (commutatorPreimage_normalized Q Q Z J hQN hJQ hJQ hJN)
  refine ⟨lt_of_le_of_ne (le_conjugateSpanBy V J) ?_,hUQ,
    (commutator_mono hUP le_rfl).trans (commutator_commutatorPreimage_le Q Q Z hQN)⟩
  intro he
  have hJV : J ≤ normalizer (V : Set G) := by
    change V=U at he
    rw [he]
    exact le_normalizer_conjugateSpanBy V J
  let H := ChapterF.Source.generated ![L,B] (T : Subgroup G)
  have hHV : H ≤ normalizer (V : Set G) := by
    change L ⊔ B ⊔ (T : Subgroup G) ≤ _
    exact sup_le (sup_le (normalizer_commutator_ge_right R L)
      ((show B ≤ J from le_sup_left.trans le_sup_left).trans hJV)) h.sylow_normalizes_layer
  have hVH : V ≤ H := h.layer_le_T.trans le_sup_right
  have hh := le_pCoreIn_of_normalizes (T.isPGroup'.to_le h.layer_le_T) hVH hHV
  have hzero : H.pCoreIn 2=⊥ := by
    change (pCore 2 H).map H.subtype=⊥
    rw [hF.twoCore_free,Subgroup.map_bot]
  exact h.nontrivial_action (bot_unique (hh.trans_eq hzero))
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R B : Subgroup G}

/-- Adjoining the full Borel does not enlarge the B-conjugate span:
the original cubic and Sylow both preserve the natural seed. -/
theorem natural_cubic_amalgam_right_span_eq
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) :
    conjugateSpanBy (layer L R)
      (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) =
        conjugateSpanBy (layer L R) B := by
  rw [ChapterF.Source.parabolic_eq_sup_commonBorel]
  apply conjugateSpanBy_sup_of_normalizes_seed
  · rw [(natural_cubic_amalgam_products hF e).2.1]
    exact sup_le ((ChapterF.Source.borel_le L (T : Subgroup G)).trans
      (normalizer_commutator_ge_right R L)) h.sylow_normalizes_layer
  · exact hF.commonBorel_normalizes_local 1

/-- Under the source abelian-closure assumption, the same right span is an
actual elementary subgroup of the original two-core, of order at least 32. -/
theorem natural_cubic_amalgam_right_elementary_span
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hr : NaturalCubicRightQuotientData T L R B e)
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
    let U := conjugateSpanBy (layer L R) J
    U ≤ Escape.U (T : Subgroup G) L R ∧ IsElementaryAbelian 2 U ∧
      32 ≤ Nat.card U ∧ 32 ≤ Nat.card (pCore 2 J) ∧ 64 ≤ Nat.card T := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  have hUI : U ≤ Escape.U (T : Subgroup G) L R := by
    rw [show U = conjugateSpanBy (layer L R) B from
      natural_cubic_amalgam_right_span_eq h hF e]
    have he : conjugateSpanBy (layer L R) (Escape.I (T : Subgroup G) L R) =
        Escape.U (T : Subgroup G) L R := by
      rw [conjugateSpanBy_eq_iSup_conj]
      rfl
    rw [←he]
    exact conjugateSpanBy_mono le_rfl hBI
  let := h.layer_elementary
  let : IsMulCommutative U := le_centralizer_iff_isMulCommutative.mp
    (hUI.trans (hab.trans (centralizer_le hUI)))
  let : IsElementaryAbelian 2 U := conjugateSpanBy_elementary_of_commutative _ _
  obtain ⟨hVU,hUQ,hcomm⟩ := natural_cubic_amalgam_right_span h hnat hF e hr
  have hlt : 16 < Nat.card U := by
    have hh : Nat.card (layer L R) < Nat.card U := Set.ncard_lt_ncard hVU
    simpa only [hnat.card,show 2^(2*2)=16 from rfl] using hh
  obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 U).exists_card_eq
  have hk5 : 5 ≤ k := by
    have hh : 2^4 < 2^k := hk ▸ hlt
    exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp hh
  have h32 : 32 ≤ Nat.card U := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0<2) hk5
  have hQ : 32 ≤ Nat.card (pCore 2 J) := by
    have hh := card_le_of_le hUQ
    change Nat.card U ≤ Nat.card ((pCore 2 J).map J.subtype) at hh
    rw [card_map_of_injective J.subtype_injective] at hh
    exact h32.trans hh
  refine ⟨hUI,inferInstance,h32,hQ,?_⟩
  rcases natural_cubic_amalgam_right_models_and_sizes hnat hF e hr with hh | hh
  · have he := hh.2
    change Nat.card T = 2 * Nat.card (pCore 2 J) at he
    omega
  · have he := hh.2
    change Nat.card T = 4 * Nat.card (pCore 2 J) at he
    omega
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

/-- The actual natural span and its interaction with the full right two-core.
All subgroups remain in the original ambient group. -/
@[expose] def NaturalCubicRightCoreData (T : Sylow 2 G) (L R B : Subgroup G) : Prop :=
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  layer L R < U ∧ U ≤ J.pCoreIn 2 ∧
    J.pCoreIn 2 ≤ (T : Subgroup G) ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) ∧
    ⁅U,J.pCoreIn 2⁆ ≤ ZS (T : Subgroup G) L R ∧
    U ≤ Escape.U (T : Subgroup G) L R ∧ IsElementaryAbelian 2 U ∧
    32 ≤ Nat.card U ∧ 32 ≤ Nat.card (pCore 2 J) ∧ 64 ≤ Nat.card T

/-- The escaping pair retains its original markings and now includes the
actual elementary span inside the right two-core. -/
@[expose] def NaturalEscapingAmalgamCoreData (T : Sylow 2 G) (L R P N M : Subgroup G) : Prop :=
  ∃ B : Subgroup G, B ≤ P ⊔ N.pCoreIn 2 ∧
    B ≤ Escape.I (T : Subgroup G) L R ∧ (¬ B ≤ M) ∧
    Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) ∧
    ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G) ∧
    Group.IsSolvable (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) ∧
    ChapterF.Source.LocallyRankOneTriple
      (fun i => (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) i).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G)))
      ((ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)).subgroupOf
        (ChapterF.Source.generated ![L,B] (T : Subgroup G))) ∧ NaturalUnitaryAmalgamExclusion T L B ∧
    ∀ e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3),
      NaturalCubicRightQuotientData T L R B e ∧
      NaturalCubicRightCoreData T L R B ∧
      let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 3)) ∧
        Nat.card T = 2 * Nat.card (pCore 2 J)) ∨
      (Nonempty ((J ⧸ pCore 2 J) ≃*
          Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
        Nat.card T = 4 * Nat.card (pCore 2 J))

variable [Finite G] {T : Sylow 2 G} {L M R P N : Subgroup G}

/-- Construct the right-core geometry on the same escaping subgroup and
retain the quotient equation, full overlap and both unitary exclusions. -/
theorem natural_escaping_amalgam_right_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G))
    (d : NaturalEscapingAmalgamRightData T L R P N M) :
    NaturalEscapingAmalgamCoreData T L R P N M := by
  obtain ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,hright⟩ := d
  refine ⟨B,hBK,hBI,hBM,he,hF,hsolv,htriple,hno,fun e => ?_⟩
  obtain ⟨hr,hmodels⟩ := hright e
  obtain ⟨hlt,hUQ,hcomm⟩ := natural_cubic_amalgam_right_span h hnat hF e hr
  obtain ⟨hUI,hUE,h32,hQ32,hT64⟩ :=
    natural_cubic_amalgam_right_elementary_span h hnat hF e hr hBI hab
  exact ⟨hr,⟨hlt,hUQ,natural_cubic_amalgam_right_core_le_line_sylow e hr,
    hcomm,hUI,hUE,h32,hQ32,hT64⟩,hmodels⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
