module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCore
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFusionComplete

/-!
# The moving pair and the action quotient in the escaping closure

The elementary quotient U/Z_S makes the actual image of U on V_L elementary.
The natural SL₂ automizer bounds its order by 2ⁿ. For a noncommuting conjugate
A of V_L in I, the proved common-line geometry gives C_A(V_L) = Z_S, so that
A already attains this bound. Hence U = A C_U(V_L). Conjugating gives the
opposite factorization, and together these give U = V_L A C_U(V_L A).
The literal quotient U/C_U(V_L) is elementary of order 2ⁿ.

These are the product and action-quotient assertions in source 6.1.20(4).
Nonabelianness supplies a moving pair, but its proof from the escaping source
hypotheses, the maximal-elementary assertion, and the later core/section
geometry are not asserted here. The final constructor discharges six fields
of the existing `NaturalEscape.Geometry` interface from the proved natural
and pair data, retaining the remaining source identities explicitly.
Their discharge and the initial natural marking remain with
qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith, 6.1.10–11 and 6.1.20(4), printed pp.670, 675;
the geometric size consumer is 6.1.26 on pp.678–679.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem image_card_eq_index (B A : Subgroup G)
    (hAN : A ≤ normalizer (B : Set G)) :
    Nat.card (ChapterE.inducedAutomizer B A) = (A ⊓ centralizer (B : Set G)).relIndex A := by
  unfold ChapterE.inducedAutomizer
  rw [← Subgroup.relIndex_ker, MonoidHom.ker_rangeRestrict,
    Subgroup.normalizerMonoidHom_ker, Subgroup.relIndex_subgroupOf hAN,
    Subgroup.inf_relIndex_left]

omit [Finite G] in
private theorem image_elementary_of_quotient (B A Z : Subgroup G)
    [hZ : (Z.subgroupOf A).Normal] [IsElementaryAbelian 2 (A ⧸ Z.subgroupOf A)]
    (hAN : A ≤ normalizer (B : Set G)) (hZC : Z ≤ centralizer (B : Set G)) :
    IsElementaryAbelian 2 (ChapterE.inducedAutomizer B A) := by
  let f := NaturalAction.layerAction hAN
  have hk : Z.subgroupOf A ≤ f.ker := by
    intro z hz
    apply Subtype.ext
    change (NaturalAction.layerAction hAN z : ChapterE.Automizer B) = 1
    rw [NaturalAction.layerAction_coe]
    apply Subtype.ext
    change B.normalizerMonoidHom ⟨z,hAN z.property⟩ = 1
    change (⟨z,hAN z.property⟩ : normalizer (B : Set G)) ∈ B.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hZC hz
  let fQ := QuotientGroup.lift (Z.subgroupOf A) f hk
  apply IsElementaryAbelian.of_surjective fQ
  intro a
  obtain ⟨z,rfl⟩ := NaturalAction.layerAction_surjective hAN a
  exact ⟨QuotientGroup.mk' (Z.subgroupOf A) z,rfl⟩

private theorem natural_elementary_image_card_le {L B : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 B] (hn : 2 ≤ n)
    (hnatural : IsNaturalModule L B n)
    (hNL : normalizer (B : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup (ChapterE.Automizer B)) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 2 ^ n := by
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra _ 2
  obtain ⟨j,E,hE⟩ := NaturalAction.marking e f hf
  let C := ChapterE.inducedAutomizer B L
  let : C.Normal := NaturalAction.induced_normal hNL
  let τ : Representation (ZMod 2) (ChapterE.Automizer B) (Fin 2 → F) :=
    E.conjRingEquiv.toMonoidHom.comp (ChapterE.automizerRepresentation B)
  have hτ : Function.Injective τ :=
    E.conjRingEquiv.injective.comp (ChapterE.automizerRepresentation_injective B)
  have hnat : ∀ (g : C) v, τ (g : ChapterE.Automizer B) v =
      Matrix.mulVec (j g).val v := by
    intro g v
    change E (ChapterE.automizerRepresentation B g (E.symm v)) = _
    rw [hE,E.apply_symm_apply]
  exact (primeRank_le_iff_elementary_card_le (ChapterE.Automizer B)).mp
    (Representation.SL2NaturalOffenders.faithful_extension_rank_le C j τ hτ hnat hn hF) A hA

variable {κ : GroupClass} {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

theorem natural_escape_centralizer_index_le
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V)) :
    (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)).relIndex
      (Escape.U (T : Subgroup G) L V) ≤ 2 ^ n := by
  let := h.layer_elementary
  let := h.ZS_normal_in_escape_U
  let := natural_escape_quotient_elementary h hnatural
  have hUN := (natural_escape_U_le_sylow h hnatural).trans h.sylow_normalizes_layer
  rw [← image_card_eq_index _ _ hUN]
  exact natural_elementary_image_card_le h.n_gt_one hnatural
    (hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)) _
    (image_elementary_of_quotient (layer L V) (Escape.U (T : Subgroup G) L V)
      (ZS (T : Subgroup G) L V) hUN (inf_le_left.trans (le_centralizer _)))


/-- Every centralizer conjugate of the seed is normal in the closure. -/
theorem natural_escape_pair_normalizes
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V) :
    (layer L V).map (MulAut.conj g).toMonoidHom ≤ Escape.U (T : Subgroup G) L V ∧
      Escape.U (T : Subgroup G) L V ≤
        normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hUN := (natural_escape_U_le_sylow h hnatural).trans h.sylow_normalizes_layer
  have hUg := mem_normalizer_iff_map_conj_eq.mp
    (NaturalEscape.I_normalizes_U (T : Subgroup G) L V hg)
  change (Escape.U (T : Subgroup G) L V).map (MulAut.conj g).toMonoidHom = _ at hUg
  refine ⟨le_iSup (fun i : Escape.I (T : Subgroup G) L V =>
    (layer L V).map (MulAut.conj (i : G)).toMonoidHom) ⟨g,hg⟩, ?_⟩
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hUN
  rwa [hUg, map_equiv_normalizer_eq] at hh

/-- The source common-line identities for a noncommuting pair in U. -/
theorem natural_escape_pair_lines
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V)
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (layer L V : Set G)) :
    let B := layer L V
    let A := B.map (MulAut.conj g).toMonoidHom
    let Z := ZS (T : Subgroup G) L V
    B ⊓ centralizer (A : Set G) = Z ∧ A ⊓ centralizer (B : Set G) = Z ∧
      ⁅B,A⁆ = Z ∧ B ⊓ A = Z := by
  obtain ⟨hAU,hUN⟩ := natural_escape_pair_normalizes h hnatural hg
  obtain ⟨h1,h2,h3,h4,_⟩ := mutual_conjugate_line_geometry h hnatural hs
    (elementaryActionRankBound_of_natural h hnatural hE)
    (naturalOffenderFixedLines_of_natural h hnatural hE) g
    (hAU.trans (natural_escape_U_le_sylow h hnatural)) hnon
    ((Escape.layer_le_U _ _ _).trans hUN)
  exact ⟨h1,h2,h3,h4⟩

/-- Once a pair moves the seed, the full U action has exactly order 2^n. -/
theorem natural_escape_centralizer_index
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V)
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤
      centralizer (layer L V : Set G)) :
    (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)).relIndex
      (Escape.U (T : Subgroup G) L V) = 2 ^ n := by
  let B := layer L V
  let A := B.map (MulAut.conj g).toMonoidHom
  let Z := ZS (T : Subgroup G) L V
  have hfix : A ⊓ centralizer (B : Set G) = Z :=
    (natural_escape_pair_lines h hnatural hE hs hg hnon).2.1
  have hcardZ : Nat.card Z = 2 ^ n :=
    (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  have hcardA : Nat.card A = 2 ^ n * 2 ^ n := by
    rw [card_map_of_injective (MulAut.conj g).injective, hnatural.card]
    rw [Nat.mul_two, pow_add]
  have hidx : (centralizer (B : Set G)).relIndex A = 2 ^ n := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Z A bot_le (hfix ▸ inf_le_left)
    rw [relIndex_bot_left, relIndex_bot_left, hcardZ, hcardA] at hh
    have he := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n) hh
    rwa [← hfix, inf_relIndex_left] at he
  apply le_antisymm (natural_escape_centralizer_index_le h hnatural hE)
  rw [inf_relIndex_left, ← hidx]
  exact relIndex_le_of_le_right (natural_escape_pair_normalizes h hnatural hg).1
    ((centralizer (B : Set G)).subgroupOf (Escape.U (T : Subgroup G) L V)).index_ne_zero_of_finite


omit [Finite G] in
private theorem centralizer_map_equiv (A : Subgroup G) (f : G ≃* G) :
    (centralizer (A : Set G)).map f.toMonoidHom =
      centralizer (A.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine mem_map.mpr ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    apply f.injective
    simpa using mem_centralizer_iff.mp hx (f a) (mem_map.mpr ⟨a, ha, rfl⟩)

omit [Finite G] in
/-- Nonabelianness of the closure produces a moving conjugate of the seed. -/
theorem natural_escape_exists_pair
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G)) :
    ∃ g ∈ Escape.I (T : Subgroup G) L V,
      ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G) := by
  by_contra! hh
  apply hnon
  have hUB : Escape.U (T : Subgroup G) L V ≤ centralizer (layer L V : Set G) :=
    iSup_le fun i => hh i i.property
  apply iSup_le
  intro i
  have hm := map_mono (f := (MulAut.conj (i : G)).toMonoidHom) (le_centralizer_iff.mp hUB)
  rw [centralizer_map_equiv] at hm
  have hUi := mem_normalizer_iff_map_conj_eq.mp
    (NaturalEscape.I_normalizes_U (T : Subgroup G) L V i.property)
  change (Escape.U (T : Subgroup G) L V).map (MulAut.conj (i : G)).toMonoidHom = _ at hUi
  rwa [hUi] at hm

private theorem sup_eq_of_index_eq {A C U : Subgroup G}
    (hAU : A ≤ U) (hCU : C ≤ U) (hCN : U ≤ normalizer (C : Set G))
    (hidx : C.relIndex A = C.relIndex U) : A ⊔ C = U := by
  let : (C.subgroupOf U).Normal := normal_subgroupOf_of_le_normalizer hCN
  have hi := relIndex_sup_right (A.subgroupOf U) (C.subgroupOf U)
  rw [← subgroupOf_sup hAU hCU, relIndex_subgroupOf (sup_le hAU hCU),
    relIndex_subgroupOf hAU] at hi
  have hm := relIndex_mul_relIndex C (A ⊔ C) U le_sup_right (sup_le hAU hCU)
  rw [hi,hidx] at hm
  have h1 : (A ⊔ C).relIndex U = 1 :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (C.subgroupOf U).index_ne_zero_of_finite)
      (hm.trans (mul_one _).symm)
  exact le_antisymm (sup_le hAU hCU) (relIndex_eq_one.mp h1)

omit [Finite G] in
private theorem centralizer_sup_eq (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

omit [Finite G] in
private theorem pair_product {A B U : Subgroup G} [IsMulCommutative B]
    (hAU : A ≤ U) (hBU : B ≤ U) (hUN : U ≤ normalizer (B : Set G))
    (ha : A ⊔ (U ⊓ centralizer (B : Set G)) = U)
    (hb : B ⊔ (U ⊓ centralizer (A : Set G)) = U) :
    U = (B ⊔ A) ⊔ (U ⊓ centralizer ((B ⊔ A : Subgroup G) : Set G)) := by
  apply le_antisymm
  · apply le_trans ha.symm.le
    apply sup_le (le_sup_right.trans le_sup_left)
    intro x hx
    have hxprod : x ∈ (B : Set G) * ((U ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left B (U ⊓ centralizer (A : Set G))
        (inf_le_left.trans hUN),hb]
      exact hx.1
    obtain ⟨b,hbB,c,hc,he⟩ := hxprod
    change b * c = x at he
    have hcB : c ∈ centralizer (B : Set G) :=
      (centralizer (B : Set G)).mul_mem_cancel_left ((le_centralizer B) hbB) |>.mp
        (by rw [he]; exact hx.2)
    have hcBA : c ∈ centralizer ((B ⊔ A : Subgroup G) : Set G) := by
      rw [centralizer_sup_eq]
      exact ⟨hcB,hc.2⟩
    rw [← he]
    exact mul_mem_sup ((show B ≤ B ⊔ A from le_sup_left) hbB) ⟨hc.1,hcBA⟩
  · exact sup_le (sup_le hBU hAU) inf_le_left

/-- Source 6.1.20(4): the moving pair splits off its common centralizer.
Both relative centralizer indices are computed on the literal U. -/
theorem natural_escape_pair_product
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V)
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G)) :
    let B := layer L V
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := Escape.U (T : Subgroup G) L V
    U = (B ⊔ A) ⊔ (U ⊓ centralizer ((B ⊔ A : Subgroup G) : Set G)) ∧
      (U ⊓ centralizer (B : Set G)).relIndex U = 2 ^ n ∧
      (centralizer (A : Set G)).relIndex U = 2 ^ n := by
  let B := layer L V
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := Escape.U (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let := h.layer_elementary
  have hBU : B ≤ U := Escape.layer_le_U _ _ _
  have hUBN := (natural_escape_U_le_sylow h hnatural).trans h.sylow_normalizes_layer
  obtain ⟨hAU,hUAN⟩ := natural_escape_pair_normalizes h hnatural hg
  obtain ⟨hfixB,hfixA,_,_⟩ := natural_escape_pair_lines h hnatural hE hs hg hnon
  have hi := natural_escape_centralizer_index h hnatural hE hs hg hnon
  have hUg := mem_normalizer_iff_map_conj_eq.mp
    (NaturalEscape.I_normalizes_U (T : Subgroup G) L V hg)
  change U.map (MulAut.conj g).toMonoidHom = U at hUg
  have hiA : (centralizer (A : Set G)).relIndex U = 2 ^ n := by
    have hm := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (centralizer (B : Set G)) U (MulAut.conj g).injective
    change ((centralizer (B : Set G)).map (MulAut.conj g).toMonoidHom).relIndex
      (U.map (MulAut.conj g).toMonoidHom) = _ at hm
    rw [centralizer_map_equiv,hUg] at hm
    exact hm.trans (by simpa only [inf_relIndex_left] using hi)
  have hcZ : Nat.card Z = 2 ^ n :=
    (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
  have hcB : Nat.card B = 2 ^ n * 2 ^ n := by
    rw [hnatural.card,Nat.mul_two,pow_add]
  have hcA : Nat.card A = Nat.card B := card_map_of_injective (MulAut.conj g).injective
  have hindex (X Y : Subgroup G) (hfix : X ⊓ centralizer (Y : Set G) = Z)
      (hX : Nat.card X = 2 ^ n * 2 ^ n) : (centralizer (Y : Set G)).relIndex X = 2 ^ n := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) Z X bot_le (hfix ▸ inf_le_left)
    rw [relIndex_bot_left,relIndex_bot_left,hcZ,hX] at hm
    have he := Nat.eq_of_mul_eq_mul_left (by positivity : 0 < 2 ^ n) hm
    rwa [← hfix,inf_relIndex_left] at he
  have hgenA : A ⊔ (U ⊓ centralizer (B : Set G)) = U := by
    apply sup_eq_of_index_eq hAU inf_le_left
      ((le_inf U.le_normalizer (hUBN.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf)
    rw [show (U ⊓ centralizer (B : Set G)).relIndex A = (centralizer (B : Set G)).relIndex A by
      rw [inf_comm, ← inf_relIndex_right _ A, inf_assoc, inf_of_le_right hAU,inf_relIndex_right]]
    exact (hindex A B hfixA (hcA.trans hcB)).trans hi.symm
  have hgenB : B ⊔ (U ⊓ centralizer (A : Set G)) = U := by
    apply sup_eq_of_index_eq hBU inf_le_left
      ((le_inf U.le_normalizer (hUAN.trans (normalizer_le_normalizer_centralizer A))).trans
        inf_normalizer_le_normalizer_inf)
    rw [show (U ⊓ centralizer (A : Set G)).relIndex B = (centralizer (A : Set G)).relIndex B by
      rw [inf_comm, ← inf_relIndex_right _ B, inf_assoc, inf_of_le_right hBU,inf_relIndex_right]]
    exact (hindex B A hfixB hcB).trans (by simpa only [inf_relIndex_left] using hiA.symm)
  exact ⟨pair_product hAU hBU hUBN hgenA hgenB,hi,hiA⟩


/-- The action kernel is normal relative to the actual U. -/
theorem natural_escape_action_kernel_normal
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ((centralizer (layer L V : Set G)).subgroupOf (Escape.U (T : Subgroup G) L V)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((natural_escape_U_le_sylow h hnatural).trans h.sylow_normalizes_layer).trans
      (normalizer_le_normalizer_centralizer _))

/-- The literal action quotient in 6.1.20(4) is elementary of order 2^n. -/
theorem natural_escape_pair_action_quotient
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    {g : G} (hg : g ∈ Escape.I (T : Subgroup G) L V)
    (hnon : ¬ (layer L V).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L V : Set G)) :
    letI := natural_escape_action_kernel_normal h hnatural
    let Q := Escape.U (T : Subgroup G) L V ⧸
      (centralizer (layer L V : Set G)).subgroupOf (Escape.U (T : Subgroup G) L V)
    IsElementaryAbelian 2 Q ∧ Nat.card Q = 2 ^ n := by
  let U := Escape.U (T : Subgroup G) L V
  let C := (centralizer (layer L V : Set G)).subgroupOf U
  let Z := (ZS (T : Subgroup G) L V).subgroupOf U
  let := natural_escape_action_kernel_normal h hnatural
  let := h.ZS_normal_in_escape_U
  let := natural_escape_quotient_elementary h hnatural
  let := h.layer_elementary
  have hZC : Z ≤ C.comap (MonoidHom.id U) := by
    intro z hz
    exact (le_centralizer (layer L V)) (show (z : G) ∈ layer L V from hz.1)
  let f := QuotientGroup.map Z C (MonoidHom.id U) hZC
  refine ⟨IsElementaryAbelian.of_surjective f
    (QuotientGroup.map_surjective_of_surjective Z C (MonoidHom.id U)
      (QuotientGroup.mk'_surjective C) hZC), ?_⟩
  exact (inf_relIndex_left U (centralizer (layer L V : Set G))).symm.trans
    (natural_escape_centralizer_index h hnatural hE hs hg hnon)

/-- Construct the existing geometry interface from its remaining source
identities. The closure, product and action-index premises are discharged. -/
theorem natural_escape_geometry_of_pair
    (h : Hypothesis611 κ T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = 2)
    {g l : G} (hg : g ∈ Escape.I (T : Subgroup G) L V) (hl : l ∈ L)
    (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hmove : ¬ (layer L V).map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (layer L V : Set G))
    (hgen : Escape.L1 (T : Subgroup G) L V l = L ⊔ Escape.U (T : Subgroup G) L V)
    (hEE : Escape.E (T : Subgroup G) L V l ≤ centralizer (Escape.E (T : Subgroup G) L V l : Set G))
    (hcore : Escape.R (T : Subgroup G) L V l =
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) ⊔
        ((Escape.U (T : Subgroup G) L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓
          centralizer (layer L V : Set G)))
    (hcentral : ⁅Escape.L1 (T : Subgroup G) L V l, Escape.E (T : Subgroup G) L V l⁆ ≤ layer L V)
    (hfixedR : ZS (T : Subgroup G) L V ⊓ centralizer
      ((layer L V).map (MulAut.conj (g * l)⁻¹).toMonoidHom : Set G) = ⊥)
    (hfixedL : (ZS (T : Subgroup G) L V).map (MulAut.conj l⁻¹).toMonoidHom ⊓ centralizer
      ((layer L V).map (MulAut.conj g⁻¹).toMonoidHom : Set G) = ⊥)
    (hsection : Escape.IsNaturalSectionFour (Escape.L1 (T : Subgroup G) L V l)
      (Escape.R (T : Subgroup G) L V l) (Escape.E (T : Subgroup G) L V l))
    (hindex : (Escape.E (T : Subgroup G) L V l).relIndex
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 4) :
    Nonempty (NaturalEscape.Geometry (T : Subgroup G) L V) := by
  obtain ⟨hprod,hidx,hconj⟩ := natural_escape_pair_product h hnatural hE hs
    ((Escape.I (T : Subgroup G) L V).inv_mem hg) hmove
  exact ⟨{
    g := g
    l := l
    g_mem := hg
    l_mem := hl
    l_out := hlout
    generated := hgen
    intersection_commutes := hEE
    U_le_T := natural_escape_U_le_sylow h hnatural
    core := hcore
    product := hprod
    central := hcentral
    line_card := (hnatural.sylow_intersection_geometry T h.sylow_normalizes_L).1
    conjugate_index := hconj
    fixed_right := hfixedR
    fixed_left := hfixedL
    natural_section := hsection
    centralizer_index := hindex
    U_index := hidx
    commutator := natural_escape_commutator h hnatural }⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
