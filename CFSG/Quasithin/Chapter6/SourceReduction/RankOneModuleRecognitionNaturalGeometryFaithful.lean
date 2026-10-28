module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryKernel
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.UniqueLocalResidualKernel
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# The faithful escaping action and its moved components

The kernel of I acting on U/Z_S is exactly O₂(I). To prove the reverse
containment, its two-residual centralizes the natural layer and is normalized
by both I and LT; uniqueness of the maximal two-local over LT kills it.
The resulting isomorphism I/O₂(I) ≃ I* lifts actual components with their
marked action images and quasisimple two-core quotients intact.

A Frattini argument shows that the whole natural-layer normalizer preserves
the escaping two-core R. Hence a component moved by R* escapes M and its
image in I*: containment would put a nontrivial perfect component in R*.
The conditional selection theorem requires the Fitting-centralization input
of 6.1.24(3). That input and the later PSL₂ identification remain with
qt-d-1222-rankone-recognition-natural; this is not unconditional 6.1.27.

Source: Aschbacher–Smith, 6.1.21(1,5), 6.1.24 and the paragraph preceding
6.1.25, printed pp.675–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

private theorem escape_kernel_commutatorPreimage
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n) :
    letI := h.ZS_normal_in_escape_U
    (NaturalEscape.action (T : Subgroup G) L V).ker =
      (commutatorPreimage (Escape.I (T : Subgroup G) L V)
        (Escape.U (T : Subgroup G) L V) (ZS (T : Subgroup G) L V)).subgroupOf
          (Escape.I (T : Subgroup G) L V) := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let U := Escape.U (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  have hIZ : I ≤ normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  ext i
  change a i = 1 ↔ (i : G) ∈ commutatorPreimage I U Z
  rw [mem_commutatorPreimage_iff I U Z hIZ]
  constructor
  · intro hi
    refine ⟨i.property, ?_⟩
    intro u hu
    have hh := congrArg (fun f : MulAut (NaturalEscape.Quotient (T : Subgroup G) L V) =>
      f (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,hu⟩)) hi
    rw [NaturalEscape.action_mk] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change (i : G) * u * (i : G)⁻¹ / u ∈ Z at hz
    simpa only [div_eq_mul_inv,commutatorElement_def] using hz
  · rintro ⟨_, hc⟩
    ext u
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) u
    rw [NaturalEscape.action_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (i : G) * (u : G) * (i : G)⁻¹ / (u : G) ∈ Z
    simpa only [div_eq_mul_inv,commutatorElement_def] using hc u u.property

/-- In the escaping branch, the literal action kernel is exactly O₂(I). -/
theorem natural_escape_action_kernel_eq_twoCore
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M) :
    letI := h.ZS_normal_in_escape_U
    (NaturalEscape.action (T : Subgroup G) L V).ker =
      pCore 2 (Escape.I (T : Subgroup G) L V) := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let U := Escape.U (T : Subgroup G) L V
  let Z := ZS (T : Subgroup G) L V
  let B := layer L V
  let K := commutatorPreimage I U Z
  let Y := (pResidual 2 K).map K.subtype
  have hIZ : I ≤ normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hKH : K ≤ I := commutatorPreimage_le I U Z
  have hIK : I ≤ normalizer (K : Set G) := commutatorPreimage_normalized I U Z I hIZ
    I.le_normalizer (NaturalEscape.I_normalizes_U _ _ _) hIZ
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized I U Z T hIZ
      (h.sylow_normalizes_ZS.trans (normalizer_le_normalizer_centralizer Z))
      (h.sylow_normalizes_ZS.trans (natural_escape_normalizer_normalizes_U h hE hNS))
      h.sylow_normalizes_ZS
  have hKB : ⁅K,B⁆ ≤ Z := (commutator_mono le_rfl (Escape.layer_le_U _ _ _)).trans
    (commutator_commutatorPreimage_le I U Z hIZ)
  have hYC : Y ≤ centralizer (B : Set G) := residual_centralizes_of_two_layer K B Z
    (T.isPGroup'.to_le h.ZS_le_T) hKH hKB
  have hYK : Y ≤ K := map_subtype_le _
  have hIY : I ≤ normalizer (Y : Set G) := hIK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hTK.trans
    (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
  have hNL : normalizer (B : Set G) ≤ normalizer (L : Set G) :=
    hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  have hLN : L ≤ normalizer (B : Set G) := normalizer_commutator_ge_right V L
  have hLC : ⁅L, centralizer (B : Set G)⁆ ≤ L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) (natural_centralizer_eq_core hnatural).le
    · exact le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.centralizer_le_normalizer _).trans hNL)
    · exact le_normalizer_iff_commutator_le_right.mp
        (hLN.trans (normalizer_le_normalizer_centralizer B))
  have hLQ : L ≤ normalizer (L.pCoreIn 2 : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hQI : L.pCoreIn 2 ≤ I :=
    ((natural_centralizer_eq_core hnatural).ge.trans inf_le_right).trans
      (centralizer_le (show Z ≤ B from inf_le_left))
  have hLY : L ≤ normalizer (Y : Set G) := normalizes_residual_of_commutator_le_two
    L I K (L.pCoreIn 2) hIK hQI (isPGroup_pCoreIn 2 L) hLQ
      ((commutator_mono le_rfl hYC).trans hLC)
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro J hJ hLJ
    exact le_antisymm (h.local_mem.1.2 hJ hLJ) hLJ
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl h.sylow_normalizes_L)
      (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hLN
    have h1 := hu.normalizer_unique N hN
    have h2 := hu.normalizer_unique M h.maximal
    rw [horbit] at h1 h2
    exact (h1 hLN).trans (h2 (sup_le h.L_le h.sylow_le)).symm
  have hYbot : Y = ⊥ := normal_eq_bot_of_unique_core (L ⊔ (T : Subgroup G)) I M Y
    huniq hI h.ZS_centralizer_mem_He (hYK.trans hKH) hIY (sup_le hLY hTY)
  have hres : pResidual 2 K = ⊥ :=
    (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hYbot
  have hp : IsPGroup 2 K := (isPGroup_quotient_pResidual (G := K) 2).of_injective
    (QuotientGroup.mk' (pResidual 2 K)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [QuotientGroup.ker_mk', hres])
  have hKcore : K ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes hp hKH hIK
  have hcoreK : I.pCoreIn 2 ≤ K := le_commutatorPreimage (pCoreIn_le 2 I) (by
    rw [commutator_comm]
    exact (natural_escape_core h hnatural).2)
  rw [escape_kernel_commutatorPreimage h]
  change K.subgroupOf I = pCore 2 I
  rw [le_antisymm hKcore hcoreK]
  exact (pCore 2 I).comap_map_eq_self_of_injective I.subtype_injective

/-- The actual action quotient, with the denominator identified as O₂(I). -/
@[expose] def naturalEscapeActionEquiv
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M) :
    letI := h.ZS_normal_in_escape_U
    (Escape.I (T : Subgroup G) L V ⧸ pCore 2 (Escape.I (T : Subgroup G) L V)) ≃*
      (NaturalEscape.action (T : Subgroup G) L V).range := by
  let := h.ZS_normal_in_escape_U
  exact (QuotientGroup.quotientMulEquivOfEq
    (natural_escape_action_kernel_eq_twoCore h hnatural hE hNS hI).symm).trans
      (QuotientGroup.quotientKerEquivRange (NaturalEscape.action (T : Subgroup G) L V))

@[simp] theorem naturalEscapeActionEquiv_mk
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    (i : Escape.I (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    naturalEscapeActionEquiv h hnatural hE hNS hI
      (QuotientGroup.mk' (pCore 2 (Escape.I (T : Subgroup G) L V)) i) =
        (NaturalEscape.action (T : Subgroup G) L V).rangeRestrict i := rfl

/-- Lift an actual component of I* without changing its marked action image. -/
theorem natural_escape_action_component_lift
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M) :
    letI := h.ZS_normal_in_escape_U
    ∀ J : Subgroup (NaturalEscape.action (T : Subgroup G) L V).range,
      IsComponent _ J → ∃ K : Subgroup (Escape.I (T : Subgroup G) L V),
        K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
          K.map (NaturalEscape.action (T : Subgroup G) L V).rangeRestrict = J := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  let e := naturalEscapeActionEquiv h hnatural hE hNS hI
  let q := QuotientGroup.mk' (pCore 2 I)
  intro J hJ
  have hJq := hJ.map_equiv e.symm
  let : Group.IsNilpotent (pCore 2 I) := pCore_isNilpotent
  obtain ⟨K,hK,hmap⟩ := hJq.isCComponent.exists_map_quotient_eq (pCore 2 I)
  have hKq : IsComponent (I ⧸ pCore 2 I) (K.map q) := hmap.symm ▸ hJq
  let := hKq.2
  have hquasi : IsQuasisimple (K ⧸ pCore 2 K) :=
    IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK).symm
  refine ⟨K,hK,hquasi,?_⟩
  have he : e.toMonoidHom.comp q = a.rangeRestrict := by ext i; rfl
  rw [←he,←map_map,hmap,map_map]
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id a.range := by
    apply MonoidHom.ext
    intro x
    exact e.apply_symm_apply x
  rw [hid,Subgroup.map_id]


/-- The whole normalizer of the natural layer normalizes L₁ and its two-core.
This is the full M_V-normality assertion in 6.1.21(1,5). -/
theorem natural_escape_layer_normalizer_normalizes_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    normalizer (layer L V : Set G) ≤ normalizer (Escape.R (T : Subgroup G) L V l : Set G) := by
  let B := layer L V
  let N := normalizer (B : Set G)
  let U := Escape.U (T : Subgroup G) L V
  let J := Escape.L1 (T : Subgroup G) L V l
  have hLN : L ≤ N := normalizer_commutator_ge_right V L
  have hNL : N ≤ normalizer (L : Set G) :=
    hE.normalizer_le.trans ((normal_subgroupOf_iff_le_normalizer h.L_le).mp h.L_normal)
  let L' := L.subgroupOf N
  let : L'.Normal := normal_subgroupOf_of_le_normalizer hNL
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L h.sylow_normalizes_L
  let e : L ≃* L' := (subgroupOfEquivOfLe hLN).symm
  let P' : Sylow 2 L' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hpmap : ((P' : Subgroup L').map L'.subtype).map N.subtype = (T : Subgroup G) ⊓ L := by
    change (((P : Subgroup L).map e.toMonoidHom).map L'.subtype).map N.subtype = _
    rw [map_map,map_map]
    change (P : Subgroup L).map L.subtype = _
    rw [hP,subgroupOf_map_subtype]
  have hfr := congrArg (Subgroup.map N.subtype) P'.normalizer_sup_eq_top
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLN,←MonoidHom.range_eq_map,range_subtype] at hfr
  have hgen := (natural_escape_core_geometry h hnatural hE hNS hnon hl hlout).1
  have hLJ : L ≤ J := by
    change L ≤ Escape.L1 (T : Subgroup G) L V l
    rw [hgen]
    exact le_sup_left
  have hJJ : L ≤ normalizer (J : Set G) := hLJ.trans J.le_normalizer
  have hNJ : N ≤ normalizer (J : Set G) := by
    rw [←hfr]
    apply sup_le ?_ hJJ
    rintro x ⟨m,hm,rfl⟩
    have hmTL := ((P' : Subgroup L').map L'.subtype).le_normalizer_map N.subtype
      (mem_map_of_mem N.subtype hm)
    rw [hpmap] at hmTL
    have hmZ : (m : G) ∈ normalizer (ZS (T : Subgroup G) L V : Set G) :=
      inf_normalizer_le_normalizer_inf
        ⟨m.property, (normalizer_le_normalizer_centralizer ((T : Subgroup G) ⊓ L)) hmTL⟩
    change (m : G) ∈ normalizer (Escape.L1 (T : Subgroup G) L V l : Set G)
    rw [hgen]
    exact (normalizer_inf_normalizer_le_normalizer_sup L U)
      ⟨hNL m.property, natural_escape_normalizer_normalizes_U h hE hNS hmZ⟩
  exact hNJ.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))

/-- The nontrivial core image selects and lifts a moved component once the
Fitting-centralization assertion of 6.1.24(3) has been proved. -/
theorem natural_escape_moved_component_of_fitting_centralization
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hF : letI := h.ZS_normal_in_escape_U
      let a := NaturalEscape.action (T : Subgroup G) L V
      let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf
        (Escape.I (T : Subgroup G) L V)).map a
      A.subgroupOf a.range ≤ centralizer (fittingSubgroup a.range : Set a.range)) :
    letI := h.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L V
    let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf
      (Escape.I (T : Subgroup G) L V)).map a
    ∃ K : Subgroup (Escape.I (T : Subgroup G) L V),
      K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
        IsComponent a.range (K.map a.rangeRestrict) ∧
          ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf I).map a
  have hA := natural_escape_core_action_elementary h hnatural hE hNS hnon hl hlout
  have hp : IsPGroup 2 (A.subgroupOf a.range) :=
    (hA.isPGroup).comap_subtype
  have hne : A.subgroupOf a.range ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map a.range.subtype) he
    rw [map_subgroupOf_eq_of_le (map_le_range a _),Subgroup.map_bot] at hh
    exact natural_escape_core_action_nontrivial h hnatural hE hs hNS hnon hI hl hlout hh
  obtain ⟨J,hJ,hm⟩ := exists_component_moved_of_centralizes_fitting 2
    (A.subgroupOf a.range) hp hne (natural_escape_action_twoCore_eq_bot h hnatural) hF
  obtain ⟨K,hK,hquasi,he⟩ := natural_escape_action_component_lift h hnatural hE hNS hI J hJ
  exact ⟨K,hK,hquasi,he.symm ▸ hJ,he.symm ▸ hm⟩

/-- A component moved by the core image cannot be contained in the original
local group. This uses full layer-normalizer control of the literal core. -/
theorem natural_escape_moved_component_not_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L V
    let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf
      (Escape.I (T : Subgroup G) L V)).map a
    ∀ K : Subgroup (Escape.I (T : Subgroup G) L V),
      IsComponent a.range (K.map a.rangeRestrict) →
      ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ →
      ¬ K.map (Escape.I (T : Subgroup G) L V).subtype ≤ M := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  let R := Escape.R (T : Subgroup G) L V l
  let A := (R.subgroupOf I).map a
  change ∀ K : Subgroup I, IsComponent a.range (K.map a.rangeRestrict) →
    ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ → ¬ K.map I.subtype ≤ M
  intro K hK hm hKM
  have hKN : K ≤ (normalizer (R : Set G)).comap I.subtype := by
    intro k hk
    exact natural_escape_layer_normalizer_normalizes_core h hnatural hE hNS hnon hl hlout
      (hE.localCentralizer_le_normalizer h.ZS_ne_bot inf_le_left
        ⟨hKM (mem_map_of_mem I.subtype hk),k.property⟩)
  have he : (R.subgroupOf I).map a.rangeRestrict = A.subgroupOf a.range := by
    ext z
    constructor
    · rintro ⟨i,hi,hi'⟩
      exact ⟨i,hi,congrArg Subtype.val hi'⟩
    · rintro ⟨i,hi,hi'⟩
      exact ⟨i,hi,Subtype.ext hi'⟩
  have hn : K.map a.rangeRestrict ≤ normalizer (A.subgroupOf a.range : Set a.range) := by
    rw [←he]
    exact (map_mono (hKN.trans (le_normalizer_comap _))).trans (le_normalizer_map _)
  have hh := (hK.commutator_dichotomy (A.subgroupOf a.range)).resolve_left hm
  have hle : K.map a.rangeRestrict ≤ A.subgroupOf a.range :=
    (le_iSup_conjugates _ _).trans (hh.symm.le.trans
      (le_normalizer_iff_commutator_le_right.mp hn))
  have hA := natural_escape_core_action_elementary h hnatural hE hNS hnon hl hlout
  have hp : IsPGroup 2 (K.map a.rangeRestrict) := hA.isPGroup.comap_subtype.to_le hle
  let : Group.IsNilpotent (K.map a.rangeRestrict) := hp.isNilpotent
  exact hK.isCComponent.not_isSolvable inferInstance

/-- The selected component also escapes the literal image of M in I*. -/
theorem natural_escape_moved_component_image_not_le
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    let a := NaturalEscape.action (T : Subgroup G) L V
    let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf
      (Escape.I (T : Subgroup G) L V)).map a
    ∀ K : Subgroup (Escape.I (T : Subgroup G) L V),
      IsComponent a.range (K.map a.rangeRestrict) →
      ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ →
      ¬ K.map a.rangeRestrict ≤
        (M.subgroupOf (Escape.I (T : Subgroup G) L V)).map a.rangeRestrict := by
  let := h.ZS_normal_in_escape_U
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  let A := ((Escape.R (T : Subgroup G) L V l).subgroupOf I).map a
  change ∀ K : Subgroup I, IsComponent a.range (K.map a.rangeRestrict) →
    ⁅K.map a.rangeRestrict, A.subgroupOf a.range⁆ ≠ ⊥ →
      ¬ K.map a.rangeRestrict ≤ (M.subgroupOf I).map a.rangeRestrict
  intro K hK hm hle
  apply natural_escape_moved_component_not_le h hnatural hE hNS hnon hl hlout K hK hm
  have hk : a.rangeRestrict.ker ≤ M.subgroupOf I := by
    intro i hi
    have hi' : i ∈ a.ker := congrArg Subtype.val hi
    exact hE.normalizer_le (natural_escape_action_kernel_normalizes_layer h
      (mem_map_of_mem I.subtype hi'))
  have hKM : K ≤ M.subgroupOf I := by
    have hh := map_le_iff_le_comap.mp hle
    rwa [comap_map_eq_self hk] at hh
  rintro _ ⟨k,hk,rfl⟩
  exact hKM hk

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
