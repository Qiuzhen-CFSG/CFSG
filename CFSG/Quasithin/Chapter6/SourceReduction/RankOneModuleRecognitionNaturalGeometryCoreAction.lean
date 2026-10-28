module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryStrict
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryAction

/-!
# The nontrivial elementary action of the escaping two-core

The natural layer has a proper nonzero Sylow-fixed line, so irreducibility
selects an actual element of L moving that line. For this conjugator the
literal quotient R/E is elementary. Since E lies in U and [U,U] lies in
Z_S, E fixes U/Z_S. Thus the original R-action on U/Z_S is elementary.

If that action were trivial, conjugating the commutator bound would make
C_U(V_L) normal in L₁ = LU. Its two prescribed conjugates would then
coincide, forcing R ≤ E, contrary to the strictness theorem. Hence the
actual core image is nontrivial, as needed before selecting the component
in 6.1.24. The Chapter 12 application also supplies the trivial two-core
and proper local subgroup of the same I-action image.

The initial natural action, escaping nonabelianness, parameter reduction
and prime component still belong to qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.21–24, printed pp.675–677.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- Irreducibility selects a conjugator outside the central-line normalizer. -/
theorem natural_escape_exists_line_mover
    {κ : GroupClass} (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n) :
    ∃ l ∈ L, l ∉ Escape.H (T : Subgroup G) L V := by
  apply SetLike.not_le_iff_exists.mp
  intro hLH
  have he := (hnatural.invariant_subgroup (ZS (T : Subgroup G) L V)
    inf_le_left hLH).resolve_left h.ZS_ne_bot
  exact (natural_escape_invariant_interval h hnatural).1 he

private theorem action_eq_one_of_commutators
    {κ : GroupClass} (h : Hypothesis611 κ T L M V n)
    (i : Escape.I (T : Subgroup G) L V)
    (hc : ∀ u ∈ Escape.U (T : Subgroup G) L V,
      i.val * u * i.val⁻¹ * u⁻¹ ∈ ZS (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    NaturalEscape.action (T : Subgroup G) L V i = 1 := by
  let := h.ZS_normal_in_escape_U
  ext x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective
    ((ZS (T : Subgroup G) L V).subgroupOf (Escape.U (T : Subgroup G) L V)) x
  rw [NaturalEscape.action_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (i.val * u.val * i.val⁻¹) / u.val ∈ ZS (T : Subgroup G) L V
  simpa only [div_eq_mul_inv] using hc u u.property

/-- The literal R-action factors through its elementary quotient R/E. -/
theorem natural_escape_core_action_elementary
    {κ : GroupClass} (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    IsElementaryAbelian 2
      (((Escape.R (T : Subgroup G) L V l).subgroupOf (Escape.I (T : Subgroup G) L V)).map
        (NaturalEscape.action (T : Subgroup G) L V)) := by
  let := h.ZS_normal_in_escape_U
  let D := naturalEscapeSetup (T : Subgroup G) L V
  let R := Escape.R (T : Subgroup G) L V l
  let E := Escape.E (T : Subgroup G) L V l
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨hU,_,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
  have hf := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hn : (E.subgroupOf R).Normal := by
    have hh := d.quotientIntersection_normal hut hf
    rwa [hR,hE'] at hh
  let := hn
  let : IsElementaryAbelian 2 (R ⧸ E.subgroupOf R) := by
    let := d.quotientIntersection_normal hut hf
    let := d.quotient_elementary_of_source hut hf
    exact IsElementaryAbelian.of_surjective
      (QuotientGroup.equivQuotientSubgroupOfOfEq hE' hR).toMonoidHom
      (QuotientGroup.equivQuotientSubgroupOfOfEq hE' hR).surjective
  have hcore := (natural_escape_core_geometry h hnatural hE hNS hnon hl hlout).2.1
  have hRI : R ≤ I := (hcore.le.trans (sup_le inf_le_right inf_le_right)).trans
    (centralizer_le (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left))
  let f : R →* MulAut (NaturalEscape.Quotient (T : Subgroup G) L V) :=
    a.comp (inclusion hRI)
  have hk : E.subgroupOf R ≤ f.rangeRestrict.ker := by
    intro e he
    apply Subtype.ext
    exact action_eq_one_of_commutators h (inclusion hRI e) (fun u hu =>
      natural_escape_commutator h hnatural
        (commutator_mem_commutator (show (e : G) ∈ Escape.U (T : Subgroup G) L V from he.1) hu))
  let fq := QuotientGroup.lift (E.subgroupOf R) f.rangeRestrict hk
  have hsur : Function.Surjective fq := by
    intro y
    obtain ⟨r,hr⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' (E.subgroupOf R) r,hr⟩
  have helem := IsElementaryAbelian.of_surjective fq hsur (p := 2)
  have hrange : f.range = (R.subgroupOf I).map a := by
    rw [MonoidHom.range_comp,inclusion_range]
  exact hrange ▸ helem

/-- The two-core acts nontrivially on the literal U/Z_S. This is the
nontrivial R* input preceding the component selection in source 6.1.24. -/
theorem natural_escape_core_action_nontrivial
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = n)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    ((Escape.R (T : Subgroup G) L V l).subgroupOf (Escape.I (T : Subgroup G) L V)).map
      (NaturalEscape.action (T : Subgroup G) L V) ≠ ⊥ := by
  let := h.ZS_normal_in_escape_U
  let U := Escape.U (T : Subgroup G) L V
  let R := Escape.R (T : Subgroup G) L V l
  let E := Escape.E (T : Subgroup G) L V l
  let Z := ZS (T : Subgroup G) L V
  let J := Escape.L1 (T : Subgroup G) L V l
  let I := Escape.I (T : Subgroup G) L V
  let W := U ⊓ centralizer (layer L V : Set G)
  let Ul := U.map (MulAut.conj l⁻¹).toMonoidHom
  let Wl := W.map (MulAut.conj l⁻¹).toMonoidHom
  have hlt := natural_escape_intersection_lt_core h hnatural hE hs hNS hnon hI hl hlout
  obtain ⟨hgen,hcore,_,_,hnorm⟩ := natural_escape_core_geometry h hnatural hE hNS hnon hl hlout
  have hRC : R ≤ centralizer (layer L V : Set G) :=
    hcore.le.trans (sup_le inf_le_right inf_le_right)
  have hRI : R ≤ I := hRC.trans (centralizer_le (show Z ≤ layer L V from inf_le_left))
  have hRW : R = W ⊔ Wl := by
    have hB : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right V L (L.inv_mem hl))
    change R = W ⊔ (U ⊓ centralizer (layer L V : Set G)).map (MulAut.conj l⁻¹).toMonoidHom
    rw [map_inf _ _ _ (MulAut.conj l⁻¹).injective,Theory.Quasithin.map_centralizer,hB]
    exact hcore
  have hRl : R.map (MulAut.conj l⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hnorm (mem_sup_left (L.inv_mem hl)))
  have hWN : U ≤ normalizer (W : Set G) :=
    (le_inf U.le_normalizer (((natural_escape_U_le_sylow h hnatural).trans
      h.sylow_normalizes_layer).trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hEW : E ≤ W := le_inf inf_le_left (hlt.le.trans hRC)
  intro hzero
  have hcomm : ⁅U,R⁆ ≤ Z := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro r hr u hu
    have hrker : NaturalEscape.action (T : Subgroup G) L V (⟨r,hRI hr⟩ : I) = 1 := by
      apply mem_bot.mp
      rw [←hzero]
      exact mem_map_of_mem _ hr
    have hh := congrArg (fun f : MulAut (NaturalEscape.Quotient (T : Subgroup G) L V) =>
      f (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,hu⟩)) hrker
    rw [NaturalEscape.action_mk] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change (r * u * r⁻¹) / u ∈ Z at hz
    simpa only [div_eq_mul_inv,commutatorElement_def] using hz
  have hUlR : ⁅Ul,R⁆ ≤ E := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hcomm
    rw [map_commutator,hRl] at hh
    apply hh.trans
    have hB : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right V L (L.inv_mem hl))
    have hEB : layer L V ≤ E := by
      have hBU : layer L V ≤ U := Escape.layer_le_U _ _ _
      exact le_inf hBU (by rw [←hB]; exact map_mono hBU)
    exact ((map_mono (show Z ≤ layer L V from inf_le_left)).trans_eq hB).trans hEB
  have hWR : W ≤ R := by rw [hRW]; exact le_sup_left
  have hUlW : Ul ≤ normalizer (W : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr
      ((commutator_mono le_rfl hWR).trans (hUlR.trans hEW))
  have hJN : J ≤ normalizer (W : Set G) := sup_le hWN hUlW
  have hlJ : l ∈ J := by change l ∈ Escape.L1 (T : Subgroup G) L V l; rw [hgen]; exact mem_sup_left hl
  have hWl : Wl = W := mem_normalizer_iff_map_conj_eq.mp (hJN (J.inv_mem hlJ))
  have hRE : R ≤ E := by
    rw [hRW,hWl,sup_idem]
    exact le_inf inf_le_left (by rw [←hWl]; exact map_mono inf_le_left)
  exact hlt.not_ge hRE

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
