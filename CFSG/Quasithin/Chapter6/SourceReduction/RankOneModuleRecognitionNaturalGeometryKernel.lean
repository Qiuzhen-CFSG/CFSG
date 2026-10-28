module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryCoreAction
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The exact kernel and order of the escaping core action

Put W = C_U(V_L). The conjugate product R = WWˡ identifies the fixed
subgroup of R/E under U with W/E. An element of the second factor fixed
modulo E by U is fixed by both generators of L₁, so conjugating back puts
it in W as well. This proves the fixed-subgroup identity without invoking
a natural-module classification for R/E.

An element of R fixing U/Z_S therefore lies in W, and every element of W
fixes that quotient because [U,U] ≤ Z_S. Thus the literal core-action
kernel is W. The conjugate index square and the subgroup index tower give
|R*| = |W:E|. In field four, positive natural multiplicity turns |R*| ≤ 4
into the exact marked index four consumed by the natural-section theorem.

The Chapter 12 extension applies these results on the whole reduced layer
and connects them to the terminal quotient bound and conditional 6.1.27.
Initial naturalness, escaping nonabelianness, parameter reduction, the
small core-image bound and the PSL₂ component remain obligations of
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.21(4), 6.1.24(1–2) and 6.1.25(3), pp.675–678.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G]

private theorem fixed_modulo_of_conjugate_product
    (U W E J R : Subgroup G) (g : G)
    (hgen : J = U ⊔ U.map (MulAut.conj g).toMonoidHom)
    (hg : g ∈ J) (hNE : J ≤ normalizer (E : Set G))
    (hWU : W ≤ U) (hEW : E ≤ W)
    (hcomm : ⁅U,U⁆ ≤ E)
    (hprod : (R : Set G) = (W : Set G) * (W.map (MulAut.conj g).toMonoidHom : Set G)) :
    R ⊓ commutatorPreimage J U E = W := by
  have hUJ : U ≤ J := hgen ▸ le_sup_left
  have hWJ := hWU.trans hUJ
  have hWK : W ≤ commutatorPreimage J U E :=
    le_commutatorPreimage hWJ ((commutator_mono hWU le_rfl).trans hcomm)
  have hWR : W ≤ R := by
    intro w hw
    change w ∈ (R : Set G)
    rw [hprod]
    simpa only [mul_one] using Set.mul_mem_mul hw (one_mem (W.map (MulAut.conj g).toMonoidHom))
  apply le_antisymm ?_ (le_inf hWR hWK)
  rintro x ⟨hx,hxf⟩
  change x ∈ (R : Set G) at hx
  rw [hprod] at hx
  obtain ⟨a,ha,b,hb,hab⟩ := hx
  have hbf : b ∈ commutatorPreimage J U E := by
    have hh := (commutatorPreimage J U E).mul_mem
      ((commutatorPreimage J U E).inv_mem (hWK ha)) hxf
    simpa only [←hab,inv_mul_cancel_left] using hh
  let Ug := U.map (MulAut.conj g).toMonoidHom
  have hUgJ : Ug ≤ J := hgen ▸ le_sup_right
  have hbUg : b ∈ Ug := map_mono hWU hb
  have hcommg : ⁅Ug,Ug⁆ ≤ E := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
    rw [map_commutator] at hh
    have he : E.map (MulAut.conj g).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp (hNE hg)
    exact hh.trans_eq he
  have hJK : J ≤ commutatorPreimage J (zpowers b) E := by
    apply hgen.le.trans
    refine sup_le (le_commutatorPreimage hUJ ?_)
      (le_commutatorPreimage hUgJ ?_)
    · rw [commutator_comm]
      exact (commutator_mono (zpowers_le.mpr hbf) le_rfl).trans
        (commutator_commutatorPreimage_le J U E hNE)
    · exact (commutator_mono le_rfl (zpowers_le.mpr hbUg)).trans hcommg
  have hbconj : (MulAut.conj g⁻¹) b ∈ W := by
    obtain ⟨b₀,hb₀,rfl⟩ := hb
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one, SetLike.mem_coe] using hb₀
  have hgi : ⁅g⁻¹,b⁆ ∈ E := commutator_commutatorPreimage_le J (zpowers b) E hNE
    (commutator_mem_commutator (hJK (J.inv_mem hg)) (mem_zpowers b))
  have hbW : b ∈ W := by
    have hh := W.mul_mem (W.inv_mem (hEW hgi)) hbconj
    convert hh using 1
    simp only [commutatorElement_def, MulAut.conj_apply]
    group
  rw [←hab]
  exact W.mul_mem ha hbW

open ChapterG.Section02.RankOneHigherFields

private theorem marked_core_fixed [Finite G]
    {D : ChapterG.Section02.Setup G} {F : Type*} [Field F] [Finite F]
    {n : ℕ} {l : G} (d : Hypothesis D F n l) (hut : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) :
    D.S l ⊓ commutatorPreimage (D.I l) D.U (D.S₂ l) = D.W l := by
  have hseries := d.series hut hf
  have hEW : D.S₂ l ≤ D.W l := le_inf inf_le_left hseries.2.1
  have hprod : (D.S l : Set G) = (D.W l : Set G) *
      ((D.W l).map (MulAut.conj l⁻¹).toMonoidHom : Set G) := by
    rw [d.S_eq_WProduct_of_source hut hf]
    exact d.WProduct_eq_product hut (d.star_I_eq_star_L hut hf).ge
  exact fixed_modulo_of_conjugate_product D.U (D.W l) (D.S₂ l) (D.I l) (D.S l) l⁻¹
    rfl ((D.I l).inv_mem (d.g_mem_I hut hf))
    (d.quotientIntersection_normalizes hut hf) inf_le_left hEW
    ((derived_le_of_frattini_image_le (d.U_isPGroup hut) hf).trans
      (d.setup.point_le.trans hseries.1)) hprod
variable [Finite G] {κ : GroupClass}
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The fixed subgroup of R/E under U is exactly C_U(V_L)/E.
This follows from the conjugate product, without module recognition. -/
theorem natural_escape_core_fixed_modulo_intersection
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    Escape.R (T : Subgroup G) L V l ⊓
      commutatorPreimage (Escape.L1 (T : Subgroup G) L V l)
        (Escape.U (T : Subgroup G) L V) (Escape.E (T : Subgroup G) L V l) =
      Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G) := by
  let D := naturalEscapeSetup (T : Subgroup G) L V
  obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
  obtain ⟨hU,hJ,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
  have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
  have hf := (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point
  have hW : D.W l = Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G) := by
    change D.U ⊓ D.S l = _
    rw [d.S_eq_star_kernel hut hf, ←inf_assoc,
      inf_eq_left.mpr (show D.U ≤ D.I l from le_sup_left)]
    change D.U ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 = _
    rw [←local_layer_centralizer_eq_core h hnatural, ←inf_assoc,
      inf_eq_left.mpr (show D.U ≤ L ⊔ (T : Subgroup G) from hut.trans le_sup_right), hU]
  have hh := marked_core_fixed d hut hf
  rwa [hR,hJ,hU,hE',hW] at hh

/-- Source 6.1.24(1): the kernel of the literal R-action on U/Z_S is C_U(V_L). -/
theorem natural_escape_core_action_kernel
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    (Escape.R (T : Subgroup G) L V l).subgroupOf (Escape.I (T : Subgroup G) L V) ⊓
      (NaturalEscape.action (T : Subgroup G) L V).ker =
    (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)).subgroupOf
      (Escape.I (T : Subgroup G) L V) := by
  let := h.ZS_normal_in_escape_U
  let U := Escape.U (T : Subgroup G) L V
  let R := Escape.R (T : Subgroup G) L V l
  let E := Escape.E (T : Subgroup G) L V l
  let J := Escape.L1 (T : Subgroup G) L V l
  let Z := ZS (T : Subgroup G) L V
  let W := U ⊓ centralizer (layer L V : Set G)
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  obtain ⟨_,hcore,_,hc,_⟩ := natural_escape_core_geometry h hnatural hE hNS hnon hl hlout
  have hWR : W ≤ R := le_sup_left.trans hcore.ge
  have hBE : layer L V ≤ E := by
    have hb : (layer L V).map (MulAut.conj l⁻¹).toMonoidHom = layer L V :=
      mem_normalizer_iff_map_conj_eq.mp (normalizer_commutator_ge_right V L (L.inv_mem hl))
    exact le_inf (Escape.layer_le_U _ _ _) (by
      rw [←hb]
      exact map_mono (Escape.layer_le_U _ _ _))
  have hZE : Z ≤ E := inf_le_left.trans hBE
  have hNE : J ≤ normalizer (E : Set G) :=
    le_normalizer_iff_commutator_le_right.mpr (hc.trans hBE)
  have hfixed : R ⊓ commutatorPreimage J U E = W :=
    natural_escape_core_fixed_modulo_intersection h hnatural hE hNS hnon hl hlout
  ext r
  constructor
  · rintro ⟨hr,hk⟩
    apply hfixed.le
    refine ⟨hr,(mem_commutatorPreimage_iff J U E hNE r).mpr
      ⟨pCoreIn_le 2 J hr,?_⟩⟩
    intro u hu
    have hh := congrArg (fun f : MulAut (NaturalEscape.Quotient (T : Subgroup G) L V) =>
      f (QuotientGroup.mk' (Z.subgroupOf U) ⟨u,hu⟩)) (MonoidHom.mem_ker.mp hk)
    rw [NaturalEscape.action_mk] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change ((r : G) * u * (r : G)⁻¹) / u ∈ Z at hz
    apply hZE
    simpa only [div_eq_mul_inv,commutatorElement_def] using hz
  · intro hr
    refine ⟨hWR hr,?_⟩
    apply MonoidHom.mem_ker.mpr
    ext x
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) x
    rw [NaturalEscape.action_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change ((r : G) * (u : G) * (r : G)⁻¹) / (u : G) ∈ Z
    simpa only [div_eq_mul_inv,commutatorElement_def, Subgroup.subtype_apply] using
      natural_escape_commutator h hnatural (commutator_mem_commutator hr.1 u.property)

/-- The order of R* is the marked index |C_U(V_L):E|, on the same quotient action. -/
theorem natural_escape_core_action_card
    (h : Hypothesis611 κ T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 κ T M (layer L V))
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V) :
    letI := h.ZS_normal_in_escape_U
    Nat.card (((Escape.R (T : Subgroup G) L V l).subgroupOf
      (Escape.I (T : Subgroup G) L V)).map (NaturalEscape.action (T : Subgroup G) L V)) =
      (Escape.E (T : Subgroup G) L V l).relIndex
        (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) := by
  let := h.ZS_normal_in_escape_U
  let U := Escape.U (T : Subgroup G) L V
  let R := Escape.R (T : Subgroup G) L V l
  let E := Escape.E (T : Subgroup G) L V l
  let W := U ⊓ centralizer (layer L V : Set G)
  let I := Escape.I (T : Subgroup G) L V
  let a := NaturalEscape.action (T : Subgroup G) L V
  have hcore := (natural_escape_core_geometry h hnatural hE hNS hnon hl hlout).2.1
  have hWR : W ≤ R := le_sup_left.trans hcore.ge
  have hRC : R ≤ centralizer (layer L V : Set G) :=
    hcore.le.trans (sup_le inf_le_right inf_le_right)
  have hRI : R ≤ I := hRC.trans (centralizer_le (show ZS (T : Subgroup G) L V ≤ layer L V from inf_le_left))
  have hER : E ≤ R := by
    let D := naturalEscapeSetup (T : Subgroup G) L V
    obtain ⟨F,_,_,⟨d⟩⟩ := natural_escape_G2_marking h hnatural hE hNS hnon hl hlout
    obtain ⟨hU,_,hR,hE'⟩ := natural_escape_G2_constructions h hE hNS l
    have hut : D.U ≤ D.T := by rw [hU]; exact natural_escape_U_le_sylow h hnatural
    have hh := (d.series hut (natural_escape_G2_hypothesis h hnatural).frattini_U_le_point).2.1
    rwa [hR,hE'] at hh
  have hEW : E ≤ W := le_inf inf_le_left (hER.trans hRC)
  have hcard : Nat.card ((R.subgroupOf I).map a) = W.relIndex R := by
    rw [←relIndex_ker,←inf_relIndex_left,
      natural_escape_core_action_kernel h hnatural hE hNS hnon hl hlout,
      relIndex_subgroupOf hRI]
  rw [hcard]
  have hsquare := natural_escape_core_index_square h hnatural hE hNS hnon hl hlout
  have htower := relIndex_mul_relIndex E W R hEW hWR
  have hpos : 0 < E.relIndex W := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [htower,←hsquare,pow_two]

/-- The source bound |R*| ≤ 4 forces multiplicity one in field four.
The marked index is derived from the actual quotient-action image. -/
theorem natural_escape_index_four_of_small_core_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V 2)
    (hnatural : IsNaturalModule L (layer L V) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L V) = 2)
    (hNS : normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L V : Set G) : Subgroup G) : Set G) ≤ M)
    (hnon : ¬ Escape.U (T : Subgroup G) L V ≤
      centralizer (Escape.U (T : Subgroup G) L V : Set G))
    (hI : ¬ Escape.I (T : Subgroup G) L V ≤ M)
    {l : G} (hl : l ∈ L) (hlout : l ∉ Escape.H (T : Subgroup G) L V)
    (hsmall : letI := h.ZS_normal_in_escape_U
      Nat.card (((Escape.R (T : Subgroup G) L V l).subgroupOf
        (Escape.I (T : Subgroup G) L V)).map (NaturalEscape.action (T : Subgroup G) L V)) ≤ 4) :
    (Escape.E (T : Subgroup G) L V l).relIndex
      (Escape.U (T : Subgroup G) L V ⊓ centralizer (layer L V : Set G)) = 4 := by
  let := h.ZS_normal_in_escape_U
  have hc := natural_escape_core_action_card h hnatural hE hNS hnon hl hlout
  obtain ⟨s,hpos,hi,_,_⟩ := natural_escape_four_positive_multiplicity
    h hnatural hE hs hNS hnon hI hl hlout
  have hlow : 4 ≤ 2 ^ (2 * s) := by
    change 2 ^ 2 ≤ 2 ^ (2 * s)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  rw [hi] at hc ⊢
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
