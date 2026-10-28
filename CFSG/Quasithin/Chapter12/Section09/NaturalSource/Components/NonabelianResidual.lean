module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianAmbient
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Residual motion in the original ambient parabolic

Let P₀ be the full original preimage of the dotted plane-point centralizer,
R = O²(P₀), and J = [Z(U),R]. The dotted action fixes V₂ modulo Z(U),
so [V₂Z(U),R] lies in Z(U). Two-perfect commutator idempotence identifies
this displacement with J. The original Sylow supplements R in P₀, hence
P₀ preserves V₂J. Its proved escape from N_G(V₂) makes this extension
strict, and the fully moved two-group J has at least four elements.

For the returning center D = Z(U)^g, the actual equality
C_{Z(U)}(D) = Z(I₂)V₁ also shows that I₂ preserves V₂C_I(D) and fixes
its quotient by V₂. This uses neither C_I(D) = [I,D] nor centralization
of C_I(D) by I₂. The final application retains the same original natural
constituent I and the guarded module theorem of 12.2.2.

The comparison of J with I, the fixed-space argument and the final ambient
contradiction remain source obligations, as do catalogue exhaustion and
LocalControlInput. The residual here is O²(P₀), not O₂(P₀).

Source: Aschbacher--Smith, proof of 12.9.4, printed p.860 of
refs/quasithin.pdf, using the literal 12.8.10 center intersections.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The literal embedded two-residual O²(P₀). -/
@[expose] def planePointResidual (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) : Subgroup G :=
  (pResidual 2 (planePointPreimage F v)).map (planePointPreimage F v).subtype

/-- The original center displaced by the full preimage’s two-residual. -/
@[expose] def planeCenterDisplacement (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) : Subgroup G :=
  ⁅F.ZU,planePointResidual F v⁆

omit [Finite G] in
private theorem center_normalized (F : InvariantFlag T V n) :
    F.H ≤ normalizer (F.ZU : Set G) :=
  (le_normalizer_conjugateSpanBy V F.H).trans
    (normalizer_le_normalizer_characteristic_image F.U (center F.U))

omit [Finite G] in
/-- The full preimage fixes the original plane modulo Z(U). -/
theorem planePointPreimage_plane_commutator
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ⁅F.Vi 2,planePointPreimage F v⁆ ≤ F.ZU := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha w hw
  obtain ⟨a,ha,rfl⟩ := ha
  let u : F.U := ⟨w,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) hw⟩
  have hu : hatElement F u ∈ Submodule.span (ZMod 2) {v} :=
    hline ▸ show hatElement F u ∈ hatSpace F (F.Vi 2) from ⟨u,hw,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
  have he : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
      (hatElement F u) = hatElement F u := by rw [←hc,map_smul,ha]
  have he' := congrArg Additive.toMul he
  rw [F.terminalRepresentation_apply_mk] at he'
  change F.terminalHatAction a (QuotientGroup.mk' (center F.U) u) =
    QuotientGroup.mk' (center F.U) u at he'
  rw [F.terminalHatAction_apply_mk] at he'
  refine ⟨F.uAction a u / u,QuotientGroup.eq_iff_div_mem.mp he',?_⟩
  change (a:G) * w * (a:G)⁻¹ / w = ⁅(a:G),w⁆
  simp only [commutatorElement_def,div_eq_mul_inv]

/-- The full central extension has exactly the center's residual displacement. -/
theorem planePointResidual_displacement
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ⁅F.Vi 2 ⊔ F.ZU,planePointResidual F v⁆ = planeCenterDisplacement F v ∧
      ⁅F.Vi 2,planePointResidual F v⁆ ≤ planeCenterDisplacement F v ∧
      planeCenterDisplacement F v ≤ F.ZU ∧
      planePointPreimage F v ≤ normalizer (planeCenterDisplacement F v : Set G) := by
  let := h.chosen.elementary
  let P := planePointPreimage F v
  let R := planePointResidual F v
  let Q := F.Vi 2 ⊔ F.ZU
  have hRP : R ≤ P := map_subtype_le _
  have hPZ : P ≤ normalizer (F.ZU : Set G) :=
    (planePointPreimage_le_H F v).trans (center_normalized F)
  have hPR : P ≤ normalizer (R : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  have hQZ : ⁅Q,R⁆ ≤ F.ZU := by
    apply commutator_sup_le_of_relative_normal F.H (F.Vi 2) F.ZU R F.ZU
      (center_normalized F)
      (((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans F.U_le_H)
      ((map_subtype_le _).trans F.U_le_H)
    · exact (commutator_mono le_rfl hRP).trans (planePointPreimage_plane_commutator F v hline)
    · exact le_normalizer_iff_commutator_le_left.mp (hRP.trans hPZ)
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz F earlier.alternatives)
  have hQtwo : IsPGroup 2 Q := htwo.to_le
    (sup_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) (map_subtype_le _))
  have hid := commutator_isPPerfect_idempotent R Q
    (isPPerfect_embedded_pResidual 2 P) hQtwo
    (hRP.trans (planePointPreimage_normalizes_plane_center F v hline))
  have he : ⁅Q,R⁆ = ⁅F.ZU,R⁆ := le_antisymm
    (hid.symm.le.trans (commutator_mono hQZ le_rfl))
    (commutator_mono le_sup_right le_rfl)
  refine ⟨he,(commutator_mono le_sup_left le_rfl).trans he.le,
    le_normalizer_iff_commutator_le_left.mp (hRP.trans hPZ),?_⟩
  intro a ha
  change a ∈ normalizer ((⁅F.ZU,R⁆ : Subgroup G) : Set G)
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hPZ ha),
    mem_normalizer_iff_map_conj_eq.mp (hPR ha)]


/-- The residual and the original Sylow supplement the full ambient preimage. -/
theorem planePointResidual_sup_sylow
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    planePointResidual F v ⊔ (T : Subgroup G) = planePointPreimage F v := by
  have ht : (T : Subgroup G) ≤ planePointPreimage F v :=
    le_sup_right.trans (planePointPreimage_contains_sylow_residual (L := ⊥) F v hv hline)
  have he := congrArg (map (planePointPreimage F v).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype ht))
  simpa only [planePointResidual,Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le ht,
    ←MonoidHom.range_eq_map,range_subtype] using he

omit [Finite G] in
private theorem normalizes_join_of_displacement (A J R : Subgroup G)
    (hRJ : R ≤ normalizer (J : Set G)) (hcomm : ⁅A,R⁆ ≤ J) :
    R ≤ normalizer ((A ⊔ J : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro r hr x hx
  let f := (MulAut.conj r).toMonoidHom
  have ha : A.map f ≤ A ⊔ J := by
    rintro _ ⟨a,ha,rfl⟩
    have hc : ⁅r,a⁆ ∈ J := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator hr ha)
    have hm := (A ⊔ J).mul_mem (mem_sup_right hc) (mem_sup_left ha)
    simpa only [f,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hm
  have hj : J.map f ≤ J := (mem_normalizer_iff_map_conj_eq.mp (hRJ hr)).le
  have hm : (A ⊔ J).map f ≤ A ⊔ J := by
    rw [Subgroup.map_sup]
    exact sup_le ha (hj.trans le_sup_right)
  exact hm (mem_map_of_mem f hx)

/-- The canonical residual displacement gives an actual P₀-invariant plane extension. -/
theorem planePointPreimage_normalizes_residual_extension
    {K : GroupClass.{u}} (h : HigherRankHypothesis K T L V n)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    planePointPreimage F v ≤ normalizer
      ((F.Vi 2 ⊔ planeCenterDisplacement F v : Subgroup G) : Set G) ∧
    conjugateSpanBy (F.Vi 2) (planePointPreimage F v) ≤
      F.Vi 2 ⊔ planeCenterDisplacement F v := by
  obtain ⟨_,hc,_,hn⟩ := planePointResidual_displacement h earlier F v hline
  have ht : (T : Subgroup G) ≤ planePointPreimage F v :=
    le_sup_right.trans (planePointPreimage_contains_sylow_residual (L := L) F v hv hline)
  have hp : planePointPreimage F v ≤ normalizer
      ((F.Vi 2 ⊔ planeCenterDisplacement F v : Subgroup G) : Set G) := by
    rw [←planePointResidual_sup_sylow F v hv hline]
    apply sup_le
    · exact normalizes_join_of_displacement _ _ _ ((map_subtype_le _).trans hn) hc
    · exact (le_inf (F.invariant 2) (ht.trans hn)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  exact ⟨hp,conjugateSpanBy_le le_sup_left hp⟩

/-- The original ambient escape forces nontrivial residual motion of the plane,
and the center displacement strictly enlarges it. -/
theorem nonabelian_caseFive_residual_moves_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ¬ ⁅F.Vi 2,planePointResidual F v⁆ ≤ F.Vi 2 ∧
      ¬ planeCenterDisplacement F v ≤ F.Vi 2 ∧
      F.Vi 2 < F.Vi 2 ⊔ planeCenterDisplacement F v := by
  have hout := nonabelian_caseFive_planePointPreimage_not_le_plane
    h hn earlier F hne g hgP hgH B h5 v hv hline
  have hm : ¬ ⁅F.Vi 2,planePointResidual F v⁆ ≤ F.Vi 2 := by
    intro hc
    apply hout
    rw [←planePointResidual_sup_sylow F v hv hline]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr hc) (F.invariant 2)
  have hj : ¬ planeCenterDisplacement F v ≤ F.Vi 2 := fun hj => hm
    ((planePointResidual_displacement h earlier F v hline).2.1.trans hj)
  exact ⟨hm,hj,lt_iff_le_not_ge.mpr ⟨le_sup_left,fun hh => hj (le_sup_right.trans hh)⟩⟩

/-- The actual residual displacement is fully moved and has at least four elements. -/
theorem nonabelian_caseFive_residual_displacement_size
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ⁅planeCenterDisplacement F v,planePointResidual F v⁆ = planeCenterDisplacement F v ∧
      4 ≤ Nat.card (planeCenterDisplacement F v) := by
  let J := planeCenterDisplacement F v
  let R := planePointResidual F v
  obtain ⟨he,_,hJZ,hPJ⟩ := planePointResidual_displacement h earlier F v hline
  let := h.chosen.elementary
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.point_mem_Hz F earlier.alternatives)
  have hZtwo : IsPGroup 2 F.ZU := htwo.to_le (map_subtype_le _)
  have hid : ⁅J,R⁆ = J := commutator_isPPerfect_idempotent R F.ZU
    (isPPerfect_embedded_pResidual 2 (planePointPreimage F v)) hZtwo
    ((map_subtype_le _).trans ((planePointPreimage_le_H F v).trans (center_normalized F)))
  have hnot := (nonabelian_caseFive_residual_moves_plane
    h hn earlier F hne g hgP hgH B h5 v hv hline).2.1
  change ¬ J ≤ F.Vi 2 at hnot
  have hJne : J ≠ ⊥ := fun hz => hnot (hz ▸ bot_le)
  have hcard2 : Nat.card J ≠ 2 := by
    intro hj
    have hc : R ≤ centralizer (J : Set G) :=
      ((map_subtype_le _).trans hPJ).trans (normalizer_le_centralizer_of_card_two J hj)
    exact hJne (hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
  obtain ⟨k,hk⟩ := (hZtwo.to_le hJZ).exists_card_eq
  change Nat.card J = 2 ^ k at hk
  have hlo : 1 < Nat.card J := (one_lt_card_iff_ne_bot J).mpr hJne
  have hk2 : 2 ≤ k := by
    by_contra! hh
    have hk01 : k = 0 ∨ k = 1 := by omega
    rcases hk01 with rfl | rfl
    · exact (Nat.ne_of_gt hlo) (by simpa only [pow_zero] using hk)
    · exact hcard2 (by simpa only [pow_one] using hk)
  refine ⟨hid,?_⟩
  change 4 ≤ Nat.card J
  rw [hk]
  exact Nat.pow_le_pow_right (by decide : 1 ≤ 2) hk2

/-- The returning fixed subgroup, even without identifying it with the
commutator, gives an I₂-invariant extension of V₂. I₂ fixes its quotient by
V₂; centralization of the fixed subgroup itself is not asserted. -/
theorem nonabelian_caseFive_returning_fixed_extension
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    {I : Subgroup G} (hiZ : I ≤ F.ZU) :
    ⁅F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)),F.I₂ L⁆ ≤ F.Vi 2 ∧
      F.I₂ L ≤ normalizer
        ((F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)) : Subgroup G) : Set G) := by
  let := h.chosen.elementary
  have hUU := (F.localKernel_commutator_squares h.source.simpleQTKE L _
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape F earlier.alternatives)).1
  have hUG : F.U ≤ F.Gi 2 := F.U_le_G₂_of_commutator hUU
  have hIG : F.I₂ L ≤ F.Gi 2 :=
    conjugateSpanBy_le hUG
      ((F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes).trans
        (F.Gi 2).le_normalizer)
  have hV2G : F.Vi 2 ≤ F.Gi 2 := (F.Vi 2).le_normalizer
  have hpointG : F.Vi 1 ≤ F.Gi 2 := (F.monotone (by omega : 1 ≤ 2)).trans hV2G
  have hZG : Section08.centerIn (F.I₂ L) ≤ F.Gi 2 := (map_subtype_le _).trans hIG
  have hVC : ⁅F.Vi 2,F.I₂ L⁆ ≤ F.Vi 2 := le_normalizer_iff_commutator_le_left.mp hIG
  have hfixed : I ⊓ centralizer (conjugate F.ZU g : Set G) ≤
      Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 := by
    rw [←(nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1,
      ←nonabelian_caseFive_center_centralizer h hn earlier F hne g hgP hgH B h5]
    exact inf_le_inf_right _ hiZ
  have hFC : ⁅I ⊓ centralizer (conjugate F.ZU g : Set G),F.I₂ L⁆ ≤ F.Vi 2 := by
    apply (commutator_mono hfixed le_rfl).trans
    apply commutator_sup_le_of_relative_normal (F.Gi 2) (Section08.centerIn (F.I₂ L))
      (F.Vi 1) (F.I₂ L) (F.Vi 2) le_rfl hZG hpointG
    · exact (commutator_eq_bot_iff_le_centralizer.mpr (centerIn_le_centralizer _)).le.trans bot_le
    · exact (commutator_mono (F.monotone (by omega : 1 ≤ 2)) le_rfl).trans hVC
  have hcomm : ⁅F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)),F.I₂ L⁆ ≤ F.Vi 2 := by
    apply commutator_sup_le_of_relative_normal (F.Gi 2) (F.Vi 2)
      (I ⊓ centralizer (conjugate F.ZU g : Set G)) (F.I₂ L) (F.Vi 2)
      le_rfl hV2G (hfixed.trans (sup_le hZG hpointG)) hVC hFC
  exact ⟨hcomm,le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_left)⟩

/-- Apply the residual construction to the same original flag, component and
natural constituent. No containment of the new displacement in I is assumed. -/
theorem nonabelian_caseFive_natural_residual_geometry
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (v : Additive F.Uhat) (C : ComponentGeometry F L) (I : Subgroup G)
      (c : ChosenModule T C.K1 I),
      v ≠ 0 ∧ hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧ Nat.card I = 16 ∧
      planePointPreimage F v ≤ normalizer (I : Set G) ∧
      Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4 ∧
      ⁅F.Vi 2 ⊔ F.ZU,planePointResidual F v⁆ = planeCenterDisplacement F v ∧
      ⁅F.Vi 2,planePointResidual F v⁆ ≤ planeCenterDisplacement F v ∧
      planeCenterDisplacement F v ≤ F.ZU ∧
      planePointPreimage F v ≤ normalizer (planeCenterDisplacement F v : Set G) ∧
      ⁅planeCenterDisplacement F v,planePointResidual F v⁆ = planeCenterDisplacement F v ∧
      4 ≤ Nat.card (planeCenterDisplacement F v) ∧
      F.Vi 2 < F.Vi 2 ⊔ planeCenterDisplacement F v ∧
      planePointPreimage F v ≤ normalizer
        ((F.Vi 2 ⊔ planeCenterDisplacement F v : Subgroup G) : Set G) ∧
      ⁅F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)),F.I₂ L⁆ ≤ F.Vi 2 ∧
      F.I₂ L ≤ normalizer
        ((F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨v,C,I,c,hv,hline,hi,hiZ,he,hcard,hfixed,_,_,hPI,_⟩ :=
    nonabelian_caseFive_ambient_parabolic_geometry modules h preferred earlier four
      F hne g hgP hgH B h5
  obtain ⟨hdisp,hplane,hZ,hPJ⟩ := planePointResidual_displacement h earlier F v hline
  obtain ⟨hmove,hsize⟩ := nonabelian_caseFive_residual_displacement_size h (.inl rfl)
    earlier F hne g hgP hgH B h5 v hv hline
  exact ⟨v,C,I,c,hv,hline,hi,hiZ,he,hcard,hPI,hfixed,hdisp,hplane,hZ,hPJ,hmove,hsize,
    (nonabelian_caseFive_residual_moves_plane h (.inl rfl) earlier F hne g hgP hgH B h5
      v hv hline).2.2,
    (planePointPreimage_normalizes_residual_extension h earlier F v hv hline).1,
    nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier F hne
      g hgP hgH B h5 hiZ⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
