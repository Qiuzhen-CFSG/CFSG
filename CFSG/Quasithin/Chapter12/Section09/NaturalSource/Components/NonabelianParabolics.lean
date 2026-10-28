module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianFourGeometry
public import Theory.GroupTheory.PResidual.SylowCentralizer
public import Theory.GroupTheory.PResidual.Restriction
public import Theory.GroupTheory.IrreducibleFourResidual

/-!
# The literal plane-centralizer residual in 12.9.4

Put L₀ = O²(C_L(V₂)). The centralizer of V₂ lies in the point stabilizer,
so its residual lies in L₁ and equals O²(C_{L₁}(V₂)). In the nonabelian
flag, H ∩ G₂ = C_G(V₂)T. Residual monotonicity inside LT and H ∩ G₂
then gives L₀T = L₁T ∩ G₂. For degree four this is precisely the
opposite end-node ordered parabolic, with its original embedded residual.

The natural action identifies the dotted image of L₀T with the intersection
of the seed stabilizer and the hatted-plane point centralizer. The checked
conjugate-center four-group is irreducible under that intersection. Since
L₀ is two-perfect and the supplement is the actual dotted Sylow two-group,
it is already irreducible under the dotted image of L₀.

The plane normalizer in LT normalizes C_L(V₂), hence L₀. Thus the original
P, I₂ and selected g preserve L₀ before taking any quotient. The final
application supplies these transports and irreducibility from the unchanged
orthogonal source hypotheses. The transport to Z(U)/((Z(U) ∩ Z(U)ᵍ)V₁),
the ensuing natural-four-module contradiction, catalogue exhaustion and
LocalControlInput remain with the natural-branch assembly owner.

Source: Aschbacher--Smith 12.9.4, printed pp.859--860 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The literal L₀ = O²(C_L(V₂)) on printed p.859. -/
@[expose] def planeCentralizerResidual (F : InvariantFlag T V n) (L : Subgroup G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer (F.Vi 2 : Set G) : Subgroup G)).map
    (L ⊓ centralizer (F.Vi 2 : Set G)).subtype

private theorem residual_join_sylow (C : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (C : Set G)) :
    (pResidual 2 (C ⊔ (T : Subgroup G) : Subgroup G)).map
      (C ⊔ (T : Subgroup G)).subtype = (pResidual 2 C).map C.subtype := by
  rw [← embedded_pResidual_sup_sylow_of_normalizes T C hn]
  exact embedded_pResidual_join_pGroup _ _ (isPPerfect_embedded_pResidual 2 C)
    T.isPGroup' (hn.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))

/-- The original point residual and Sylow recover the point stabilizer inside LT. -/
theorem point_residual_sylow_eq_intersection {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    F.Li L 1 ⊔ (T : Subgroup G) = (L ⊔ (T : Subgroup G)) ⊓ F.H := by
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by have := h.rank; omega)
  have ht : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [← F.H_eq_centralizer (by have := h.rank; omega) z hpoint]
    exact F.invariant 1
  simp only [Li,show ¬ (n = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega,if_false]
  change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype ⊔
    (T : Subgroup G) = _
  rw [F.H_eq_centralizer (by have := h.rank; omega) z hpoint]
  exact embedded_pointResidual_sup_sylow T L (h.sylow_normalizes earlier.structural) z ht

/-- Both source definitions of L₀ use the same embedded two-residual. -/
theorem planeCentralizerResidual_eq_point (F : InvariantFlag T V n) (L : Subgroup G) :
    planeCentralizerResidual F L =
      (pResidual 2 (F.Li L 1 ⊓ centralizer (F.Vi 2 : Set G) : Subgroup G)).map
        (F.Li L 1 ⊓ centralizer (F.Vi 2 : Set G)).subtype := by
  have hc : centralizer (F.Vi 2 : Set G) ≤ F.H :=
    (centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans (Subgroup.centralizer_le_normalizer _)
  have hRL : planeCentralizerResidual F L ≤ F.Li L 1 := by
    change (pResidual 2 _).map _ ≤ _
    simp only [Li,show ¬ (n = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega,if_false]
    exact embedded_pResidual_mono 2 (inf_le_inf_left L hc)
  exact (embedded_pResidual_eq_of_le_of_residual_le 2
    (inf_le_inf_right _ ((F.Li_le L 1).trans inf_le_left))
    (le_inf hRL ((map_subtype_le _).trans inf_le_right))).symm

private theorem nonabelian_U_le_T {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : F.U ≤ (T : Subgroup G) := by
  let := h.chosen.elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hs := (F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)).2
  exact F.binary_U_le_sylow (by omega) hs

/-- In the original nonabelian flag, T supplements the literal plane centralizer in H₂. -/
theorem nonabelian_H2_eq_centralizer_sup_sylow {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    F.H ⊓ F.Gi 2 = centralizer (F.Vi 2 : Set G) ⊔ (T : Subgroup G) := by
  let := h.chosen.elementary
  let := F.binaryPlane_elementary
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by have := h.rank; omega)
  have he := F.H2_eq_plane_centralizer_sup_U (by have := h.rank; omega) z hpoint hz
    (nonabelian_plane_commutator h earlier F hne)
  apply le_antisymm
  · rw [he]
    exact sup_le_sup_left (nonabelian_U_le_T h earlier F) _
  · exact sup_le (he ▸ le_sup_left) (le_inf (F.invariant 1) (F.invariant 2))

/-- The literal L₀T is the original point-plane intersection in LT. -/
theorem nonabelian_planeResidual_sup_sylow {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    planeCentralizerResidual F L ⊔ (T : Subgroup G) =
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.Gi 2 := by
  let N := (L ⊔ (T : Subgroup G)) ⊓ (F.H ⊓ F.Gi 2)
  let C := L ⊓ centralizer (F.Vi 2 : Set G)
  have hCN : C ≤ N := le_inf (inf_le_left.trans le_sup_left)
    (le_inf (inf_le_right.trans ((centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans
      (Subgroup.centralizer_le_normalizer _))) (inf_le_right.trans (Subgroup.centralizer_le_normalizer _)))
  have hTN : (T : Subgroup G) ≤ N := le_inf le_sup_right
    (le_inf (F.invariant 1) (F.invariant 2))
  have hRH : (pResidual 2 (F.H ⊓ F.Gi 2 : Subgroup G)).map
      (F.H ⊓ F.Gi 2).subtype ≤ centralizer (F.Vi 2 : Set G) := by
    rw [nonabelian_H2_eq_centralizer_sup_sylow h earlier F hne,
      residual_join_sylow _ ((F.invariant 2).trans (normalizer_le_normalizer_centralizer _))]
    exact map_subtype_le _
  have hRL : (pResidual 2 (L ⊔ (T : Subgroup G) : Subgroup G)).map
      (L ⊔ (T : Subgroup G)).subtype = L :=
    embedded_pResidual_join_pGroup L _ ((pResidual_eq_top_iff 2 L).mp h.residual)
      T.isPGroup' (h.sylow_normalizes earlier.structural)
  have hR : (pResidual 2 N).map N.subtype ≤ C := le_inf
    ((embedded_pResidual_mono 2 (show N ≤ L ⊔ (T : Subgroup G) from inf_le_left)).trans hRL.le)
    ((embedded_pResidual_mono 2 (show N ≤ F.H ⊓ F.Gi 2 from inf_le_right)).trans hRH)
  have he : planeCentralizerResidual F L = (pResidual 2 N).map N.subtype :=
    embedded_pResidual_eq_of_le_of_residual_le 2 hCN hR
  rw [he]
  have hs := congrArg (map N.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTN))
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,
    ←MonoidHom.range_eq_map,range_subtype] at hs
  rw [hs,point_residual_sylow_eq_intersection h earlier F,inf_assoc]

/-- L₀ is normalized by the full original plane normalizer inside LT. -/
theorem planeResidual_normalizer {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    (L ⊔ (T : Subgroup G)) ⊓ F.Gi 2 ≤
      normalizer (planeCentralizerResidual F L : Set G) := by
  have hNL : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer (h.sylow_normalizes earlier.structural)
  exact ((le_inf (inf_le_left.trans hNL)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))

/-- The selected original conjugator normalizes L₀. -/
theorem parabolic_normalizes_planeResidual {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : F.P L ≤ normalizer (planeCentralizerResidual F L : Set G) :=
  (le_inf inf_le_left (F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes)).trans
    (planeResidual_normalizer h earlier F)

/-- The literal I₂ also normalizes L₀, before any dotted quotient. -/
theorem nonabelian_I2_normalizes_planeResidual {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) : F.I₂ L ≤ normalizer (planeCentralizerResidual F L : Set G) := by
  apply (conjugateSpanBy_le_self ?_).trans (parabolic_normalizes_planeResidual h earlier F)
  exact (nonabelian_U_le_T h earlier F).trans (F.sylow_le_orderedParabolic L 1 |>.trans
    (F.orderedParabolic_one L).le)

/-- In degree four, L₀T is exactly the opposite end-node flag parabolic. -/
theorem nonabelian_four_planeResidual_ordered
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V 4) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U) :
    planeCentralizerResidual F L ⊔ (T : Subgroup G) = F.orderedParabolic L 3 ∧
      planeCentralizerResidual F L = F.orderedResidual L 3 := by
  have hj : planeCentralizerResidual F L ⊔ (T : Subgroup G) = F.orderedParabolic L 3 := by
    rw [nonabelian_planeResidual_sup_sylow h earlier F hne,
      point_residual_sylow_eq_intersection h earlier F]
    apply le_antisymm
    · rintro x ⟨⟨hx,h1⟩,h2⟩
      refine ⟨hx,mem_iInf.mpr fun i => mem_iInf.mpr fun hi => ?_⟩
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · exact h1
      · exact h2
    · rintro x ⟨hx,hi⟩
      exact ⟨⟨hx,(mem_iInf.mp (mem_iInf.mp hi 1) (by omega))⟩,
        mem_iInf.mp (mem_iInf.mp hi 2) (by omega)⟩
  refine ⟨hj,?_⟩
  have hn : (T : Subgroup G) ≤ normalizer (planeCentralizerResidual F L : Set G) :=
    (le_inf le_sup_right (F.invariant 2)).trans (planeResidual_normalizer h earlier F)
  have hr := embedded_pResidual_join_pGroup (planeCentralizerResidual F L) (T : Subgroup G)
    (isPPerfect_embedded_pResidual 2 _) T.isPGroup' hn
  rw [hj] at hr
  exact hr.symm

omit [Finite G] in
private theorem dot_sup (F : InvariantFlag T V n) (A B : Subgroup G)
    (hA : A ≤ F.H) (hB : B ≤ F.H) :
    F.terminalDot (A ⊔ B) = F.terminalDot A ⊔ F.terminalDot B := by
  change ((A ⊔ B).subgroupOf F.H).map _ = _
  rw [subgroupOf_sup hA hB,Subgroup.map_sup]
  rfl

omit [Finite G] in
/-- The source plane-centralizer residual fixes the literal hatted plane point. -/
theorem planeResidual_dot_le_pointCentralizer
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    F.terminalDot (planeCentralizerResidual F L) ≤ F.terminalPointCentralizer v := by
  rintro _ ⟨a,ha,rfl⟩
  have hc : (a:G) ∈ centralizer (F.Vi 2 : Set G) := (map_subtype_le _ ha).2
  have hv : v ∈ hatSpace F (F.Vi 2) := hline ▸ Submodule.mem_span_singleton_self v
  obtain ⟨w,hw,he⟩ := (show v.toMul ∈ hatImage F (F.Vi 2) from hv)
  change F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) v = v
  apply Additive.toMul.injective
  rw [F.terminalRepresentation_apply_mk,←he,F.terminalHatAction_apply_mk]
  congr 1
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mpr (hc w hw).symm

/-- The actual dotted L₀T equals the intersection used by the four-group action. -/
theorem nonabelian_planeResidual_dot_intersection
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    F.terminalDot (planeCentralizerResidual F L) ⊔ F.terminalDot (T : Subgroup G) =
      F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ F.terminalPointCentralizer v := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hRP : planeCentralizerResidual F L ≤ F.Li L 1 := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans inf_le_left
  have hRH : planeCentralizerResidual F L ≤ F.H := hRP.trans ((F.Li_le L 1).trans inf_le_right)
  have he := nonabelian_planeResidual_sup_sylow h earlier F hne
  apply le_antisymm
  · apply le_inf
    · exact sup_le (map_mono (comap_mono (hRP.trans le_sup_left)))
        (map_mono (comap_mono le_sup_right))
    · exact sup_le (planeResidual_dot_le_pointCentralizer F v hline)
        (sylow_fixes_plane_hat_point F v hv hline)
  · let S := ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf F.H) ⊓
      (F.terminalPointCentralizer v).comap (QuotientGroup.mk' F.terminalHatAction.ker)
    have hSV : S.map F.H.subtype ≤ normalizer (V : Set G) := by
      rintro _ ⟨a,ha,rfl⟩
      exact (sup_le (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
        (h.sylow_normalizes_seed earlier.structural)) ha.1
    have hcenter := F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne
    have hS : S.map F.H.subtype ≤ F.Gi 2 := by
      apply Subgroup.le_normalizer_iff.mpr
      rintro _ ⟨a,ha,rfl⟩ w hw
      let u : F.U := ⟨w,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) hw⟩
      have hu : hatElement F u ∈ hatSpace F (F.Vi 2) := ⟨u,hw,rfl⟩
      rw [hline] at hu
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
      have hh : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
          (hatElement F u) = hatElement F u := by rw [←hc,map_smul,ha.2]
      have hq := congrArg Additive.toMul hh
      rw [F.terminalRepresentation_apply_mk] at hq
      change F.terminalHatAction a (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U) u at hq
      rw [F.terminalHatAction_apply_mk] at hq
      have hz : F.uAction a u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp hq
      have hzG : ((F.uAction a u / u : F.U):G) ∈ F.Vi 1 := by
        rw [←hcenter]
        exact ⟨V.div_mem ((mem_normalizer_iff.mp (hSV (mem_map_of_mem _ ha)) w).mp
          (F.le_seed 2 hw)) (F.le_seed 2 hw),mem_map_of_mem F.U.subtype hz⟩
      have hhG := (F.Vi 2).mul_mem (F.monotone (by omega : 1 ≤ 2) hzG) hw
      simpa only [Subgroup.coe_div,F.uAction_apply,u,div_mul_cancel,Subgroup.subtype_apply] using hhG
    rintro _ ⟨⟨a,ha,rfl⟩,hfix⟩
    rw [←dot_sup F _ _ hRH (F.invariant 1),he]
    exact ⟨a,⟨ha,hS (mem_map_of_mem _ (show a ∈ S from ⟨ha,hfix⟩))⟩,rfl⟩

/-- The actual conjugate-center four-group is irreducible already under L₀.
The two-group supplement is the original dotted full Sylow. -/
theorem nonabelian_caseFive_center_irreducible_planeResidual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∀ A : Subgroup F.TerminalHdot, A ≤ F.terminalDot (conjugate F.ZU g) →
      F.terminalDot (planeCentralizerResidual F L) ≤ normalizer (A : Set F.TerminalHdot) →
      A = ⊥ ∨ A = F.terminalDot (conjugate F.ZU g) := by
  obtain ⟨v,hv,hline,hD,hcard,hDJ,hDN,hirr⟩ :=
    nonabelian_caseFive_center_four_geometry h hn earlier F hne g hgP hgH B₀ h5
  let := hD
  have he := nonabelian_planeResidual_dot_intersection h earlier F hne v hv hline
  have hJN := (normal_subgroupOf_iff_le_normalizer hDJ).mp hDN
  have hRH : planeCentralizerResidual F L ≤ F.H := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right))
  have hR : IsPPerfect 2 (F.terminalDot (planeCentralizerResidual F L)) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (F.Vi 2 : Set G))).of_surjective
      (dotMap F F.terminalHatAction (planeCentralizerResidual F L) hRH)
      (dotMap_surjective _ _ _ _)
  have hQ : IsPGroup 2 (F.terminalDot (T : Subgroup G)) :=
    T.isPGroup'.comap_subtype.map (QuotientGroup.mk' F.terminalHatAction.ker)
  apply four_irreducible_of_twoPerfect_supplement _ _ _ hR hQ hcard
    ((le_sup_left.trans he.le).trans hJN) ((le_sup_right.trans he.le).trans hJN)
  intro A hAD hAN
  apply hirr A hAD
  rwa [←he]

/-- The source conjugator and I₂ preserve exactly the residual whose dotted
image acts irreducibly on the conjugate center. -/
theorem nonabelian_caseFive_planeResidual_geometry
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    conjugate (planeCentralizerResidual F L) g = planeCentralizerResidual F L ∧
      F.I₂ L ≤ normalizer (planeCentralizerResidual F L : Set G) ∧
      ∀ A : Subgroup F.TerminalHdot, A ≤ F.terminalDot (conjugate F.ZU g) →
        F.terminalDot (planeCentralizerResidual F L) ≤ normalizer (A : Set F.TerminalHdot) →
        A = ⊥ ∨ A = F.terminalDot (conjugate F.ZU g) :=
  ⟨(conjugate_eq_iff _ g).mpr (parabolic_normalizes_planeResidual h earlier F hgP),
    nonabelian_I2_normalizes_planeResidual h earlier F,
    nonabelian_caseFive_center_irreducible_planeResidual h hn earlier F hne g hgP hgH B₀ h5⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
