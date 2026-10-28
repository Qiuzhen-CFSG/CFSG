module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianResidual
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Modules
public import Theory.GroupTheory.NormalizedSupCard

/-!
# A component lift of the original ambient parabolic

Let P₀ be the full preimage of the dotted plane-point centralizer and
P = P₀ intersect K₁T. The original K₁ surjects onto the dotted actor,
so P still has the entire parabolic image and contains the same L₀T.
Normality of K₁ in the point normalizer and the two-group supplement T
put R = O²(P) inside K₁. Therefore J = [Z(U),R] lies in the original
natural constituent I = [Z(U),K₁]. Two-perfect commutator idempotence gives
[V₂Z(U),R] = J and proves that P preserves V₂I. The original three-rank
bound excludes P ≤ N_G(V₂), so the residual moves V₂, J has at least four
elements, and V₂ < V₂I.

The full natural action also gives I intersect V = 1: that intersection
lies in V₁, which K₁ fixes pointwise. Consequently V₂I is elementary of
order 64, and V₂C_I(Z(U)^g) is elementary of order 16. The already proved
returning-center calculation makes I₂ preserve the latter and fix its
quotient by V₂. The final application constructs all these data for the
same original flag, component, constituent and literal quotient map.

This restricted lift supplies the required residual containment without
asserting it for the full P₀. The L₀-normalizer/fixed-space argument, the
ambient contradiction, genuine catalogue exhaustion and LocalControlInput
remain with the natural-branch assembly. The guarded earlier module theorem
and NaturalReduction 4 remain explicit source inputs.

Source: Aschbacher--Smith, proof of 12.9.4, printed pp.859--860 of
refs/quasithin.pdf; the parabolic is lifted inside the original K₁T.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The full dotted parabolic lifted inside the original component/Sylow join. -/
@[expose] def componentPlanePreimage (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (C : ComponentGeometry F L)
    (v : Additive F.Uhat) : Subgroup G :=
  (C.K1 ⊔ (T : Subgroup G)) ⊓ planePointPreimage F v

/-- The embedded two-residual of the component lift. -/
@[expose] def componentPlaneResidual (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (C : ComponentGeometry F L)
    (v : Additive F.Uhat) : Subgroup G :=
  (pResidual 2 (componentPlanePreimage F C v)).map (componentPlanePreimage F C v).subtype

/-- Center displacement by the two-residual of the component lift. -/
@[expose] def componentCenterDisplacement (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (C : ComponentGeometry F L)
    (v : Additive F.Uhat) : Subgroup G :=
  ⁅F.ZU,componentPlaneResidual F C v⁆

/-- The original plane-centralizer residual and Sylow lie in the lift. -/
theorem componentPlanePreimage_contains
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    planeCentralizerResidual F L ⊔ (T : Subgroup G) ≤ componentPlanePreimage F C v := by
  apply le_inf _ (planePointPreimage_contains_sylow_residual F v hv hline)
  apply sup_le_sup _ le_rfl
  rw [planeCentralizerResidual_eq_point F L]
  exact (map_subtype_le _).trans (inf_le_left.trans C.contains)

/-- Restricting the lift to K₁T retains the entire literal dotted parabolic. -/
theorem nonabelian_caseFive_componentPlanePreimage_dot
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) :
    F.terminalDot (componentPlanePreimage F C v) = F.terminalPointCentralizer v := by
  apply le_antisymm
  · exact (map_mono (comap_mono inf_le_right)).trans (planePointPreimage_dot F v).le
  · intro x hx
    have hk : x ∈ F.terminalDot C.K1 :=
      (nonabelian_caseFive_point_component_image h (.inl rfl) earlier F hne B h5 C).symm ▸ mem_top x
    obtain ⟨k,hk,rfl⟩ := hk
    exact ⟨k,⟨mem_sup_left hk,⟨k,hx,rfl⟩⟩,rfl⟩

/-- The two-group supplement makes the lifted two-residual lie in K₁. -/
theorem componentPlaneResidual_le_component
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (F : InvariantFlag T V 4) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (v : Additive F.Uhat) :
    componentPlaneResidual F C v ≤ C.K1 := by
  have hn : (T : Subgroup G) ≤ normalizer (C.K1 : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have he := embedded_pResidual_join_pGroup C.K1 (T : Subgroup G)
    (Chapter1.Section02.Adequate.mem_L_isPPerfect (nonabelian_point_component_local h F C))
    T.isPGroup' hn
  exact (embedded_pResidual_mono 2 (show componentPlanePreimage F C v ≤
    C.K1 ⊔ (T : Subgroup G) from inf_le_left)).trans he.le

/-- The original Sylow supplements the residual in the actual lift. -/
theorem componentPlaneResidual_sup_sylow
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    componentPlaneResidual F C v ⊔ (T : Subgroup G) = componentPlanePreimage F C v := by
  have ht : (T : Subgroup G) ≤ componentPlanePreimage F C v :=
    le_sup_right.trans (componentPlanePreimage_contains F C v hv hline)
  have he := congrArg (map (componentPlanePreimage F C v).subtype)
    (pResidual_sup_sylow_eq_top (T.subtype ht))
  simpa only [componentPlaneResidual,Subgroup.map_sup,Sylow.coe_subtype,
    map_subgroupOf_eq_of_le ht,←MonoidHom.range_eq_map,range_subtype] using he

/-- The same three-rank obstruction excludes plane normalization by this lift. -/
theorem nonabelian_caseFive_componentPlanePreimage_not_le_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ¬ componentPlanePreimage F C v ≤ F.Gi 2 := by
  intro hPG
  let P := componentPlanePreimage F C v
  have hPH : P ≤ F.H := inf_le_right.trans (planePointPreimage_le_H F v)
  have hPC := (le_inf hPH hPG).trans
    (nonabelian_point_plane_eq_tilde_centralizer h earlier F hne).le
  have hr : primeRank 3 P ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hPC)
      (inclusion_injective hPC)).trans
      (nonabelian_tilde_plane_three_rank h earlier F hne g hgP hgH)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let f : P →* F.terminalPointCentralizer v :=
    (q.comp (inclusion hPH)).codRestrict _ (fun p => by
      have hh : q (inclusion hPH p) ∈ F.terminalDot P := mem_map_of_mem _ p.property
      rwa [nonabelian_caseFive_componentPlanePreimage_dot h earlier F hne B h5 C v] at hh)
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ F.terminalDot P :=
      (nonabelian_caseFive_componentPlanePreimage_dot h earlier F hne B h5 C v).symm ▸ x.property
    obtain ⟨a,ha,he⟩ := hx
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  let S : Sylow 3 P := Classical.choice inferInstance
  have hlo := S.primeRank_le_one_of_surjective
    (S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) f hf
  have hhi := nonabelian_caseFive_point_rank h (.inl rfl) earlier F hne B h5 v hv hline
  omega


/-- The smaller ambient lift has its entire center displacement in the
original natural constituent, while keeping the original quotient map. -/
theorem componentPlaneResidual_displacement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (hi : I = ⁅F.ZU,C.K1⁆) :
    ⁅F.Vi 2 ⊔ F.ZU,componentPlaneResidual F C v⁆ = componentCenterDisplacement F C v ∧
      ⁅F.Vi 2,componentPlaneResidual F C v⁆ ≤ componentCenterDisplacement F C v ∧
      componentCenterDisplacement F C v ≤ I ∧
      componentPlanePreimage F C v ≤ normalizer (componentCenterDisplacement F C v : Set G) := by
  let P := componentPlanePreimage F C v
  let R := componentPlaneResidual F C v
  let Q := F.Vi 2 ⊔ F.ZU
  have hRP : R ≤ P := map_subtype_le _
  have hPP : P ≤ planePointPreimage F v := inf_le_right
  have hRfull : R ≤ planePointResidual F v := embedded_pResidual_mono 2 hPP
  have hZfull : ⁅Q,planePointResidual F v⁆ ≤ F.ZU := by
    rw [(planePointResidual_displacement h earlier F v hline).1]
    exact (planePointResidual_displacement h earlier F v hline).2.2.1
  have hQZ : ⁅Q,R⁆ ≤ F.ZU := (commutator_mono le_rfl hRfull).trans hZfull
  let := h.chosen.elementary
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.point_mem_Hz F earlier.alternatives)
  have hid := commutator_isPPerfect_idempotent R Q
    (isPPerfect_embedded_pResidual 2 P)
    (htwo.to_le (sup_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) (map_subtype_le _)))
    (hRP.trans (hPP.trans (planePointPreimage_normalizes_plane_center F v hline)))
  have he : ⁅Q,R⁆ = ⁅F.ZU,R⁆ := le_antisymm
    (hid.symm.le.trans (commutator_mono hQZ le_rfl))
    (commutator_mono le_sup_right le_rfl)
  have hPZ : P ≤ normalizer (F.ZU : Set G) :=
    (hPP.trans (planePointPreimage_le_H F v)).trans
      ((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U)))
  have hPR : P ≤ normalizer (R : Set G) := P.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image P (pResidual 2 P))
  refine ⟨he,(commutator_mono le_sup_left le_rfl).trans he.le,?_,?_⟩
  · rw [hi]
    exact commutator_mono le_rfl (componentPlaneResidual_le_component h F C v)
  · intro a ha
    change a ∈ normalizer ((⁅F.ZU,R⁆ : Subgroup G) : Set G)
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hPZ ha),
      mem_normalizer_iff_map_conj_eq.mp (hPR ha)]

/-- The selected lift preserves V₂I, and fixes its quotient by I. The
residual containment in K₁ discharges the required center-motion premise. -/
theorem componentPlanePreimage_normalizes_natural_extension
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) (hi : I = ⁅F.ZU,C.K1⁆) :
    componentPlanePreimage F C v ≤ normalizer ((F.Vi 2 ⊔ I : Subgroup G) : Set G) ∧
      ⁅F.Vi 2 ⊔ I,componentPlaneResidual F C v⁆ ≤ I := by
  let := h.chosen.elementary
  let R := componentPlaneResidual F C v
  have hRI : R ≤ normalizer (I : Set G) :=
    (componentPlaneResidual_le_component h F C v).trans c.normalizes
  have hHI : F.H ≤ normalizer (I : Set G) := by
    rw [hi]
    have hHZ : F.H ≤ normalizer (F.ZU : Set G) :=
      (le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U))
    have hHK := (normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hHZ ha),mem_normalizer_iff_map_conj_eq.mp (hHK ha)]
  obtain ⟨_,hplane,hJI,_⟩ := componentPlaneResidual_displacement h earlier F C v hline hi
  have hc : ⁅F.Vi 2 ⊔ I,R⁆ ≤ I := by
    apply commutator_sup_le_of_relative_normal F.H (F.Vi 2) I R I hHI
      (((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans F.U_le_H)
      (hiZ.trans ((map_subtype_le _).trans F.U_le_H))
      (hplane.trans hJI) (le_normalizer_iff_commutator_le_left.mp hRI)
  refine ⟨?_,hc⟩
  rw [←componentPlaneResidual_sup_sylow F C v hv hline]
  apply sup_le (le_normalizer_iff_commutator_le_left.mpr (hc.trans le_sup_right))
  exact (le_inf (F.invariant 2) ((F.invariant 1).trans hHI)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The residual has genuine motion inside the same constituent I, and the
original plane is a proper subgroup of V₂I. -/
theorem nonabelian_caseFive_component_displacement_moves
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (hi : I = ⁅F.ZU,C.K1⁆) :
    ¬ ⁅F.Vi 2,componentPlaneResidual F C v⁆ ≤ F.Vi 2 ∧
      ¬ componentCenterDisplacement F C v ≤ F.Vi 2 ∧ F.Vi 2 < F.Vi 2 ⊔ I := by
  have hout := nonabelian_caseFive_componentPlanePreimage_not_le_plane
    h earlier F hne g hgP hgH B h5 C v hv hline
  have hm : ¬ ⁅F.Vi 2,componentPlaneResidual F C v⁆ ≤ F.Vi 2 := by
    intro hc
    apply hout
    rw [←componentPlaneResidual_sup_sylow F C v hv hline]
    exact sup_le (le_normalizer_iff_commutator_le_left.mpr hc) (F.invariant 2)
  obtain ⟨_,hc,hJI,_⟩ := componentPlaneResidual_displacement h earlier F C v hline hi
  have hj : ¬ componentCenterDisplacement F C v ≤ F.Vi 2 := fun hh => hm (hc.trans hh)
  exact ⟨hm,hj,lt_iff_le_not_ge.mpr ⟨le_sup_left,fun hh => hj (hJI.trans (le_sup_right.trans hh))⟩⟩

/-- The natural constituent contains a fully moved residual submodule of
order at least four. This is a statement about the actual lift, not a model tag. -/
theorem nonabelian_caseFive_component_displacement_size
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hi : I = ⁅F.ZU,C.K1⁆) :
    ⁅componentCenterDisplacement F C v,componentPlaneResidual F C v⁆ = componentCenterDisplacement F C v ∧
      4 ≤ Nat.card (componentCenterDisplacement F C v) := by
  let J := componentCenterDisplacement F C v
  let R := componentPlaneResidual F C v
  obtain ⟨_,_,hJI,hPJ⟩ := componentPlaneResidual_displacement h earlier F C v hline hi
  have hRZ : R ≤ normalizer (F.ZU : Set G) :=
    ((map_subtype_le _).trans (inf_le_right.trans (planePointPreimage_le_H F v))).trans
      ((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U)))
  let := h.chosen.elementary
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.point_mem_Hz F earlier.alternatives)
  have hid : ⁅J,R⁆ = J := commutator_isPPerfect_idempotent R F.ZU
    (isPPerfect_embedded_pResidual 2 (componentPlanePreimage F C v))
    (htwo.to_le (map_subtype_le _)) hRZ
  have hnot := (nonabelian_caseFive_component_displacement_moves h earlier F hne g hgP hgH
    B h5 C v hv hline hi).2.1
  change ¬ J ≤ F.Vi 2 at hnot
  have hJne : J ≠ ⊥ := fun hz => hnot (hz ▸ bot_le)
  have hcard2 : Nat.card J ≠ 2 := by
    intro hj
    have hc : R ≤ centralizer (J : Set G) :=
      ((map_subtype_le _).trans hPJ).trans (normalizer_le_centralizer_of_card_two J hj)
    exact hJne (hid.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)))
  let := c.elementary
  obtain ⟨k,hk⟩ := ((IsElementaryAbelian.isPGroup 2 I).to_le hJI).exists_card_eq
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


/-- The natural constituent meets the original seed trivially. Any point
in their intersection lies in V₁ and is fixed by K₁, whereas the actual
full natural action has no nonzero fixed vector. -/
theorem nonabelian_caseFive_chosen_disjoint_seed
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU) : Disjoint I V := by
  let := h.chosen.elementary
  let := c.elementary
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨m⟩ := hnatural
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  rintro x ⟨hxi,hxv⟩
  have hxp : x ∈ F.Vi 1 :=
    (F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne) ▸
      (show x ∈ V ⊓ F.ZU from ⟨hxv,hiZ hxi⟩)
  let w : Additive I := Additive.ofMul ⟨x,hxi⟩
  have hw : m.coordinates w = 0 := by
    apply BinaryNaturalDual.VectorStabilizers.natural_fixed_eq_zero
      (by simp : 2 ≤ finrank (ZMod 2) (Fin 4 → ZMod 2))
    intro a
    obtain ⟨q,hq⟩ := m.quotientEquiv.surjective a
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 C.K1) q
    have he := m.equivariant k w
    rw [hq] at he
    have hkx : (k:G) * x * (k:G)⁻¹ = x :=
      mul_inv_eq_iff_eq_mul.mpr (hHC (C.point_le k.property) x hxp).symm
    have hw' : (Additive.ofMul ⟨(k:G) * w.toMul * (k:G)⁻¹,
      (mem_normalizer_iff.mp (c.normalizes k.property) w.toMul).mp w.toMul.property⟩ : Additive I) = w := by
      apply Additive.toMul.injective
      exact Subtype.ext hkx
    rw [hw'] at he
    exact he.symm
  have hw0 : w = 0 := m.coordinates.injective (hw.trans m.coordinates.map_zero.symm)
  exact congrArg (fun z : Additive I => (z.toMul:G)) hw0

/-- Every part of the same constituent gives an elementary direct plane
extension of the predicted order. This applies to I and to its actual
returning-center fixed subgroup. -/
theorem nonabelian_caseFive_plane_extension_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hnatural : NaturalModule c 4) (hiZ : I ≤ F.ZU)
    {A : Subgroup G} (hAI : A ≤ I) :
    IsElementaryAbelian 2 (F.Vi 2 ⊔ A : Subgroup G) ∧
      Nat.card (F.Vi 2 ⊔ A : Subgroup G) = 4 * Nat.card A := by
  let := h.chosen.elementary
  let := F.binaryPlane_elementary
  let := c.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le hAI
  have hAC : A ≤ centralizer (F.Vi 2 : Set G) :=
    (hAI.trans hiZ).trans ((centerIn_le_centralizer F.U).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))))
  have hd : Disjoint (F.Vi 2) A :=
    (nonabelian_caseFive_chosen_disjoint_seed h F hne C c hnatural hiZ).symm.mono
      (F.le_seed 2) hAI
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hAC,?_⟩
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hAC.trans (Subgroup.centralizer_le_normalizer _)) hd,F.card 2 (by decide)]
  rfl

/-- Actual original-flag application of the component lift. All residual
containment and motion premises are discharged, with the same chosen I.
The returning fixed four-group still requires its ambient normalizer argument. -/
theorem nonabelian_caseFive_natural_component_parabolic_geometry
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
      planeCentralizerResidual F L ⊔ (T : Subgroup G) ≤ componentPlanePreimage F C v ∧
      F.terminalDot (componentPlanePreimage F C v) = F.terminalPointCentralizer v ∧
      componentPlaneResidual F C v ≤ C.K1 ∧
      componentCenterDisplacement F C v ≤ I ∧
      ⁅componentCenterDisplacement F C v,componentPlaneResidual F C v⁆ = componentCenterDisplacement F C v ∧
      4 ≤ Nat.card (componentCenterDisplacement F C v) ∧
      F.Vi 2 < F.Vi 2 ⊔ I ∧
      componentPlanePreimage F C v ≤ normalizer ((F.Vi 2 ⊔ I : Subgroup G) : Set G) ∧
      ¬ componentPlanePreimage F C v ≤ F.Gi 2 ∧
      IsElementaryAbelian 2 (F.Vi 2 ⊔ I : Subgroup G) ∧
      Nat.card (F.Vi 2 ⊔ I : Subgroup G) = 64 ∧
      IsElementaryAbelian 2 (F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)) : Subgroup G) ∧
      Nat.card (F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)) : Subgroup G) = 16 ∧
      ⁅F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)),F.I₂ L⁆ ≤ F.Vi 2 ∧
      F.I₂ L ≤ normalizer
        ((F.Vi 2 ⊔ (I ⊓ centralizer (conjugate F.ZU g : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨v,C,I,c,hv,hline,hnat,hiZ,he,hcard,_,hfixed,_⟩ :=
    nonabelian_caseFive_natural_residual_geometry modules h preferred earlier four
      F hne g hgP hgH B h5
  obtain ⟨hmove,hsize⟩ := nonabelian_caseFive_component_displacement_size
    h earlier F hne g hgP hgH B h5 C v hv hline c he
  obtain ⟨hE,hEc⟩ := nonabelian_caseFive_plane_extension_card h F hne C c hnat hiZ le_rfl
  obtain ⟨hD,hDc⟩ := nonabelian_caseFive_plane_extension_card h F hne C c hnat hiZ
    (show I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ I from inf_le_left)
  rw [hcard] at hEc
  rw [hfixed] at hDc
  exact ⟨v,C,I,c,hv,hline,hnat,hiZ,he,hcard,
    componentPlanePreimage_contains F C v hv hline,
    nonabelian_caseFive_componentPlanePreimage_dot h earlier F hne B h5 C v,
    componentPlaneResidual_le_component h F C v,
    (componentPlaneResidual_displacement h earlier F C v hline he).2.2.1,hmove,hsize,
    (nonabelian_caseFive_component_displacement_moves h earlier F hne g hgP hgH
      B h5 C v hv hline he).2.2,
    (componentPlanePreimage_normalizes_natural_extension h earlier F C v hv hline c hiZ he).1,
    nonabelian_caseFive_componentPlanePreimage_not_le_plane h earlier F hne
      g hgP hgH B h5 C v hv hline,hE,hEc,hD,hDc,
    nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier F hne g hgP hgH B h5 hiZ⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
