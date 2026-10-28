module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianNatural
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The ambient point-centralizer preimage in the nonabelian branch

The full preimage in H of C_Hdot(Vhat₂) preserves V₂ Z(U). It contains
both the original Sylow subgroup and L₀ = O²(C_L(V₂)), but cannot
normalize V₂: H intersect G₂ is the literal tilded-plane centralizer,
whose Sylow three-subgroups are cyclic, whereas the dotted point
centralizer has three-rank at least two.

For the same natural constituent I, the displacement [I,Z(U)^g] equals
[Z(U),Z(U)^g]. Mutual normalization puts it in Z(I₂), so the original
I₂ centralizes it. It is nontrivial and lies in the D-fixed four-group,
hence has order two or four. The final application retains the original
flag, component, module, quotient and guarded earlier module source.

This does not identify the displacement with the whole fixed four-group.
That identification and the remaining ambient parabolic argument are still
needed for the orthogonal exclusion. The next source step uses O²(P₀),
the two-residual, not its two-core.

Source: Aschbacher--Smith, 12.8.13(8) and the proof of 12.9.4,
printed pp.855--856,860 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The full original preimage of the dotted plane-point centralizer. -/
@[expose] def planePointPreimage (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) : Subgroup G :=
  ((F.terminalPointCentralizer v).comap (QuotientGroup.mk' F.terminalHatAction.ker)).map
    F.H.subtype

omit [Finite G] in
theorem planePointPreimage_le_H (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) :
    planePointPreimage F v ≤ F.H := map_subtype_le _

omit [Finite G] in
theorem planePointPreimage_dot (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 F.Uhat] (v : Additive F.Uhat) :
    F.terminalDot (planePointPreimage F v) = F.terminalPointCentralizer v := by
  change ((((F.terminalPointCentralizer v).comap
    (QuotientGroup.mk' F.terminalHatAction.ker)).map F.H.subtype).subgroupOf F.H).map
    (QuotientGroup.mk' F.terminalHatAction.ker) = F.terminalPointCentralizer v
  rw [subgroupOf, comap_map_eq_self_of_injective F.H.subtype_injective, map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem planePointPreimage_contains_sylow_residual
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    planeCentralizerResidual F L ⊔ (T : Subgroup G) ≤ planePointPreimage F v := by
  have lift (A : Subgroup G) (hAH : A ≤ F.H)
      (hA : F.terminalDot A ≤ F.terminalPointCentralizer v) : A ≤ planePointPreimage F v := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hA (mem_map_of_mem _ ha),rfl⟩
  apply sup_le
  · apply lift _ _ (planeResidual_dot_le_pointCentralizer F v hline)
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans ((F.Li_le L 1).trans inf_le_right))
  · exact lift _ (F.invariant 1) (sylow_fixes_plane_hat_point F v hv hline)

omit [Finite G] in
/-- Fixing the hatted point preserves the whole original central extension
V₂ Z(U), with no choice of a complement. -/
theorem planePointPreimage_normalizes_plane_center
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    planePointPreimage F v ≤ normalizer ((F.Vi 2 ⊔ F.ZU : Subgroup G) : Set G) := by
  apply Subgroup.le_normalizer_iff.mpr
  rintro _ ⟨a,ha,rfl⟩ w hw
  let f := (MulAut.conj (a:G)).toMonoidHom
  have hZ : F.ZU.map f ≤ F.ZU := by
    exact (mem_normalizer_iff_map_conj_eq.mp
      (((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U))) a.property)).le
  have hP : (F.Vi 2).map f ≤ F.Vi 2 ⊔ F.ZU := by
    rintro _ ⟨x,hx,rfl⟩
    let u : F.U := ⟨x,(F.le_seed 2).trans (le_conjugateSpanBy V F.H) hx⟩
    have hu : hatElement F u ∈ Submodule.span (ZMod 2) {v} :=
      hline ▸ show hatElement F u ∈ hatSpace F (F.Vi 2) from ⟨u,hx,rfl⟩
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
    have he : F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a)
        (hatElement F u) = hatElement F u := by rw [←hc,map_smul,ha]
    have he' := congrArg Additive.toMul he
    rw [F.terminalRepresentation_apply_mk] at he'
    change F.terminalHatAction a (QuotientGroup.mk' (center F.U) u) =
      QuotientGroup.mk' (center F.U) u at he'
    rw [F.terminalHatAction_apply_mk] at he'
    have hz : F.uAction a u / u ∈ center F.U := QuotientGroup.eq_iff_div_mem.mp he'
    have hm := (F.Vi 2 ⊔ F.ZU).mul_mem
      ((show F.ZU ≤ F.Vi 2 ⊔ F.ZU from le_sup_right) (mem_map_of_mem F.U.subtype hz))
      ((show F.Vi 2 ≤ F.Vi 2 ⊔ F.ZU from le_sup_left) hx)
    change ((a:G) * x * (a:G)⁻¹ / x) * x ∈ F.Vi 2 ⊔ F.ZU at hm
    simpa only [f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, div_mul_cancel] using hm
  have hm : (F.Vi 2 ⊔ F.ZU).map f ≤ F.Vi 2 ⊔ F.ZU := by
    rw [Subgroup.map_sup]
    exact sup_le hP (hZ.trans le_sup_right)
  exact hm (mem_map_of_mem f hw)

/-- In the original nonabelian flag, H ∩ G₂ is precisely the tilded-plane
centralizer. The point contribution is retained in this quotient. -/
theorem nonabelian_point_plane_eq_tilde_centralizer {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    F.H ⊓ F.Gi 2 = F.terminalTildePlaneCentralizer := by
  let := h.chosen.elementary
  apply le_antisymm ?_ (le_inf F.terminalTildePlaneCentralizer_le_H
    (F.terminalTildePlaneCentralizer_le_G₂
      ((F.le_seed 2).trans ((le_conjugateSpanBy V F.H).trans F.U_le_H))))
  let := F.binaryPlane_elementary
  obtain ⟨z,hz,hpoint⟩ := SetupFlagGeometry.exists_point_generator F (by have := h.rank; omega)
  rw [F.H2_eq_plane_centralizer_sup_U (by have := h.rank; omega) z hpoint hz
    (nonabelian_plane_commutator h earlier F hne)]
  have lift (A : Subgroup G) (hAH : A ≤ F.H) (hc : ⁅F.Vi 2,A⁆ ≤ F.Vi 1) :
      A ≤ F.terminalTildePlaneCentralizer := by
    intro a ha
    refine ⟨⟨a,hAH ha⟩,?_,rfl⟩
    rintro _ ⟨w,hw,rfl⟩
    let aH : F.H := ⟨a,hAH ha⟩
    let q := QuotientGroup.mk' ((F.Vi 1).subgroupOf F.H)
    have he : q ⁅w,aH⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
      (hc (commutator_mem_commutator hw ha))
    rw [map_commutatorElement] at he
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  apply sup_le
  · apply lift _ ((centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans
        (Subgroup.centralizer_le_normalizer _))
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp le_rfl)).le.trans bot_le
  · apply lift _ F.U_le_H
    rw [commutator_comm,nonabelian_plane_commutator h earlier F hne]

/-- The full ambient preimage cannot normalize the original plane: that
would lift the rank-two dotted point centralizer through a cyclic Sylow
three-subgroup of the actual tilded-plane centralizer. -/
theorem nonabelian_caseFive_planePointPreimage_not_le_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v}) :
    ¬ planePointPreimage F v ≤ F.Gi 2 := by
  intro hPG
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let A := (F.terminalPointCentralizer v).comap q
  let S : Sylow 3 A := Classical.choice inferInstance
  have hPC := (le_inf (planePointPreimage_le_H F v) hPG).trans
    (nonabelian_point_plane_eq_tilde_centralizer h earlier F hne).le
  let j : A →* F.terminalTildePlaneCentralizer :=
    (F.H.subtype.comp A.subtype).codRestrict _
      (fun a => hPC (mem_map_of_mem F.H.subtype a.property))
  have hj : Function.Injective j := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun c : F.terminalTildePlaneCentralizer => (c:G)) he))
  have hr : primeRank 3 A ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 j hj).trans
      (nonabelian_tilde_plane_three_rank h earlier F hne g hgP hgH)
  let f : A →* F.terminalPointCentralizer v := (q.comp A.subtype).codRestrict _ (fun a => a.property)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker x.val
    exact ⟨⟨a,show q a ∈ F.terminalPointCentralizer v from ha.symm ▸ x.property⟩,Subtype.ext ha⟩
  have hlo := S.primeRank_le_one_of_surjective
    (S.isCyclic_of_odd_of_primeRank_le_one (by decide) hr) f hf
  have hhi := nonabelian_caseFive_point_rank h hn earlier F hne B h5 v hv hline
  omega

/-- The actual displacement of any chosen constituent equals the commutator
of the two centers. It lies in the center of the original I₂, so I₂ fixes it.
No equality with the whole D-fixed subgroup is assumed. -/
theorem nonabelian_caseFive_chosen_commutator_geometry
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B)
    (C : ComponentGeometry F L) {I : Subgroup G} (c : ChosenModule T C.K1 I)
    (hiZ : I ≤ F.ZU) :
    ⁅I,conjugate F.ZU g⁆ = ⁅F.ZU,conjugate F.ZU g⁆ ∧
      ⁅I,conjugate F.ZU g⁆ ≠ ⊥ ∧
      ⁅I,conjugate F.ZU g⁆ ≤ Section08.centerIn (F.I₂ L) ∧
      ⁅I,conjugate F.ZU g⁆ ≤ I ⊓ centralizer (conjugate F.ZU g : Set G) ∧
      F.I₂ L ≤ centralizer ((⁅I,conjugate F.ZU g⁆ : Subgroup G) : Set G) ∧
      planeCentralizerResidual F L ≤ normalizer ((⁅I,conjugate F.ZU g⁆ : Subgroup G) : Set G) := by
  let D := conjugate F.ZU g
  have hgG : g ∈ F.Gi 2 := F.P_le_G₂ (by decide) L h.chosen.normalizes hgP
  have hDH : D ≤ F.H := (F.conjugate_ZU_le_X g).trans (F.X_le_H g hgG)
  have hHI := nonabelian_caseFive_point_normalizes_chosen modules h preferred earlier F hne
    g hgP hgH B h5 C c hiZ
  have hDI : D ≤ normalizer (I : Set G) := hDH.trans hHI
  have hZC : F.ZU ≤ centralizer (F.Vi 2 : Set G) :=
    (centerIn_le_centralizer F.U).trans
      (centralizer_le ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))
  have hZD : F.ZU ≤ normalizer (D : Set G) :=
    hZC.trans (F.plane_centralizer_normalizes_actors g hgG).2
  have he : ⁅I,D⁆ = ⁅F.ZU,D⁆ := by
    rw [commutator_comm I D,commutator_comm F.ZU D]
    exact commutator_eq_of_centralizing_sup
      (nonabelian_caseFive_chosen_covers_center h earlier F hne g hgP hgH B h5 C c hiZ)
      inf_le_right (hiZ.trans hZD)
  have hJI : ⁅I,D⁆ ≤ I := le_normalizer_iff_commutator_le_left.mp hDI
  have hJD : ⁅I,D⁆ ≤ D := le_normalizer_iff_commutator_le_right.mp (hiZ.trans hZD)
  have hJZ : ⁅I,D⁆ ≤ Section08.centerIn (F.I₂ L) := by
    rw [←(nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH).1]
    exact le_inf (hJI.trans hiZ) hJD
  have hfix : ⁅I,D⁆ ≤ centralizer (D : Set G) :=
    hJD.trans (le_centralizer_iff_isMulCommutative.mpr
      (map_isMulCommutative F.ZU (MulAut.conj g⁻¹).toMonoidHom))
  refine ⟨he,nonabelian_caseFive_chosen_moved h earlier F hne g hgP hgH B h5 C c,
    hJZ,le_inf hJI hfix,
    le_centralizer_iff.mp (hJZ.trans (centerIn_le_centralizer _)),?_⟩
  have hRI : planeCentralizerResidual F L ≤ normalizer (I : Set G) := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans (C.contains.trans c.normalizes))
  have hRZ : planeCentralizerResidual F L ≤ normalizer (F.ZU : Set G) := by
    rw [planeCentralizerResidual_eq_point F L]
    exact (map_subtype_le _).trans (inf_le_left.trans (((F.Li_le L 1).trans inf_le_right).trans
      ((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U)))))
  have hRD : planeCentralizerResidual F L ≤ normalizer (D : Set G) := by
    rw [←(conjugate_eq_iff (planeCentralizerResidual F L) g).mpr
      (parabolic_normalizes_planeResidual h earlier F hgP)]
    change (planeCentralizerResidual F L).map (MulAut.conj g⁻¹).toMonoidHom ≤
      normalizer (conjugate F.ZU g : Set G)
    exact (map_mono hRZ).trans (F.ZU.le_normalizer_map (MulAut.conj g⁻¹).toMonoidHom)
  intro a ha
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hRI ha),
    mem_normalizer_iff_map_conj_eq.mp (hRD ha)]

/-- Original-flag application combining the actual ambient preimage and the
same natural constituent. The displacement has order two or four; the
remaining parabolic calculation must exclude the former before identifying
it with the fixed four-group. -/
theorem nonabelian_caseFive_ambient_parabolic_geometry
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
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧
      Nat.card I = 16 ∧ Nat.card (I ⊓ centralizer (conjugate F.ZU g : Set G) : Subgroup G) = 4 ∧
      planeCentralizerResidual F L ⊔ (T : Subgroup G) ≤ planePointPreimage F v ∧
      planePointPreimage F v ≤ F.H ∧
      planePointPreimage F v ≤ normalizer (I : Set G) ∧
      planePointPreimage F v ≤ normalizer ((F.Vi 2 ⊔ F.ZU : Subgroup G) : Set G) ∧
      ¬ planePointPreimage F v ≤ F.Gi 2 ∧
      ⁅I,conjugate F.ZU g⁆ = ⁅F.ZU,conjugate F.ZU g⁆ ∧
      ⁅I,conjugate F.ZU g⁆ ≤ Section08.centerIn (F.I₂ L) ∧
      ⁅I,conjugate F.ZU g⁆ ≤ I ⊓ centralizer (conjugate F.ZU g : Set G) ∧
      F.I₂ L ≤ centralizer ((⁅I,conjugate F.ZU g⁆ : Subgroup G) : Set G) ∧
      planeCentralizerResidual F L ≤ normalizer ((⁅I,conjugate F.ZU g⁆ : Subgroup G) : Set G) ∧
      (Nat.card (⁅I,conjugate F.ZU g⁆ : Subgroup G) = 2 ∨
        Nat.card (⁅I,conjugate F.ZU g⁆ : Subgroup G) = 4) := by
  obtain ⟨C,I,c,hi,_,hiZ,_,he,hHI,hcard,hfixed⟩ :=
    nonabelian_caseFive_natural_constituent_of_module_source modules h preferred earlier four
      F hne g hgP hgH B h5
  obtain ⟨_,_,v,_,_,_,hv,hline,_⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  obtain ⟨hc,hneJ,hJZ,hJfixed,hIJ,hRJ⟩ :=
    nonabelian_caseFive_chosen_commutator_geometry
      (modules.at T (natural_flag_many_maximalTwoLocals h earlier F))
      h preferred earlier F hne g hgP hgH B h5 C c hiZ
  refine ⟨v,C,I,c,hv,hline,hi,hiZ,he,hcard,hfixed,
    planePointPreimage_contains_sylow_residual F v hv hline,
    planePointPreimage_le_H F v,(planePointPreimage_le_H F v).trans hHI,
    planePointPreimage_normalizes_plane_center F v hline,
    nonabelian_caseFive_planePointPreimage_not_le_plane h (.inl rfl) earlier F hne
      g hgP hgH B h5 v hv hline,hc,hJZ,hJfixed,hIJ,hRJ,?_⟩
  let J := ⁅I,conjugate F.ZU g⁆
  let := c.elementary
  have hp : IsPGroup 2 J := (IsElementaryAbelian.isPGroup 2 I).to_le
    (hJfixed.trans inf_le_left)
  have hlo := (one_lt_card_iff_ne_bot J).mpr hneJ
  have hhi : Nat.card J ≤ 4 := hfixed ▸ Nat.card_le_card_of_injective (inclusion hJfixed) (inclusion_injective hJfixed)
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  rw [hk] at hlo hhi ⊢
  have hk2 : k ≤ 2 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ k)
    norm_num at hh'
    omega
  interval_cases k <;> norm_num at *

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
