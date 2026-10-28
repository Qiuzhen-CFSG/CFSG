module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianExchanged
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement
/-!
# Excluding whole actions of the original point component

When Z(U) is the original point V₁, the action on U/Z(U) has kernel
exactly O₂(H). Its restriction therefore identifies the original point
component quotient K₁/O₂(K₁) with its literal dotted image, commuting
with the original projection. This lets the 12.9.3 catalogue apply to
any whole irreducible action of that image.

The small-module bounds exclude the sporadic and cover rows. Self-duality
excludes PSL₅(2); the A₇ six-space is excluded with the original marked
geometry. The A₈ action supplies the already proved CaseFive contradiction.
The E₄₉ extension cannot be quasisimple with center of order at most three.

On the same flag and escaping conjugator, the whole and exchanged
recognitions now exclude every low-rank witness. Thus the remaining
nonabelian branch has exactly the original marked fixed line. Triviality
of the smaller actor puts that point in every nonidentity displacement,
so all those displacements have rank greater than two. Exclusion of this
fixed-line branch, and hence point-span abelianity, remains open.

Source: Aschbacher--Smith 12.9.3--4, 12.8.13(6,8), and G.11.6--7,
printed pp.858--859,855--857,365--367.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- For the original point center, the hat and tilde action kernels coincide. -/
theorem nonabelian_hat_kernel_eq_core_of_center_eq {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hZ : F.ZU = F.Vi 1) :
    F.terminalHatAction.ker = pCore 2 F.H := by
  let := h.chosen.elementary
  have he := F.localKernel_eq_pCore h.source.simpleQTKE L _ F.H
    (by have := h.rank; omega) h.chosen.le_sylow h.chosen.normalizes
    (h.sylow_normalizes earlier.structural) h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L
    (h.point_mem_Hz F earlier.alternatives)
  apply le_antisymm ?_ (point_core_le_hat_kernel h earlier F)
  intro a ha
  apply he.le
  apply (F.mem_localTildeAction_ker_iff F.H le_rfl a).mpr
  have ha' : a ∈ F.uhatAction.ker := by
    rwa [F.terminalHatAction_unique F.uhatAction (fun a u => F.uhatAction_apply_mk a u)]
  intro b hb
  exact hZ ▸ (F.mem_uhatAction_ker_iff a).mp ha' b hb


/-- With Z(U)=V₁, the original point component's two-core quotient is
its literal image in the faithful action on U/Z(U). -/
theorem nonabelian_point_component_core_equiv_of_center_eq {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hZ : F.ZU = F.Vi 1) (C : ComponentGeometry F L) :
    ∃ e : (C.K1 ⧸ pCore 2 C.K1) ≃* F.terminalDot C.K1,
      ∀ k : C.K1, (e (QuotientGroup.mk' (pCore 2 C.K1) k) : F.TerminalHdot) =
        QuotientGroup.mk' F.terminalHatAction.ker (inclusion C.point_le k) := by
  let f := dotMap F F.terminalHatAction C.K1 C.point_le
  have hk : f.ker = pCore 2 C.K1 := by
    have hker : f.ker = (pCore 2 F.H).comap (inclusion C.point_le) := by
      rw [dotMap_ker,← MonoidHom.comap_ker,nonabelian_hat_kernel_eq_core_of_center_eq h earlier F hZ]
    apply le_antisymm ?_ ?_
    · rw [hker]
      exact le_sSup ⟨inferInstance,
        pCore_isPGroup.comap_of_injective (inclusion C.point_le) (inclusion_injective _)⟩
    · intro k hk
      rw [hker]
      have hh := pCoreAmbient_mono_of_isSubnormalIn C.K1 F.H 2 C.point_le
        C.normal.isSubnormal (mem_map_of_mem C.K1.subtype hk)
      obtain ⟨a,ha,he⟩ := hh
      change inclusion C.point_le k ∈ pCore 2 F.H
      exact (show a = inclusion C.point_le k from Subtype.ext he) ▸ ha
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (dotMap_surjective _ _ _ _))
  exact ⟨e,fun _ => rfl⟩

private theorem whole_seven_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {X J : Subgroup F.TerminalHdot} [IsElementaryAbelian 2 X]
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation X J J (finrank (ZMod 2) (Additive X)))
    (eK : J ≃* alternatingGroup (Fin 7)) : False := by
  let := h9.normal_H
  have hd := nonabelian_hat_rank h earlier F hne
  have hu := h9.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr eK)] at hu
  have hb := ChapterG.Section07.AlternatingSevenCover.alternating_seven_automorphism_two_rank
  let σ := (F.terminalRepresentation.comp J.subtype).comp eK.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff eK.symm.toMonoidHom eK.symm.surjective _).mpr h9.irreducible
  have hf : Function.Injective σ :=
    h9.faithful.comp (J.subtype_injective.comp eK.symm.injective)
  have hs := ChapterK.Alternating.sevenSmallDegreeSpectrum σ hf inferInstance (by omega)
  have hdim : finrank (ZMod 2) (Additive F.Uhat) = 6 := by
    rcases hs with hs | hs | hs <;> omega
  obtain ⟨f⟩ := ChapterK.Alternating.SevenSixSpace.of_point_fixed_or_dual σ hdim
    (ChapterK.Alternating.SevenSixSpace.fixed_or_dual
      ChapterK.Alternating.SevenSixSpace.pointSimpleDegrees _ hdim)
  let c := BinaryPermutation.coreEquivNatural (Fin 7) (by decide)
  let eV := f.toLinearEquiv.trans c.symm
  have he (l : J) (u : Additive F.Uhat) : eV (F.terminalRepresentation l u) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eK l) (eV u) := by
    apply c.injective
    change c (c.symm (f (F.terminalRepresentation l u))) =
      c (BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u)))
    rw [c.apply_symm_apply]
    have hh := BinaryPermutation.coreEquivNatural_equivariant (Fin 7) (by decide)
      (eK l).val (c.symm (f u))
    change c (BinaryPermutation.alternatingCoreRepresentation (Fin 7) (eK l) (c.symm (f u))) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 7) (eK l) (c (c.symm (f u))) at hh
    rw [hh,c.apply_symm_apply]
    have hh := IntertwiningMap.isIntertwining _ _ f.toIntertwiningMap (eK l) u
    change f (F.terminalRepresentation (eK.symm (eK l)) u) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 7) (eK l) (f u) at hh
    rwa [eK.symm_apply_apply] at hh
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,_,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  refine F.sevenModel_excluded g J eK eV he
    B hB hInv v hv hline hXT (sylow_fixes_plane_hat_point F v hv hline)
    hiso ?_ hfixed hWX hperp hrank ?_
  · intro x hx e he
    obtain ⟨φ,_,hφ⟩ := htrans ⟨x,hx⟩
    rw [hφ ⟨e,he⟩,add_sub_cancel_left,hline]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · exact nonabelian_conjugate_center_detected h hn earlier F hne g hgP hgH v hline

private theorem simple_of_model_center {A D : Type*} [Group A] [Group D]
    [IsQuasisimple A] (e : A ≃* D) (hz : center D = ⊥) : IsSimpleGroup A := by
  have hA : center A = ⊥ := by
    apply bot_unique
    intro a ha
    have hh := (centerCongr e ⟨a,ha⟩).property
    change e a ∈ center D at hh
    rw [hz,mem_bot] at hh
    exact (map_eq_one_iff e e.injective).mp hh
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hA).trans QuotientGroup.quotientBot).symm.isSimpleGroup

private theorem binary_model_equiv {A : Type*} [Group A] {d : ℕ}
    (hm : ClassicalGroup.IsPSL A d 2) :
    Nonempty (A ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) := by
  obtain ⟨k,_,_,hc,⟨e⟩⟩ := hm
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hc)
  exact ⟨e.trans (Atlas.fieldEquivPSL d a)⟩

private theorem point_whole_large_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (hZ : F.ZU = F.Vi 1)
    {X : Subgroup F.TerminalHdot} [IsElementaryAbelian 2 X]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)}
    {v : Additive F.Uhat} {W : Submodule (ZMod 2) (Additive F.Uhat)} {X₀ : Subgroup X}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v W X X₀)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation X (F.terminalDot C.K1) (F.terminalDot C.K1)
      (finrank (ZMod 2) (Additive X)))
    (hm : LargePointModel (C.K1 ⧸ pCore 2 C.K1)) : False := by
  obtain ⟨e,_⟩ := nonabelian_point_component_core_equiv_of_center_eq h earlier F hZ C
  let : IsQuasisimple (F.terminalDot C.K1) := h9.component.2
  rcases hm with hm | ⟨a⟩ | ⟨a⟩
  · exact ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.not_five_of_selfDual
      h9 (LargeWhole.selfDual hg10) ((binary_model_equiv hm).some |> e.symm.trans)
  · exact h9.not_m24_of_even_degree
      (AlternatingForm.even_finrank B hg10.alternating hg10.nondegenerate) (e.symm.trans a.some)
  · let a' := e.symm.trans a.some
    let := simple_of_model_center a' Janko4.model_center_eq_bot
    exact h9.not_janko_four a'

private theorem point_whole_seven_core_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (C : ComponentGeometry F L) (hZ : F.ZU = F.Vi 1)
    {X : Subgroup F.TerminalHdot} [IsElementaryAbelian 2 X]
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation X (F.terminalDot C.K1) (F.terminalDot C.K1)
      (finrank (ZMod 2) (Additive X)))
    (hm : Chapter1.Section02.LocalModels.HasExtension (C.K1 ⧸ pCore 2 C.K1)
      (Chapter1.Section02.LocalModels.ElementaryModel 7 2)
      (fun Y _ => Chapter1.Section02.LocalModels.IsSL Y 2 7)) : False := by
  obtain ⟨e,_⟩ := nonabelian_point_component_core_equiv_of_center_eq h earlier F hZ C
  let J := F.terminalDot C.K1
  let Q := C.K1 ⧸ pCore 2 C.K1
  let : IsQuasisimple J := h9.component.2
  let : IsQuasisimple Q := IsQuasisimple.of_mulEquiv e.symm
  have hzJ : Nat.card (center J) ≤ 3 := by
    rcases h9.single_component_models with ⟨hi,_⟩ | ⟨hz,_⟩
    · let := hi
      have hz : center J = ⊥ := center_eq_bot_of_simple_perfect
      rw [hz,card_bot]
      decide
    · rw [Nat.card_congr hz.some.toEquiv]
      norm_num
  have hzQ : Nat.card (center Q) ≤ 3 := (Nat.card_congr (centerCongr e).toEquiv).le.trans hzJ
  obtain ⟨N,hN,⟨a⟩,_⟩ := hm
  let := hN
  have hcard : Nat.card N = 49 := by
    rw [Nat.card_congr a.toEquiv]
    change Nat.card (Fin 2 → ZMod 7) = 49
    rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
    decide
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp : IsPGroup 7 N := IsPGroup.of_card (p := 7) (n := 2) hcard
  have hnc : N ≤ center Q := (show N ≤ pCore 7 Q from le_sSup ⟨hN,hp⟩).trans
    (IsQuasisimple.pCore_le_center 7)
  have hc : (49 : ℕ) ≤ 3 := hcard ▸ (Subgroup.card_le_of_le hnc).trans hzQ
  omega

/-- No whole action of the original point component survives in either
source degree. Every row of the actual two-core quotient catalogue is excluded. -/
theorem nonabelian_point_whole_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    {X : Subgroup F.TerminalHdot} [IsElementaryAbelian 2 X]
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)}
    {v : Additive F.Uhat} {W : Submodule (ZMod 2) (Additive F.Uhat)} {X₀ : Subgroup X}
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v W X X₀)
    (C : ComponentGeometry F L)
    (h9 : ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
      F.terminalRepresentation X (F.terminalDot C.K1) (F.terminalDot C.K1)
      (finrank (ZMod 2) (Additive X))) : False := by
  have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
  obtain ⟨e,_⟩ := nonabelian_point_component_core_equiv_of_center_eq h earlier F hZ C
  let J := F.terminalDot C.K1
  let : IsQuasisimple J := h9.component.2
  rcases C.alternatives with he | hm | ⟨hn4,hm⟩
  · exact hne (point_span_abelian_of_point_residual_normal h hn earlier F (he ▸ C.normal))
  · exact point_whole_large_impossible h earlier F C hZ hg10 h9 hm
  · subst n
    rcases hm with hm | ⟨a⟩ | hm | ⟨a⟩ | ⟨a⟩ | ⟨a⟩ | ⟨a⟩ | hm
    · let a := ((binary_model_equiv hm).some |> e.symm.trans).trans
        Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm
      have hd := nonabelian_hat_rank h earlier F hne
      obtain ⟨B',h5⟩ := whole_eight_caseFive h9 (by omega) a
      exact nonabelian_caseFive_impossible modules h preferred earlier four F hne g hgP hgH B' h5
    · exact whole_seven_impossible h (Or.inl rfl) earlier F hne g hgP hgH h9 (e.symm.trans a.some)
    · have hz : (center J).map e.symm.toMonoidHom = center (C.K1 ⧸ pCore 2 C.K1) := by
        ext a
        constructor
        · rintro ⟨b,hb,rfl⟩
          exact (centerCongr e.symm ⟨b,hb⟩).property
        · intro ha
          exact ⟨e a,(centerCongr e ⟨a,ha⟩).property,e.symm_apply_apply a⟩
      let a := (QuotientGroup.congr _ _ e.symm hz).trans hm.2.2.some
      have hc : Nat.card (center J) = 3 :=
        (Nat.card_congr ((centerCongr e.symm).trans hm.2.1.some).toEquiv).trans (by simp)
      exact h9.not_triple_alternating_seven a hc
    · exact h9.not_m23 (e.symm.trans a.some)
    · exact h9.not_higman_sims (e.symm.trans a.some)
    · exact h9.not_held (e.symm.trans a.some)
    · let a' := e.symm.trans a.some
      let := simple_of_model_center a' Rudvalis.LowCentralizers.model_center_eq_bot
      exact h9.not_rudvalis a'
    · exact point_whole_seven_core_impossible h earlier F C hZ h9 hm

/-- The original nonabelian configuration must have exactly its original
marked line as common fixed space; the whole and exchanged alternatives
are now excluded. This does not infer a low-rank witness from that line. -/
private theorem fixed_line_of_original
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) := by
  obtain ⟨hZ,hsmall,hX,B,v,hg10,hline,hS,hns,hi,hd,hr,hcases⟩ :=
    nonabelian_extraspecial_point_component modules h hn preferred earlier four F hne g hgP hgH
  let := hX
  rcases hcases with hf | ⟨hw,C,h9⟩
  · exact hf.trans hline.symm
  · exact (nonabelian_point_whole_impossible modules h hn preferred earlier four F hne g hgP hgH
      hg10 C h9).elim

private theorem source_lowRank_impossible
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hg10 : ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
      (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (hS : NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hw : LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) : False := by
  have hns := nonabelian_hat_not_solvable h hn F hne
  rcases ExchangedRecognition.corrected_conclusion_or_remaining
    hg10 ⟨nonabelian_sqtkCover h F⟩ hw hS with hc | ⟨_,_,hs | ⟨_,J,hJ,hm,_,hwhole | hex⟩⟩
  · obtain ⟨rfl,h5⟩ := nonabelian_corrected_catalogue_orthogonal h hn earlier F hne
      g hgP hgH B v (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) hc
    exact nonabelian_caseFive_impossible modules h preferred earlier four F hne g hgP hgH B h5
  · exact hns hs.1
  · obtain ⟨C⟩ := componentGeometry earlier h hn F
    obtain ⟨he,hOrbit⟩ := nonabelian_whole_eq_point h hn F hne C hwhole
    rw [hOrbit,he] at hwhole
    exact nonabelian_point_whole_impossible modules h hn preferred earlier four F hne g hgP hgH
      hg10 C hwhole
  · have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
    have hr := nonabelian_point_three_rank_of_center_eq h earlier F hne g hgP hgH v hline hZ
    obtain ⟨I,hI,hv,hgeo,_,_,_,_,m,hm5,hm8,_,hmodel⟩ := hex
    exact Exchanged.not_natural_of_point_rank hg10 ⟨nonabelian_sqtkCover h F⟩
      hw hS hns hr hJ hm hI hv hgeo m hm5 hm8 hmodel

/-- Every nonidentity element of the original actor has displacement rank
greater than two. The common fixed line and the rank bound use the unchanged flag and g. -/
theorem nonabelian_fixed_line_and_moved_rank
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
      ∀ x ∈ F.terminalDot (F.X g),
        x ≠ 1 →
        2 < finrank (ZMod 2) (RankTwo.movedSpace F.terminalRepresentation x) := by
  refine ⟨fixed_line_of_original modules h hn preferred earlier four F hne g hgP hgH,?_⟩
  intro x hx hxe
  by_contra hr
  obtain ⟨hX,B,v,hg10,hline,hS⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
  let := hX
  have hZ := nonabelian_center_eq_point modules h hn preferred earlier four F hne g hgP hgH
  have hs := nonabelian_smaller_actor_eq_bot_of_center_eq h F g hgP hZ
  let a : F.terminalDot (F.X g) := ⟨x,hx⟩
  have ha : a ∉ ((F.terminalDot (conjugate F.ZU g)).subgroupOf
      (F.terminalDot (F.X g))) := by
    simpa only [hs,bot_subgroupOf,mem_bot,Subtype.ext_iff,Subgroup.coe_one] using (show (a : F.TerminalHdot) ≠ 1 from hxe)
  have hp : v ∈ B.orthogonal (F.terminalRepresentation x - LinearMap.id).ker := by
    intro u hu
    apply hg10.alternating.isRefl
    exact hg10.fixed_bound a ha u (sub_eq_zero.mp hu)
  rw [hg10.displacement_ker_eq_orthogonal_range a,
    B.orthogonal_orthogonal hg10.nondegenerate hg10.alternating.isRefl] at hp
  exact source_lowRank_impossible modules h hn preferred earlier four F hne g hgP hgH
    B v hg10 hline hS ⟨x,hx,by omega,hp⟩

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
