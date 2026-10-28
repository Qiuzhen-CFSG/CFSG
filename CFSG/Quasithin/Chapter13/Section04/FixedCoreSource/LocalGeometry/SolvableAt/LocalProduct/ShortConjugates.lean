module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.CentralizerModule
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortConjugates
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# Moving conjugates in the larger-kernel short-block branch: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/LocalProduct/ShortConjugates` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_conjugate_at {N B : Subgroup G} {g : G}
    (hg : g ∈ normalizer (N : Set G)) (hn : N ≤ normalizer (B : Set G)) :
    N ≤ normalizer (B.conjBy g : Set G) := by
  change N ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G)
  rw [← map_equiv_normalizer_eq]
  have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hn
  have he : N.map (MulAut.conj g).toMonoidHom = N :=
    mem_normalizer_iff_map_conj_eq.mp hg
  rwa [he] at hh

/-- Under the centralizing Thompson alternative, the actual H-conjugate span
of V lies in O₂(H), but does not centralize V. -/
theorem centralizer_short_block_span_moves_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (R : Subgroup G)
    (hcore : R ⊓ centralizer (centralizerOmegaOrbit T z.val : Set G) =
      (centralizer ({z.val} : Set G)).pCoreIn 2)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    let H := centralizer ({z.val} : Set G)
    let U := conjugateSpanBy V H
    U ≤ H.pCoreIn 2 ∧ ¬ U ≤ centralizer (V : Set G) := by
  let H := centralizer ({z.val} : Set G)
  let U := conjugateSpanBy V H
  have hVQ : V ≤ H.pCoreIn 2 := by
    rw [← hcore]
    exact le_inf (hVJ.trans (sSup_le fun _ hA => hA.1)) (hVJ.trans hJ)
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hUQ : U ≤ H.pCoreIn 2 := conjugateSpanBy_le hVQ hnQ
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hQT : H.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  refine ⟨hUQ,?_⟩
  intro hc
  have hUL : ⁅U,L⁆ ≤ U :=
    ((commutator_mono (le_inf (hUQ.trans hQT) hc) le_rfl).trans
      (sylow_module_centralizer_commutator_le_chosen D hb)).trans (le_conjugateSpanBy V H)
  have hnU : L ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) :=
    sup_le (le_normalizer_iff_commutator_le_left.mpr hUL)
      (hTH.trans (le_normalizer_conjugateSpanBy V H))
  have hne : U ≠ ⊥ := fun he => D.ne_bot (bot_unique (he ▸ le_conjugateSpanBy V H))
  have hN := normalizer_le_of_unique_maximalTwoLocal
    (h.source_normalizer_maximal_unique_at structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 H).to_le hUQ) hne hnU
  exact hout ((le_normalizer_conjugateSpanBy V H).trans hN)

/-- The moving conjugate is in the same actual two-core. Both copies of V
are normalized by that core, so their commutator lies in their intersection.
Earlier fusion control excludes the original fixed line from the other copy. -/
theorem centralizer_short_block_moving_conjugate_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (R : Subgroup G)
    (hcore : R ⊓ centralizer (centralizerOmegaOrbit T z.val : Set G) =
      (centralizer ({z.val} : Set G)).pCoreIn 2)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w) :
    let H := centralizer ({z.val} : Set G)
    ∃ g ∈ H,
      V.conjBy g ≤ H.pCoreIn 2 ∧
      H.pCoreIn 2 ≤ normalizer (V.conjBy g : Set G) ∧
      ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g ∧
      ⁅V,V.conjBy g⁆ ≠ ⊥ ∧
      ¬ V ⊓ centralizer (L : Set G) ≤ V.conjBy g := by
  classical
  let H := centralizer ({z.val} : Set G)
  let U := conjugateSpanBy V H
  obtain ⟨hUQ,hmove⟩ := centralizer_short_block_span_moves_at h structural D hb
    z hz R hcore hVJ hJ hout
  have hg : ∃ g : H, ¬ V.conjBy g.val ≤ centralizer (V : Set G) := by
    by_contra! hall
    apply hmove
    rw [conjugateSpanBy_eq_iSup_conj]
    exact iSup_le hall
  obtain ⟨g,hg⟩ := hg
  have hconj : V.conjBy g.val ≤ U :=
    (by change V.conjBy g.val ≤ conjugateSpanBy V H
        rw [conjugateSpanBy_eq_iSup_conj]
        exact le_iSup (fun t : H => V.map (MulAut.conj t.val).toMonoidHom) g)
  have hVQ : V ≤ H.pCoreIn 2 := (le_conjugateSpanBy V H).trans hUQ
  have hBn : H.pCoreIn 2 ≤ normalizer (V : Set G) :=
    (centralizer_core_le_normalizer_at h₀ h structural D m hz
      (fun he => hzL (he ▸ one_mem _))).trans (normalizer_component_le_module_at h structural D m)
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hnconj := normalizes_conjugate_at (hnQ g.property) hBn
  have hne : ⁅V,V.conjBy g.val⁆ ≠ ⊥ := by
    intro he
    exact hg (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he))
  refine ⟨g,g.property,hconj.trans hUQ,hnconj,
    le_inf (le_normalizer_iff_commutator_le_left.mp ((hconj.trans hUQ).trans hBn))
      (le_normalizer_iff_commutator_le_right.mp (hVQ.trans hnconj)),hne,?_⟩
  intro hfix
  obtain ⟨d,hd1⟩ := ne_bot_iff_exists_ne_one.mp m.fixed_ne_bot
  have hd : d.val ≠ 1 := fun he => hd1 (Subtype.ext he)
  have hdV : (⟨d.val,d.property.1⟩ : V) ≠ 1 := fun he => hd (congrArg Subtype.val he)
  obtain ⟨c,hc,he⟩ := (element_fusion_iff_centralizer_incidence V d.val).mp
    (hfusion ⟨d.val,d.property.1⟩ hdV) g.val (hfix d.property)
  have hcN : c ∈ normalizer (V : Set G) := by
    rw [← normalizer_component_eq_module_at h structural D m]
    exact (fixed_generator_centralizer_at h structural D m d.property hd) ▸ hc
  have heV : V.conjBy g.val = V := he.symm.trans (mem_normalizer_iff_map_conj_eq.mp hcN)
  let := D.elementary
  rw [heV] at hne
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance))


/-- The earlier 13.3.9 input identifies the literal kernel residual with L₁
in the larger-kernel short-block case, and gives its relative normality in H. -/
theorem centralizer_short_block_residual_normal_of_source1339_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
    ((pResidual 2 K).map K.subtype).map H.subtype = firstCentralizerResidual L z.val ∧
      H ≤ normalizer (firstCentralizerResidual L z.val : Set G) ∧
      firstCentralizerResidual L z.val ≤ centralizer (centralizerOmegaOrbit T z.val : Set G) := by
  classical
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  let := (centralizerOmegaOrbit_reduced h₀ hz (fun he => hzL (he ▸ one_mem _))).normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  have ordinary := ordinary_of_short_core_marking D m hb
  have hsel : selectedFirstResidual T L V z.val = firstCentralizerResidual L z.val := by
    simp only [selectedFirstResidual,if_pos ordinary]
  have he : A.map H.subtype = firstCentralizerResidual L z.val :=
    (centralizer_kernel_residual_of_source1339_at h₀ h structural D m z hz hzL
      hlarge (selectedFirstResidual T L V z.val) h1339).1.trans hsel
  refine ⟨he,?_,?_⟩
  · rw [← he]
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  · rw [← he]
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val ((map_subtype_le (pResidual 2 K) ha)
      ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)

/-- The actual larger-kernel short-block branch constructs the moving pair
and its residual layers. Earlier 13.4.4(ii) supplies only the original Sylow
placement; earlier 13.3.9 supplies the residual. The kernel intersection,
relative normality, moving conjugate and its layer properties are conclusions. -/
theorem centralizer_larger_short_block_moving_layers_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hVJ : V ≤ elementaryAbelianMaxJ R)
    (hJ : elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let A := firstCentralizerResidual L z.val
    let W := ⁅V,A⁆
    H ≤ normalizer (A : Set G) ∧
      ∃ g ∈ H,
        V.conjBy g ≤ H.pCoreIn 2 ∧
        H.pCoreIn 2 ≤ normalizer (V.conjBy g : Set G) ∧
        ⁅V,V.conjBy g⁆ ≤ V ⊓ V.conjBy g ∧
        ⁅V,V.conjBy g⁆ ≠ ⊥ ∧
        ¬ V ⊓ centralizer (L : Set G) ≤ V.conjBy g ∧
        W.conjBy g = ⁅V.conjBy g,A⁆ ∧
        W.conjBy g ≤ A.pCoreIn 2 ∧
        ⁅W.conjBy g,A⁆ = W.conjBy g ∧
        ⁅W.conjBy g,A.pCoreIn 2⁆ ≠ ⊥ := by
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz
    (fun he => hzL (he ▸ one_mem _)) R hRT S hR
  obtain ⟨_,hn,_⟩ := centralizer_short_block_residual_normal_of_source1339_at h₀ h structural
    D m hb z hz hzL hlarge h1339
  obtain ⟨g,hg,hgQ,hnQ,hcomm,hne,hfixed⟩ := centralizer_short_block_moving_conjugate_at
    h₀ h structural D m hb z hz hzL R hc hVJ hJ hout hfusion
  have hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2 := by
    rw [← hc]
    exact le_inf (hVJ.trans (sSup_le fun _ hA => hA.1)) (hVJ.trans hJ)
  exact ⟨hn,g,hg,hgQ,hnQ,hcomm,hne,hfixed,
    centralizer_short_block_conjugate_residual_layer D m hb z hzL hVQ hn g hg⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
