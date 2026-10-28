module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.ElementSubgroupIncidence

/-!
# Moving conjugates in the larger-kernel short-block branch

Put H=C_G(z), V_H=⟨Ω₁(Z(T))^H⟩, and L₁=O^{3′}(C_L(z)), with
all subgroups embedded in the original G. Under the contrary assumption
[J(R₁),V_H]=1, the exact intersection C_{R₁}(V_H)=O₂(H) puts V in
O₂(H). Its H-conjugate span stays there. If that span centralized V,
the short-block identity [C_T(V),L]≤V would make LT normalize a
nontrivial two-subgroup whose full normalizer lies in M=N_G(L).
This contradicts H≰M, producing a noncommuting H-conjugate of V.

Both copies are normalized by O₂(H), so their commutator lies in their
intersection. Earlier normalizer fusion and the actual fixed-line
centralizer exclude C_V(L) from the other copy. In the larger-kernel
case, earlier 13.3.9 and the short-block marking identify O²(C_H(V_H))
with L₁ and prove its normality relative to H. Conjugation then carries
the literal layer [V,L₁] to [Vᵍ,L₁]≤O₂(L₁), preserving its movement by
both L₁ and O₂(L₁). The final theorem constructs this whole configuration
from the earlier residual-section Sylow placement and source inputs.

The remaining comparison of these two moved layers, which must force the
fixed line into V∩Vᵍ, remains with qt-d-1341-solvable-source, along with
Thompson noncentrality, the original R₁ identification, C₃ geometry and
ambient fusion. This module does not establish full 13.4.8–9. The genuine
earlier 13.2.2(5),(6), 13.3.9 and 13.4.4(ii) inputs retain their final
discharge with qt-d-1341-fixed-core-source and its existing producers.
Source: Aschbacher–Smith, 13.4.8, printed p.904, paragraphs beginning
“By 13.2.2.6” and “Suppose that L₁ is normal in H”.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_conjugate {N B : Subgroup G} {g : G}
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
theorem centralizer_short_block_span_moves
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (h.source_normalizer_maximal_unique structural
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
    ((isPGroup_pCoreIn 2 H).to_le hUQ) hne hnU
  exact hout ((le_normalizer_conjugateSpanBy V H).trans hN)

/-- The moving conjugate is in the same actual two-core. Both copies of V
are normalized by that core, so their commutator lies in their intersection.
Earlier fusion control excludes the original fixed line from the other copy. -/
theorem centralizer_short_block_moving_conjugate
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  obtain ⟨hUQ,hmove⟩ := centralizer_short_block_span_moves h structural D hb
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
    (centralizer_core_le_normalizer h₀ h structural D m hz
      (fun he => hzL (he ▸ one_mem _))).trans (normalizer_component_le_module h structural D m)
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hnconj := normalizes_conjugate (hnQ g.property) hBn
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
    rw [← normalizer_component_eq_module h structural D m]
    exact (fixed_generator_centralizer h structural D m d.property hd) ▸ hc
  have heV : V.conjBy g.val = V := he.symm.trans (mem_normalizer_iff_map_conj_eq.mp hcN)
  let := D.elementary
  rw [heV] at hne
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff_isMulCommutative.mpr inferInstance))


/-- The earlier 13.3.9 input identifies the literal kernel residual with L₁
in the larger-kernel short-block case, and gives its relative normality in H. -/
theorem centralizer_short_block_residual_normal_of_source1339
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
    (centralizer_kernel_residual_of_source1339 h₀ h structural D m z hz hzL
      hlarge (selectedFirstResidual T L V z.val) h1339).1.trans hsel
  refine ⟨he,?_,?_⟩
  · rw [← he]
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  · rw [← he]
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val ((map_subtype_le (pResidual 2 K) ha)
      ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)

/-- If the literal L₁ is normal in H, each conjugate of its moved layer
is the corresponding commutator, lies in O₂(L₁), and is still moved by
that same two-core. No replacement residual or abstract model is used. -/
theorem centralizer_short_block_conjugate_residual_layer
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (z : V) (hzL : z.val ∉ centralizer (L : Set G))
    (hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2)
    (hnormal : centralizer ({z.val} : Set G) ≤
      normalizer (firstCentralizerResidual L z.val : Set G))
    (g : G) (hg : g ∈ centralizer ({z.val} : Set G)) :
    let A := firstCentralizerResidual L z.val
    let W := ⁅V,A⁆
    W.conjBy g = ⁅V.conjBy g,A⁆ ∧
      W.conjBy g ≤ A.pCoreIn 2 ∧
      ⁅W.conjBy g,A⁆ = W.conjBy g ∧
      ⁅W.conjBy g,A.pCoreIn 2⁆ ≠ ⊥ := by
  let H := centralizer ({z.val} : Set G)
  let A := firstCentralizerResidual L z.val
  let W := ⁅V,A⁆
  have hAH : A ≤ H := (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hAV : A ≤ normalizer (V : Set G) :=
    ((firstCentralizerResidual_le L z.val).trans inf_le_left).trans D.normalizes
  have hAn : A.map (MulAut.conj g).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hnormal hg)
  have hAc : (A.pCoreIn 2).map (MulAut.conj g).toMonoidHom = A.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 A (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,hAn]
  have hWe : W.conjBy g = ⁅V.conjBy g,A⁆ := by
    change (⁅V,A⁆).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator,hAn]
    rfl
  have hnQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQn : (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp (hnQ hg)
  have hVgQ : V.conjBy g ≤ H.pCoreIn 2 := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hVQ
    rwa [hQn] at hh
  have hWA : ⁅V.conjBy g,A⁆ ≤ A :=
    le_normalizer_iff_commutator_le_right.mp ((hVgQ.trans (pCoreIn_le 2 H)).trans hnormal)
  have hWQ : ⁅V.conjBy g,A⁆ ≤ H.pCoreIn 2 :=
    (commutator_mono hVgQ hAH).trans (le_normalizer_iff_commutator_le_left.mp hnQ)
  have hcore : ⁅V.conjBy g,A⁆ ≤ A.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 H).to_le hWQ) hWA (normalizer_commutator_ge_right _ _)
  have hmove := commutator_isPPerfect_idempotent A (V.conjBy g)
    (firstCentralizerResidual_twoPerfect L z.val)
    ((isPGroup_pCoreIn 2 H).to_le hVgQ) (normalizes_conjugate (hnormal hg) hAV)
  have hcoreL : IsPGroup 2 (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L) := by
    rw [centralCore_eq_twoCore_of_short_core_marking D m hb]
    exact pCore_isPGroup
  have hne := firstCentralizerResidual_double_commutator_ne_bot D m hcoreL z hzL
  refine ⟨hWe,hWe.symm ▸ hcore,?_,?_⟩
  · rw [hWe]
    exact hmove
  · intro he
    apply hne
    apply (map_eq_bot_iff_of_injective (f := (MulAut.conj g).toMonoidHom)
      _ (MulAut.conj g).injective).mp
    rw [map_commutator,hAc]
    exact he


/-- The actual larger-kernel short-block branch constructs the moving pair
and its residual layers. Earlier 13.4.4(ii) supplies only the original Sylow
placement; earlier 13.3.9 supplies the residual. The kernel intersection,
relative normality, moving conjugate and its layer properties are conclusions. -/
theorem centralizer_larger_short_block_moving_layers
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  obtain ⟨_,hn,_⟩ := centralizer_short_block_residual_normal_of_source1339 h₀ h structural
    D m hb z hz hzL hlarge h1339
  obtain ⟨g,hg,hgQ,hnQ,hcomm,hne,hfixed⟩ := centralizer_short_block_moving_conjugate
    h₀ h structural D m hb z hz hzL R hc hVJ hJ hout hfusion
  have hVQ : V ≤ (centralizer ({z.val} : Set G)).pCoreIn 2 := by
    rw [← hc]
    exact le_inf (hVJ.trans (sSup_le fun _ hA => hA.1)) (hVJ.trans hJ)
  exact ⟨hn,g,hg,hgQ,hnQ,hcomm,hne,hfixed,
    centralizer_short_block_conjugate_residual_layer D m hb z hzL hVQ hn g hg⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
