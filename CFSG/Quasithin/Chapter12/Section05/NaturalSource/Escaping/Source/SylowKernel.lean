module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Assembly
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd

/-!
# The actual Sylow action kernel of the H-star span

The two-residual of H does not centralize U_H. The normal-subgroup
dichotomy for this original minimal parabolic therefore puts its action
kernel in the core of the unique maximal overgroup. The intersection of
that core with the original full Sylow is O₂(H). This proves the kernel
bound on the actual escaping conjugate A ≤ T used in the last source step.
It does not assert a bound on the full action kernel outside T.

Source: Aschbacher--Smith, B.6.8(5)--(6) and the final paragraph of 12.5.1,
printed pp.114--115,822.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE ChapterB
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

/-- The exact Sylow kernel consequence of the source's nontrivial residual action. -/
theorem HStar_sylow_action_kernel_le_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    (T : Subgroup G) ⊓ centralizer (s.marking.UH H : Set G) ≤ H.pCoreIn 2 := by
  let F := D.fundamentalSetup h.toHypothesis1221
  have hH' : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    simpa only [D.localOrbit_eq, ExteriorMarking.M] using hH
  have hP := Chapter10.source_hstar_minimal_parabolic_of_generation_gt_one F hH'
    ((s.exteriorFusion_from_source h structural).generation_gt_one H hH)
  let C := (centralizer (s.marking.UH H : Set G)).subgroupOf H
  have hn : H ≤ normalizer (centralizer (s.marking.UH H : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  let : C.Normal := normal_subgroupOf_iff_le_normalizer_inf.mpr
    ((le_inf hn H.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hKC : ¬ minimalParabolicResidual (H := H) ≤ C := by
    intro hc
    apply s.HStar_residual_not_centralizing_span h structural hH
    rintro x ⟨y,hy,rfl⟩
    exact hc hy
  have hCJ := minimalParabolic_normal_le_core_of_residual_not_le (T.subtype hH.1.1.2) hP C hKC
  intro x hx
  have hc : (⟨x,hH.1.1.2 hx.1⟩ : H) ∈ pCore 2 H := by
    rw [← minimalParabolic_sylow_inf_core (T.subtype hH.1.1.2) hP]
    exact ⟨hx.1,hCJ hx.2⟩
  exact ⟨⟨x,hH.1.1.2 hx.1⟩,hc,rfl⟩

/-- The last source contradiction only uses the Sylow action kernel. The
remaining section premises are the original incidence and image-rank bound;
the full H-action kernel is not assumed. -/
theorem exterior_false_of_HStar_incidence_and_image_rank {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHG : H ≤ s.marking.Gi 1)
    (hM : s.marking.Mi 1 ≤ s.marking.Li 1 ⊔ H)
    (hsmall : primeRank 2 (s.terminalImage H ((T : Subgroup G) ⊓ centralizer (V : Set G))) ≤ 2) :
    False := by
  obtain ⟨g,hAT,_,hAC,hescape⟩ := s.exists_conjugate_escaping_HStar_core h structural hH
  have hcor := s.terminal_corank_le_two_of_centralizer_image hH.1.1.2 hsmall hAT hAC
  have hcomm := s.terminal_commutator_line_of_point_parabolic_le h hHG hM g
  have hAH := hAT.trans hH.1.1.2
  have hn := s.terminal_span_normalizes_of_corank_two h structural hHG hAH hcomm hcor
  let := D.elementary
  let := IsElementaryAbelian.map (p := 2) (A := V) (MulAut.conj g).toMonoidHom
  let := s.HStar_span_elementary h structural hHG
  let C := ⁅s.marking.UH H, terminalIntersection s.marking H g⁆
  have hbot : C = ⊥ := by
    let : Fact (Nat.card (s.marking.Vi 1)).Prime :=
      ⟨by rw [s.marking.card_V₁]; exact Nat.prime_two⟩
    rcases (C.subgroupOf (s.marking.Vi 1)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply le_bot_iff.mp
      exact (le_inf le_rfl hcomm).trans (disjoint_iff_inf_le.mp (subgroupOf_eq_bot.mp hb))
    · have hline : s.marking.Vi 1 ≤ C := subgroupOf_eq_top.mp ht
      have hCA : C ≤ V.map (MulAut.conj g).toMonoidHom :=
        (commutator_mono le_rfl inf_le_left).trans
          (le_normalizer_iff_commutator_le_right.mp hn)
      have p := s.pointControl_from_source h structural
      have hcoreNorm : centralizer ({s.marking.z} : Set G) ≤
          normalizer ((s.marking.Gi 1).pCoreIn 2 : Set G) := by
        rw [← p.point_centralizer]
        exact (s.marking.Gi 1).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image (s.marking.Gi 1)
            (pCore 2 (s.marking.Gi 1)))
      have hcore : V.map (MulAut.conj g).toMonoidHom ≤ (s.marking.Gi 1).pCoreIn 2 := by
        apply conjugate_le_of_element_fusion_of_normalized ?_ p.seed_core hcoreNorm
          (hCA (hline p.point_mem))
        intro x hx
        obtain ⟨l,hl,he⟩ := p.fusion x hx
        exact ⟨l,D.normalizes hl,he.symm⟩
      exact (hescape ((le_inf hAH hcore).trans (inf_pCoreIn_le_of_le 2 hHG))).elim
  have hUB : s.marking.UH H ≤ centralizer (terminalIntersection s.marking H g : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hbot
  have he := centralizer_inf_eq_of_corank_lt_globalS
    (show terminalIntersection s.marking H g ≤ V.map (MulAut.conj g).toMonoidHom
      from inf_le_left) (s.terminal_corank_lt_globalS h structural hcor)
    (IsElementaryAbelian.isPGroup 2 (s.marking.UH H))
  have hUA : s.marking.UH H ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro x hx
    exact (he.le ⟨hx,hUB hx⟩).2
  exact hescape ((le_inf hAT (le_centralizer_iff.mp hUA)).trans
    (s.HStar_sylow_action_kernel_le_core h structural hH))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
