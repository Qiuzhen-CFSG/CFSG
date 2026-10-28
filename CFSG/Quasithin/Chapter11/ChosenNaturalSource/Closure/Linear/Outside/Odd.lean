module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Setup
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
public import CFSG.Quasithin.ChapterB.Section06To07.IntrinsicMinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.FrattiniQuotient

/-!
# B.6.8 and the repaired odd-degree endpoint

The original selected H has unique maximal overgroup H∩M. Its kernel on
W/V₁ preserves V and therefore lies in that maximal subgroup's core.
The ordinary centralizer C_H(W) also lies there. B.6.8(5) identifies
C_T(W) with O₂(H)∩C_H(W), which is normal in H. This proves the
centralizer-normalization premise of the existing odd endpoint.

The final application retains exactly the source splitting, T=T_L,
and T∩L≤K. The last two are still natural-action geometry obligations;
no equality W=T∩L is used. The selection, residual and normalizer
hypotheses refer throughout to the original H.
Source: Aschbacher--Smith, 11.5.7, printed p.782, and B.6.8(5--6).
-/

public section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

theorem actionCentralizer_map_le_M (A : Subgroup G) (hA : A ≤ E.G₁) :
    (actionCentralizer E A hA).map A.subtype ≤ E.M := by
  apply le_trans _ (seed_normalizer_le_M E)
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  rintro _ ⟨a,ha,rfl⟩ v hv
  exact E.V₁_le ((mem_actionCentralizer_iff E A hA a).mp ha v
    (le_conjugateSpanBy V E.G₁ hv))


/-- Minimal parabolicity and the literal maximal overgroup of the original H. -/
theorem selected_minimal_parabolic
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hNT : normalizer (T : Set G) ≤ E.M) :
    ∃ hmin : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hmin =
        E.M.subgroupOf E.H := by
  have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hH
    (Or.inl hNT)
  obtain ⟨hTB,hBH,_⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component hH
  obtain ⟨hmin,hmax⟩ := ChapterB.intrinsic_minimalParabolic T E.H (E.H ⊓ E.M)
    hp hTB hBH
  have he : (E.H ⊓ E.M).subgroupOf E.H = E.M.subgroupOf E.H := by
    ext x
    exact and_iff_right x.property
  refine ⟨hmin, ?_⟩
  have hm : IsCoatom (E.M.subgroupOf E.H) := by
    simpa only [he] using hmax
  have hSM : ((T.subtype hH.1.1.2) : Subgroup E.H) ≤ E.M.subgroupOf E.H :=
    comap_mono D.sylow_normalizes_component
  exact (ChapterB.minimalParabolicMax_unique _ hmin hm hSM).symm

/-- Apply B.6.8(6b) to the literal action on W/V₁. -/
theorem H_action_kernel_le_core
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hNT : normalizer (T : Set G) ≤ E.M) :
    ∃ hmin : ChapterB.IsMinimalParabolicOver (T.subtype hH.1.1.2) ⊤,
      actionCentralizer E E.H hHG ≤
        ChapterB.minimalParabolicCore (T.subtype hH.1.1.2) hmin := by
  obtain ⟨hmin,hmax⟩ := selected_minimal_parabolic E hH hNT
  refine ⟨hmin, ChapterB.minimalParabolic_normal_le_core_of_le_max _ hmin _ ?_⟩
  rw [hmax]
  exact map_le_iff_le_comap.mp (actionCentralizer_map_le_M E E.H hHG)

/-- The source centralizer normalization follows from B.6.8(5). -/
theorem H_normalizes_sylow_centralizer
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁)
    (hNT : normalizer (T : Set G) ≤ E.M) :
    E.H ≤ normalizer (((T : Subgroup G) ⊓ centralizer (E.W : Set G) : Subgroup G) : Set G) := by
  obtain ⟨hmin,hmax⟩ := selected_minimal_parabolic E hH hNT
  let S := T.subtype hH.1.1.2
  let N := (centralizer (E.W : Set G)).subgroupOf E.H
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    ((hHG.trans (le_normalizer_conjugateSpanBy V E.G₁)).trans
      (normalizer_le_normalizer_centralizer E.W))
  have hNM : N ≤ ChapterB.minimalParabolicMax S hmin := by
    rw [hmax]
    exact comap_mono (((centralizer_le (le_conjugateSpanBy V E.G₁)).trans
      (Subgroup.centralizer_le_normalizer _)).trans (seed_normalizer_le_M E))
  have hNJ : N ≤ ChapterB.minimalParabolicCore S hmin :=
    ChapterB.minimalParabolic_normal_le_core_of_le_max S hmin N hNM
  have he : (S : Subgroup E.H) ⊓ N = pCore 2 E.H ⊓ N := by
    apply le_antisymm
    · exact le_inf ((inf_le_inf_left _ hNJ).trans_eq
        (ChapterB.minimalParabolic_sylow_inf_core S hmin)) inf_le_right
    · exact inf_le_inf_right N (pCore_isPGroup.le_sylow_of_normal S)
  have hn : ((S : Subgroup E.H) ⊓ N).Normal := by
    rw [he]
    infer_instance
  apply (normal_subgroupOf_iff_le_normalizer
    (inf_le_left.trans hH.1.1.2)).mp
  exact hn

/-- The odd endpoint, with residual containment and centralizer normalization proved. -/
theorem contradiction_of_sourceTL_eq
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hKL : E.K = E.L₁)
    (hpoint : outsideResidual E ≤ centralizer (E.V₁ : Set G))
    (hselect : outsideResidual E ≤ E.K ∨
      ⁅E.K, outsideResidual E⁆ ≤ E.K.pCoreIn 2)
    (hUL : E.W ≤ L) (hTK : (T : Subgroup G) ⊓ L ≤ E.K)
    (hTL : (T : Subgroup G) = LocalGeometry.sourceTL T L)
    (hsplit : LocalGeometry.sourceTL T L = ((T : Subgroup G) ⊓ L) ⊔
      ((T : Subgroup G) ⊓ centralizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ E.M) : False := by
  exact odd_normalizer_contradiction E hH.1.1.2 (hH.1.1.2.trans hHG)
    hUL hTK (hTL.trans hsplit) (residual_le_Y E hH hHG hKL hpoint hselect)
    ((map_subtype_le _).trans (H_normalizes_sylow_centralizer E hH hHG hNT))
    hNT hH.1.2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
