module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.Initial
public import CFSG.Quasithin.Chapter3.Section01.Configuration
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Action
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The literal QRC configuration for 15.4.2(4)

Reducedness identifies O₂(C_M₀(V)) with O₂(M₀). Mapping the original kernel
identity into G gives D.1.1's centralizer equality. The conjugation image is
isomorphic to the original centralizer quotient, so it too has trivial
two-core. A minimal local overgroup outside M supplies the unique maximal
subgroup of H; uniqueness of M excludes every common normal two-subgroup.
No normalizer-case assumption from Hypothesis 3.1.5 is used.

Source: Aschbacher–Smith, 15.4.2(4), printed p.1156, first paragraph of its
proof, and Hypothesis D.1.1, printed pp.171–172.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.RatioSource
open MaximalPrimeSource
universe u
variable {G : Type u} [Group G]

/-- Exactly the local hypotheses in part (4), retaining the intrinsic V. -/
structure LocalHypotheses (T : Sylow 2 G) (M₀ M : Subgroup G) (V : Subgroup M₀) : Prop where
  mem_H : M₀ ∈ Chapter1.HOver G (T : Set G)
  maximal : IsMaximalTwoLocal M
  le_maximal : M₀ ≤ M
  unique : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M
  reduced : IsPReduced 2 V
  kernel : (T : Subgroup G).subgroupOf M₀ ⊓ centralizer (V : Set M₀) =
    (centralizer (V : Set M₀)).pCoreIn 2
  le_core : V.map M₀.subtype ≤ M.pCoreIn 2

variable {T : Sylow 2 G} {M₀ M : Subgroup G} {V : Subgroup M₀}

/-- Relative normality of the embedded original module. -/
theorem LocalHypotheses.normalizes (l : LocalHypotheses T M₀ M V) :
    M₀ ≤ normalizer (V.map M₀.subtype : Set G) := by
  let := l.reduced.normal
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    V.le_normalizer_map M₀.subtype

/-- The two descriptions of the original centralizer have the same elements. -/
theorem centralizer_map_subtype (M₀ : Subgroup G) (V : Subgroup M₀) :
    (centralizer (V.map M₀.subtype : Set G)).subgroupOf M₀ =
      centralizer (V : Set M₀) := by
  ext x
  constructor
  · intro hx v hv
    exact Subtype.ext (hx (M₀.subtype v) (mem_map_of_mem M₀.subtype hv))
  · intro hx v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact congrArg Subtype.val (hx w hw)

/-- The original centralizer quotient and D.1.1's actual action image agree. -/
noncomputable def LocalHypotheses.actionImageEquiv (l : LocalHypotheses T M₀ M V) :
    letI := l.reduced.normal
    (M₀ ⧸ centralizer (V : Set M₀)) ≃*
      ChapterD.internalActionImage M₀ (V.map M₀.subtype) l.normalizes := by
  let := l.reduced.normal
  let f := ChapterE.DihedralCubic.conjugation M₀ (V.map M₀.subtype) l.normalizes
  have hk : f.ker = centralizer (V : Set M₀) :=
    (ChapterE.DihedralCubic.conjugation_ker _ _ _).trans (centralizer_map_subtype M₀ V)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)

/-- Reducedness is transported along the actual action-image isomorphism. -/
theorem LocalHypotheses.actionImage_reduced (l : LocalHypotheses T M₀ M V) :
    pCore 2 (ChapterD.internalActionImage M₀ (V.map M₀.subtype) l.normalizes) = ⊥ := by
  let := l.reduced.normal
  rw [← pCore_map_iso 2 l.actionImageEquiv, l.reduced.quotient_pCore_eq_bot, Subgroup.map_bot]

/-- The intrinsic two-core is exactly the original Sylow centralizer. -/
theorem LocalHypotheses.core_eq_centralizer (l : LocalHypotheses T M₀ M V) :
    M₀.pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (V.map M₀.subtype : Set G) := by
  have hk := l.kernel.trans (AmalgamLocalCores.reduced_centralizer_core V l.reduced)
  have hm := congrArg (map M₀.subtype) hk
  rw [map_inf _ _ _ M₀.subtype_injective, map_subgroupOf_eq_of_le l.mem_H.2] at hm
  have hc : (centralizer (V : Set M₀)).map M₀.subtype =
      M₀ ⊓ centralizer (V.map M₀.subtype : Set G) := by
    rw [← centralizer_map_subtype M₀ V, subgroupOf_map_subtype, inf_comm]
  rw [hc, ← inf_assoc,
    inf_eq_left.mpr (show (T : Subgroup G) ≤ M₀ from l.mem_H.2)] at hm
  exact hm.symm

/-- Every Sylow element centralizes its central omega. -/
theorem sylow_le_centralizer_omega (T : Sylow 2 G) :
    (T : Subgroup G) ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  intro t ht z hz
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz).2.2 t ht |>.symm

variable [Finite G]

/-- Hypothesis 15.4.1 supplies a minimal member of H(T) outside M. -/
theorem exists_HStar (h : SourceHypotheses T) (hM : IsMaximalTwoLocal M) :
    ∃ H : Subgroup G, H ∈ Chapter3.HStar (T : Subgroup G) M := by
  obtain ⟨M₁, M₂, h₁, h₂, hc₁, hc₂, hne⟩ := h.centralizer_overgroups
  have hex : ∃ N : Subgroup G, IsMaximalTwoLocal N ∧ (T : Subgroup G) ≤ N ∧ ¬ N ≤ M := by
    by_cases hn : M₁ ≤ M
    · have he : M₁ = M := le_antisymm hn (h₁.2 hM.1 hn)
      refine ⟨M₂, h₂, (sylow_le_centralizer_omega T).trans hc₂, ?_⟩
      intro h₂M
      exact hne (he.trans (le_antisymm h₂M (h₂.2 hM.1 h₂M)).symm)
    · exact ⟨M₁, h₁, (sylow_le_centralizer_omega T).trans hc₁, hn⟩
  obtain ⟨N, hN, hTN, hNM⟩ := hex
  obtain ⟨H, _, hmin⟩ := Finite.exists_le_minimal
    (p := fun Y : Subgroup G => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M)
    (a := N) ⟨⟨Chapter1.mem_H_of_isTwoLocal hN.1, hTN⟩, hNM⟩
  exact ⟨H, hmin⟩

/-- Direct construction of D.1.1, without the extra cases in `QrcHypotheses`. -/
theorem LocalHypotheses.qrc (l : LocalHypotheses T M₀ M V)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterD.QRCConfiguration M₀ H (T : Subgroup G) (V.map M₀.subtype) := by
  let := l.reduced.elementary
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  refine ⟨inferInstance, inferInstance,
    ⟨T.subtype l.mem_H.2, map_subgroupOf_eq_of_le l.mem_H.2⟩,
    ⟨T.subtype hTH, map_subgroupOf_eq_of_le hTH⟩,
    map_subtype_le V, l.normalizes, IsElementaryAbelian.map M₀.subtype, l.actionImage_reduced,
    Chapter3.HStar.unique_maximal_subgroup T (l.mem_H.2.trans l.le_maximal) hH,
    l.core_eq_centralizer, ?_⟩
  intro N hN hn
  by_contra hne
  apply Chapter3.no_common_normal_of_unique_maximal (isPGroup_pCoreIn 2 M₀)
    l.unique hH.1.2
  refine ⟨N, hN, hne, Chapter3.normalIn_iff_le_normalizer.mpr ⟨?_, ?_⟩⟩
  · exact hN.trans ((pCoreIn_le 2 M₀).trans Chapter3.le_generated_left)
  · rwa [Chapter3.generated_eq_sup]

end CFSG.Quasithin.Chapter15.Section04.RatioSource
