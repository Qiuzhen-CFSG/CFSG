module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryPointSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinarySelectionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryFusion
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinarySource

/-!
# The ordinary solvable branch without a normalizer-supplement premise

The new ordinary 13.3.9 proof applies before M=LT is known. Substituting
it into the completed solvable local-product construction proves the actual
normalizer supplement. The original amalgam and recognition consumer can
then use this equality. Omega geometry and fusion are constructed from
the earlier source inputs, so no supplement, fusion or index is supplied.

Negated symplectic recognition now gives nonsolvability at every escaping
weight before the supplement is known. The same-G,T component constructor
then selects an actual escaping component at every such point. This
removes the circular ordinary 13.3.8/normalizer dependence. The nonsolvable
supplement at the selected component, the covered row, and full 13.4.1
assembly remain separate obligations. The retained universal structural
and 12.2.13 inputs in the solvable/fusion chain still need specialization.
Source: Aschbacher--Smith 13.4.6 and 13.4.8--9, pp.898,904--907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Solvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual M=LT equality in the ordinary solvable branch, with the
point-residual premise proved independently of that equality. -/
theorem ordinary_solvable_normalizer_supplement
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  obtain ⟨W,hW,hTW⟩ := exists_original_invariant_plane h structural D m
  exact (original_R1_inside_generation h₀ h structural D m
    (ordinary_firstFlagCore_alternative hl h structural D m eL z hz hzL)
    z hz hzL hout hfusion
    (fun Y hYH hnY hYM hp => ordinary_point_residual_at h (structural G T) D m eL
      z hz hzL hout hYH hnY hYM hp)
    hsolv hindex (fun _ => normalizer_primeToThree_residual_at h (structural G T) eL)
    W hW hTW).1

/-- The ordinary solvable recognition consumer now constructs its own
normalizer supplement, omega index and fusion. -/
theorem ordinary_solvable_recognition_without_supplement
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ClassicalGroup.IsPSp G 3 2 := by
  have hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w :=
    fun v _ w hw hc => ordinary_core_normalizer_fusion hl h₀ h structural D m earlier eL v w hw hc
  have hindex := original_omega_fixed_index h₀ h structural D m earlier
  have hM := ordinary_solvable_normalizer_supplement hl h₀ h structural D m eL
    z hz hzL hout hfusion hsolv hindex
  exact ordinary_R1_recognition h₀ h structural D m eL z hz hzL hout hfusion hsolv hindex
    h1332 modules fixed covered h13316 hl hM

/-- Apply the solved implication at every escaping point, before M=LT
has been established in the nonsolvable branch. -/
theorem ordinary_universal_nonsolvable_without_supplement
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (hnot : ¬ ClassicalGroup.IsPSp G 3 2) :
    ∀ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) →
      z.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) := by
  intro z hz hzL hout hs
  exact hnot (ordinary_solvable_recognition_without_supplement h₀ h structural D m eL
    earlier h1332 modules fixed covered h13316 hl z hz hzL hout hs)

/-- At every escaping weight, construct the actual component using the
universal nonsolvability just proved; no selected nonsolvability, outside
subgroup theorem or normalizer supplement is an input. -/
theorem ordinary_escaping_components_without_supplement
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (h1332 : Source1332OneTwo T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (covered : Nonsolvable.OriginalCoveredNatural1332At T L)
    (h13316 : ∀ C : Subgroup G, Hypothesis1331 T C →
      ¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 3)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (hnot : ¬ ClassicalGroup.IsPSp G 3 2)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧ K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧ ¬ L ≤ normalizer (K : Set G) := by
  exact ordinary_exists_escaping_component_at h₀ h (structural G T) m h1332 eL hz
    (fun he => hzL (he ▸ one_mem _)) hout
    (ordinary_universal_nonsolvable_without_supplement h₀ h structural D m eL earlier
      h1332 modules fixed covered h13316 hl hnot z hz hzL hout)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
