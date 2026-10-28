module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction
public import Theory.SpecificGroups.AlternatingSeven.CubicSylowExtension
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Cubic overgroups and the alternating-seven terminal branch

An overgroup of index three over T which escapes M cannot have normal
Sylow two-subgroup: otherwise it would normalize W₀ and lie in M.
The three-coset action therefore identifies its actual two-core quotient
with S₃. The terminal construction then supplies every clause of the
original TerminalConfiguration.

For K₁/O₂(K₁)≅A₇, the invariant cubic Sylow overgroups in the concrete model
lift through the original quotient and are normalized by T. They generate
K₁T, so one escapes M. This completes the alternating-seven terminal branch;
the binary linear rows still require their overgroup construction.

Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Index three and weak-closure escape produce the literal terminal configuration. -/
theorem terminalConfiguration_of_cubic
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n → F.Gi i ≤ seedNormalizer (normalizer (L : Set G)) V)
    (fusion : FusionControl T L V)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H) (hH : H ≤ F.H)
    (hHM : ¬ H ≤ normalizer (L : Set G))
    (hindex : (T : Subgroup G).relIndex H = 3) :
    Nonempty (TerminalConfiguration F L) := by
  have hproper : pCore 2 H < (T.subtype hTH : Subgroup H) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH))
    intro heq
    have he : H.pCoreIn 2 = (T : Subgroup G) := by
      change (pCore 2 H).map H.subtype = _
      rw [heq, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
    have hHT : H ≤ normalizer ((T : Subgroup G) : Set G) := by
      rw [← he]
      exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
    exact hHM (hHT.trans ((ChapterE.normalizer_le_weakClosure_normalizer V (T : Subgroup G) 0).trans
      fusion.weakClosure_normalizer))
  obtain ⟨e⟩ := sylow_index_three_core_quotient (T.subtype hTH) hindex hproper
  exact terminalConfiguration_of_symmetricThree h hn earlier F hab control fusion H hTH hH hHM e

/-- The remaining cubic-overgroup selection, owned by `qt-d-1291-natural-source`. -/
def CubicOvergroupInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C →
      ∃ H : Subgroup X, (T : Subgroup X) ≤ H ∧ H ≤ C.K1 ⊔ (T : Subgroup X) ∧
        (T : Subgroup X).relIndex H = 3 ∧ ¬ H ≤ normalizer (L : Set X)

/-- Cubic overgroups discharge the full terminal-stage contract. -/
theorem terminalInput_of_cubicOvergroups (source : CubicOvergroupInput K) : TerminalInput K := by
  intro X _ _ T L V n h hn earlier F hab C localControl fusion
  obtain ⟨H,hTH,hHK,hi,hHM⟩ := source X T L V n h hn earlier F hab C localControl
  exact terminalConfiguration_of_cubic h hn earlier F hab localControl.normalizers fusion H hTH
    (hHK.trans (sup_le C.point_le (F.invariant 1))) hHM hi

/-- Lift the actual alternating-seven cubic overgroup into the original component. -/
theorem cubic_overgroup_of_alternatingSeven
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L) (control : LocalControl C)
    (e : (C.K1 ⧸ pCore 2 C.K1) ≃* alternatingGroup (Fin 7)) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ H ≤ C.K1 ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex H = 3 ∧ ¬ H ≤ normalizer (L : Set G) := by
  have hTM := h.sylow_normalizes earlier.structural
  have hnorm : (T : Subgroup G) ≤ normalizer (C.K1 : Set G) :=
    (F.invariant 1).trans ((normal_subgroupOf_iff_le_normalizer C.point_le).mp C.normal)
  have hout : ¬ C.K1 ≤ normalizer (L : Set G) :=
    fun hk => control.overgroup.2.2 (sup_le hk hTM)
  exact AlternatingSeven.CubicSylowExtension.exists_cubic_overgroup T C.K1
    (normalizer (L : Set G)) hTM hnorm e hout

/-- The terminal configuration in the actual alternating-seven component row. -/
theorem terminalConfiguration_of_alternatingSeven
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (control : LocalControl C) (fusion : FusionControl T L V)
    (e : (C.K1 ⧸ pCore 2 C.K1) ≃* alternatingGroup (Fin 7)) :
    Nonempty (TerminalConfiguration F L) := by
  obtain ⟨H,hTH,hHK,hi,hHM⟩ := cubic_overgroup_of_alternatingSeven h earlier F C control e
  exact terminalConfiguration_of_cubic h hn earlier F hab control.normalizers fusion H hTH
    (hHK.trans (sup_le C.point_le (F.invariant 1))) hHM hi

/-- With the preceding stages supplied, the alternating-seven row is impossible. -/
theorem not_alternatingSeven_of_fusion
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (C : ComponentGeometry F L)
    (control : LocalControl C) (fusion : FusionControl T L V) :
    ¬ Nonempty ((C.K1 ⧸ pCore 2 C.K1) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  obtain ⟨d⟩ := terminalConfiguration_of_alternatingSeven h hn earlier F hab C control fusion e
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab fusion.hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index
end CFSG.Quasithin.Chapter12.Section09.NaturalSource
