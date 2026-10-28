module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallParabolicSetup
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualKernel

/-!
# Normalizer control for subgroups of the original small residual

The literal residual centralizes C_M(V) after passage to M/O₂(M).
For a T-invariant two-perfect subgroup of that residual, O₂(M) normalizes
the subgroup. The normalizer lifting theorem therefore lifts centralization
in the quotient to normalization in M. This proves the cubic assertion of
15.2.7 for every possible witness in 15.2.6, without an additional choice.

Source: Aschbacher--Smith 15.2.3(5), 15.2.6--7, pp.1105,1109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- Every T-invariant two-perfect subgroup of Y is normalized by C_M(V).
The normality asserted here is relative to that centralizer, not to G. -/
theorem ChosenSmallSource.centralizer_normalizes_residual_subgroup
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hle : Y₁ ≤ h.residual) (hp : IsPPerfect 2 Y₁)
    (hn : (T : Subgroup G) ≤ normalizer (Y₁ : Set G)) :
    M ⊓ centralizer (V : Set G) ≤ normalizer (Y₁ : Set G) := by
  let := h.prepared.elementary
  let q := QuotientGroup.mk' (pCore 2 M)
  let A := Y₁.subgroupOf M
  let C := M ⊓ centralizer (V : Set G)
  have hYM : Y₁ ≤ M := hle.trans (source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _))
  have hA : IsPPerfect 2 A := hp.of_surjective
    (subgroupOfEquivOfLe hYM).symm.toMonoidHom (subgroupOfEquivOfLe hYM).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkn : q.ker ≤ normalizer (A : Set M) := by
    rw [QuotientGroup.ker_mk', ←subgroupOf_normalizer_eq hYM]
    intro x hx
    exact hn ((pCore_isPGroup.le_sylow_of_normal (T.subtype h.maximal.1.2)) hx)
  have hc : A.map q ≤ centralizer ((C.subgroupOf M).map q : Set (M ⧸ pCore 2 M)) :=
    (map_mono (comap_mono hle)).trans (le_sup_right.trans
      (source_chosen_lemma_15_2_3_5 T h.maximal.1.2 h.partner h.prepared))
  have hlocal : C.subgroupOf M ≤ normalizer (A : Set M) := by
    rw [←comap_normalizer_map_of_pPerfect q A hA hk hkn]
    exact map_le_iff_le_comap.mp ((le_centralizer_iff.mp hc).trans
      (Subgroup.centralizer_le_normalizer _))
  rw [←subgroupOf_normalizer_eq hYM] at hlocal
  intro x hx
  exact hlocal (show (⟨x,hx.1⟩ : M) ∈ C.subgroupOf M from hx)

/-- The cubic clause of 15.2.7 follows for any subgroup satisfying the
containment, two-perfectness and invariance clauses of 15.2.6. -/
theorem ChosenSmallSource.cubicNormalizer_of_residual_subgroup
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hle : Y₁ ≤ h.residual) (hp : IsPPerfect 2 Y₁)
    (hn : (T : Subgroup G) ≤ normalizer (Y₁ : Set G)) :
    SmallCubicNormalizer h Y₁ := by
  intro X _ _ hXM _ _
  exact hXM.trans (h.centralizer_normalizes_residual_subgroup hle hp hn)

/-- The actual rank-one witness discharges the normalizer input in 15.2.8. -/
theorem SmallResidualWitness.cubicNormalizer
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} {h : ChosenSmallSource T M Mc V}
    (hw : SmallResidualWitness h Y₁) : SmallCubicNormalizer h Y₁ :=
  h.cubicNormalizer_of_residual_subgroup hw.le_residual hw.perfect hw.invariant

end CFSG.Quasithin.Chapter15.Section02
