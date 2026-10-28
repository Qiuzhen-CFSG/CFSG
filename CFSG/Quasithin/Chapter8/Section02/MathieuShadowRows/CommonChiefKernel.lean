module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialKernel
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefQuotients

import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# A common chief kernel under original odd-normalizer control

If all noncentral chief factors of the original H-span have the same
maximal-overgroup core as kernel, that core has two-group image on the
whole span. The whole-span kernel lies in H ∩ M and centralizes V.
Frattini and the original odd-normalizer control make this kernel a
two-group as well. Thus the common core is exactly O₂(H).

The actual M22-code application is `M22CodeWreath`: its proved solvable
chief sieve supplies the common kernel, rather than assuming its equality
with O₂(H). Source: Aschbacher--Smith 3.1.9(6), B.6.8 and 8.2.2(1),
printed pp.113--114,577--578,715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open NoncentralChiefRefinement MathieuCode.NormalizedShadowRows
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H M M₀ V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]

/-- The original common chief kernel is the actual two-core. -/
theorem common_chief_kernel_eq_twoCore
    (c : QrcHypotheses T M M₀ H V)
    (hp : IsMinimalParabolicOver (T.subtype c.right_mem.1.1.2) ⊤)
    (hVH : V ≤ H)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i)
    (hk : ∀ j, ¬ s.Central j → (s.factorRepresentation j).ker =
      minimalParabolicCore (T.subtype c.right_mem.1.1.2) hp)
    (hcontrol : ∀ X : Subgroup G, X ≠ ⊥ →
      X ≤ M ⊓ centralizer (V : Set G) → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ M) :
    minimalParabolicCore (T.subtype c.right_mem.1.1.2) hp = pCore 2 H := by
  let U := (conjugateSpan H V).subgroupOf H
  let J := minimalParabolicCore (T.subtype c.right_mem.1.1.2) hp
  let q := actionHom (normalRepresentation U)
  obtain ⟨f,hf,he,_⟩ := exists_chief_image_surjection U s i
  have hqJ : q.ker ≤ J := by
    change q.ker ≤ minimalParabolicCore _ hp
    rw [←hk i hi,←actionHom_ker_eq]
    intro x hx
    change actionHom (s.factorRepresentation i) x = 1
    rw [←he,show q x = 1 from hx,map_one]
  have hJM : J ≤ (H ⊓ M).subgroupOf H := by
    rw [←c.intrinsic_maximal_eq_intersection hp]
    exact normalCore_le _
  have hq2 : IsPGroup 2 q.ker := normal_centralizing_kernel_twoGroup q.ker
    (by rintro _ ⟨x,hx,rfl⟩; exact (hJM (hqJ hx)).2)
    (by rintro _ ⟨x,hx,rfl⟩; exact span_action_kernel_centralizes hVH x hx)
    c.right_mem.1.2 hcontrol
  have hJi : IsPGroup 2 (J.map q) := by
    rw [common_chief_kernel_image_eq_twoCore U s J hk i hi]
    exact pCore_isPGroup
  have hJ2 : IsPGroup 2 J := by
    have hh := hJi.comap_of_ker_isPGroup q hq2
    rwa [comap_map_eq_self hqJ] at hh
  exact le_antisymm (le_sSup ⟨inferInstance,hJ2⟩) (minimalParabolicTwoCore_le_core _ hp)

end CFSG.Quasithin.Chapter8.MathieuShadowRows
