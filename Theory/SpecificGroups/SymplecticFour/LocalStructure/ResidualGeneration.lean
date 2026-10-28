module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.Sylow.Characters
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup

/-!
# Generation by the two nonbinary symplectic parabolic residuals

The common flag Borel normalizes both determinant kernels, hence their join.
Each parabolic is the join of its determinant kernel and that Borel. Since the
two parabolics generate Sp₄, the join of their kernels is normal and has a
solvable quotient. Perfectness of Sp₄ over a characteristic-two field of order
greater than two makes this quotient trivial. The nonbinary local-structure
calculation identifies the kernels with the actual solvable residuals.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
`refs/quasithin.pdf`, the parabolic selection in 13.6.19, printed p.931,
and the concrete Sp₄ parabolics in F.1.12(I)(2), printed pp.262–264.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The two determinant kernels generate the native symplectic matrix group. -/
theorem locals_sup_eq_top {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    pointLocal (F := F) ⊔ planeLocal = ⊤ := by
  let R := pointLocal (F := F) ⊔ planeLocal
  have hgen : R ⊔ borel = ⊤ := by
    rw [← parabolics_sup_eq_top (F := F), pointParabolic_eq_pointLocal_sup_borel,
      planeParabolic_eq_planeLocal_sup_borel]
    dsimp only [R]
    ac_rfl
  have hB : borel (F := F) ≤ normalizer (R : Set (Sp F)) :=
    (le_inf
      (inf_le_left.trans (le_normalizer_of_normal_subgroupOf pointLocal_le))
      (inf_le_right.trans (le_normalizer_of_normal_subgroupOf planeLocal_le))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : R.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le R.le_normalizer hB))
  let : Group.IsSolvable (borel (F := F)) := isSolvable_borel hF
  let f := (QuotientGroup.mk' R).comp borel.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective R y
    have hg : g ∈ R ⊔ borel := hgen.symm ▸ mem_top g
    obtain ⟨r, hr, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hg
    refine ⟨⟨b, hb⟩, ?_⟩
    change QuotientGroup.mk' R b = QuotientGroup.mk' R (r * b)
    have hrq : QuotientGroup.mk' R r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [map_mul, hrq, one_mul]
  let : Group.IsSolvable (Sp F ⧸ R) := Group.isSolvable_of_surjective hf
  let : Group.IsPerfect (Sp F) := perfect_of_card_gt_two (by
    rw [hF]
    exact (show 2 = 2 ^ 1 by decide).trans_lt (Nat.pow_lt_pow_right (by decide) hn))
  exact top_unique (by simpa only [solvableResidual_eq_top] using
    (solvableResidual_le_of_solvable_quotient R))

/-- The two intrinsic parabolic residuals generate Sp₄ for every nonbinary
finite field of characteristic two. -/
theorem parabolicResiduals_sup_eq_top {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    (solvableResidual (pointParabolic (F := F))).map pointParabolic.subtype ⊔
      (solvableResidual (planeParabolic (F := F))).map planeParabolic.subtype = ⊤ := by
  rw [pointParabolic_solvableResidual_eq hF hn,
    planeParabolic_solvableResidual_eq hF hn, locals_sup_eq_top hF hn]

end Theory.SpecificGroups.SymplecticFour
