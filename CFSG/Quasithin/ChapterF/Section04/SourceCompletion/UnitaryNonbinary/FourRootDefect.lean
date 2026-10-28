module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourDefect
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourRoots
public import Theory.GroupTheory.SylowKernelCore

/-!
# Native simple-root invariance of the PSU₄ completion defect

The proved full-middle defect preserves the whole native Borel. Its relative
two-core is the original upper-unitriangular Sylow, so that Sylow is invariant
under the defect. Fixation of the two actual reflections now transfers the
concrete Weyl/Sylow intersection descriptions of both simple roots.

The full extension's two-core is never substituted for the native Sylow.
This includes q = 4 and even extension degree. Setwise root invariance is
proved here; pointwise root fixation and native generation still have to
eliminate the defect. Source: the direct apartment route of Aschbacher–Smith
F.4.10,16–17, printed pp.279,282–283 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourGeneration
variable (m : ℕ) (hm : 1 ≤ m)
local notation "F" => MatrixField m
local notation "σ" => fieldConj m
local notation "hσ" => fieldConj_involutive m hm
local notation "J" => UnitaryFourFlag.form F σ hσ
local notation "π" => project F J

/-- Setwise invariance of the two concrete simple relative root subgroups. -/
def SimpleRootsInvariant (a : MulAut (ProjectiveGroup m hm)) : Prop :=
  (∀ x : F, ∃ y : F,
    a (π (SmallCompletion.FourRoots.shortRoot F σ hσ x))=
      π (SmallCompletion.FourRoots.shortRoot F σ hσ y)) ∧
  (∀ x : UnitaryFourSylow.FixedField F σ, ∃ y : UnitaryFourSylow.FixedField F σ,
    a (π (SmallCompletion.FourRoots.longRoot F σ hσ x))=
      π (SmallCompletion.FourRoots.longRoot F σ hσ y))

/-- The full native Borel determines its Sylow as its relative two-core.
Thus the proved defect constraints preserve the actual Sylow, not the
possibly larger two-core of the full extension overlap. -/
theorem constraints_preserve_upper (a : MulAut (ProjectiveGroup m hm))
    (ha : SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
      (diagonalCartan m hm) a) :
    ∀ b∈upperProjective m hm, a b∈upperProjective m hm := by
  have hb (b : ProjectiveGroup m hm) : a b∈overlap m hm ↔ b∈overlap m hm := by
    rw [←exact_overlap]
    exact and_congr (ha.preserves_left b) (ha.preserves_right b)
  have hmB : (overlap m hm).map a.toMonoidHom=overlap m hm := by
    ext b
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact (hb u).mpr hu
    · intro h
      refine ⟨a.symm b,?_,a.apply_symm_apply b⟩
      apply (hb _).mp
      simpa only [a.apply_symm_apply] using h
  have hc : (overlap m hm).pCoreIn 2=upperProjective m hm := by
    rw [pCoreIn,overlap_twoCore,subgroupOf_map_subtype,inf_eq_left.mpr (upperProjective_le_overlap m hm)]
  have hu : (upperProjective m hm).map a.toMonoidHom=upperProjective m hm := by
    rw [←hc,map_pCoreIn_of_injective 2 _ _ a.injective,hmB]
  intro b hb
  rw [←hu]
  exact ⟨b,hb,rfl⟩

/-- The intrinsic Weyl/Sylow intersections give the two actual simple roots. -/
theorem constraints_preserve_simpleRoots (a : MulAut (ProjectiveGroup m hm))
    (ha : SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
      (diagonalCartan m hm) a) : SimpleRootsInvariant m hm a := by
  exact ⟨SmallCompletion.FourRoots.preserves_projective_shortRoot F σ hσ a
      (constraints_preserve_upper m hm a ha) ha.fixes_point ha.fixes_plane,
    SmallCompletion.FourRoots.preserves_projective_longRoot F σ hσ a
      (constraints_preserve_upper m hm a ha) ha.fixes_point ha.fixes_plane⟩

/-- An actual small-completion defect preserves the concrete simple roots. -/
theorem fourth_root_defect (hmgt : 1 < m) (E : FourExtension m hm)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    ∃ a : E.middle, c.middle a=rotation m hm E c ^ 4 ∧
      SourceExtension.CartanFixedInvolution (point m hm) (plane m hm)
        (diagonalCartan m hm) a.val ∧ SimpleRootsInvariant m hm a.val := by
  obtain ⟨a,ha,hfix⟩ := fourth_defect m hm hmgt E c ho hcard
  exact ⟨a,ha,hfix,constraints_preserve_simpleRoots m hm a.val hfix⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FourWeyl
