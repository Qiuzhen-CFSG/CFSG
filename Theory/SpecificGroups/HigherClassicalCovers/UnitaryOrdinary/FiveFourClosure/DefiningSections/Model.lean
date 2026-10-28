module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.Reduction
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Split

/-!
# The actual radical–Levi subgroup for the defining-prime calculation

The line radical and the middle SU₃ block multiply inside SU₅, before
projectivization. The matrix conjugation identity makes this multiplication
a homomorphism from the established semidirect product. Its projective image
is the existing faithful radical–Levi embedding, so the SU embedding is
faithful as well. A compatible pair of lifts therefore gives a section over
its literal image subgroup.

This is the local subgroup used for Aschbacher–Smith I.1.4(4), printed p.408
of `refs/quasithin.pdf`, citing GLS3 §6.1. Odd index and the existence of the
radical lift are separate mathematical obligations.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open LineCore LineCore.Parabolic

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections

variable {F : Type*} [Field F] [CharP F 2] (J : HermitianForm 5 F)

/-- The radical action is literal conjugation in SU, with no projective error. -/
theorem toSU_leviAction (hJ : J.form = 1)
    (A : (middleForm J).specialSubgroup) (x : Coord J) :
    toSU J hJ (leviAction J A x) =
      leviSU J hJ A * toSU J hJ x * (leviSU J hJ A)⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  apply Subtype.ext
  apply Units.ext
  change (ambientGL J (leviAction J A x)).val * leviMatrix A.val.val =
    leviMatrix A.val.val * (ambientGL J x).val
  rw [ambientGL_val, ambientGL_val]
  exact leviMatrix_commutation J A x

/-- Multiplication of the radical and the middle block in the actual SU₅. -/
def blockMap (hJ : J.form = 1) : RadicalLevi J →* J.specialSubgroup :=
  SemidirectProduct.lift (toSU J hJ) (leviSU J hJ) (by
    intro A
    exact MonoidHom.ext (toSU_leviAction J hJ A))

@[simp] theorem blockMap_apply (hJ : J.form = 1) (x : RadicalLevi J) :
    blockMap J hJ x = toSU J hJ x.left * leviSU J hJ x.right := rfl

/-- Projectivizing recovers precisely the established parabolic embedding. -/
theorem project_comp_blockMap (hJ : J.form = 1) :
    (project J).comp (blockMap J hJ) =
      (lineParabolic J).subtype.comp (radicalLeviMap J hJ) := by
  apply MonoidHom.ext
  intro x
  exact map_mul (project J) _ _

theorem blockMap_injective (hJ : J.form = 1) :
    Function.Injective (blockMap J hJ) := by
  intro x y h
  apply radicalLeviMap_injective J hJ
  apply Subtype.ext
  exact congrArg (project J) h

/-- The subgroup over which the two local lifts will provide the section. -/
def blockSubgroup (hJ : J.form = 1) : Subgroup J.specialSubgroup :=
  (blockMap J hJ).range

noncomputable def blockEquiv (hJ : J.form = 1) :
    RadicalLevi J ≃* blockSubgroup J hJ :=
  MonoidHom.ofInjective (blockMap_injective J hJ)

/-- The remaining coordinate calculation: lift the line radical compatibly
with a prescribed lift of the actual SU₃ Levi. This is an obligation, not an
assertion that such a lift exists. -/
def HasCompatibleRadicalLift (hJ : J.form = 1)
    {E : Type*} [Group E] (f : E →* J.specialSubgroup)
    (l : (middleForm J).specialSubgroup →* E) : Prop :=
  ∃ r : Coord J →* E, f.comp r = toSU J hJ ∧
    ∀ A x, r (leviAction J A x) = l A * r x * (l A)⁻¹

/-- Compatible radical and Levi lifts produce a section of the prescribed map
over the actual matrix subgroup, not merely an abstract isomorphic group. -/
theorem exists_block_section_of_compatible_lifts (hJ : J.form = 1)
    {E : Type*} [Group E] (f : E →* J.specialSubgroup)
    (r : Coord J →* E) (l : (middleForm J).specialSubgroup →* E)
    (hr : f.comp r = toSU J hJ) (hl : f.comp l = leviSU J hJ)
    (heq : ∀ A x, r (leviAction J A x) = l A * r x * (l A)⁻¹) :
    ∃ s : blockSubgroup J hJ →* E,
      f.comp s = (blockSubgroup J hJ).subtype := by
  let t : RadicalLevi J →* E :=
    SemidirectProduct.lift r l (fun A => MonoidHom.ext (heq A))
  have ht : f.comp t = blockMap J hJ := by
    apply MonoidHom.ext
    intro x
    change f (r x.left * l x.right) = toSU J hJ x.left * leviSU J hJ x.right
    rw [map_mul]
    exact congrArg₂ (· * ·) (DFunLike.congr_fun hr x.left)
      (DFunLike.congr_fun hl x.right)
  refine ⟨t.comp (blockEquiv J hJ).symm.toMonoidHom, ?_⟩
  apply MonoidHom.ext
  intro x
  change f (t ((blockEquiv J hJ).symm x)) = x.val
  exact (DFunLike.congr_fun ht ((blockEquiv J hJ).symm x)).trans
    (congrArg Subtype.val ((blockEquiv J hJ).apply_symm_apply x))

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.FiveFourClosure.DefiningSections
