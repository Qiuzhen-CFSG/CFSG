module

public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup

/-!
# Full parabolics in the concrete Ree carrier

Adjoin all split torus words to each of the two root-generated local seeds,
then intersect with the exceptional-twist fixed subgroup `Model m`. The torus
word is the usual `h_r(t) = n_r(t) n_r(1)⁻¹`, expressed in the actual F₄ root
matrices. In particular these subgroups include the complementary torus omitted
by `LargeLocalSeeds.standardSeed`.

The radicals are the fixed intersections of the existing positive root
radicals. Their two-group property follows from the proved unitriangular
calculation, independently of any quotient or normality calculation. This
module defines the concrete subgroups and proves containments only: normalizer
coverage, Levi projections, and radical centralizers remain separate results.

Sources: GLS3, §§2.3–2.4 (`refs/KGroup/GLS3/chapter2.tex`), and the Ree case of
Aschbacher–Smith, Theorem 0.1.2(1), printed p.4, with the local factors of
F.1.12(I)(5), printed p.263 (`refs/quasithin.pdf`). The field size is always
`2^(2*m+1)`; the simple-family application requires `1 ≤ m`.
-/

@[expose] public noncomputable section

namespace ReeF4.ConverseParabolics

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds

local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The standard rank-one Weyl word in the concrete split matrix group. -/
def weylWord (m : ℕ) (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    SplitGroup m :=
  rootGeneratorInGroup m r t * rootGeneratorInGroup m (-r) (-(t.val)⁻¹) *
    rootGeneratorInGroup m r t

/-- The split torus word associated to a root and a nonzero field parameter. -/
def torusWord (m : ℕ) (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) :
    SplitGroup m := weylWord m r t * (weylWord m r 1)⁻¹

/-- All split torus words, including those outside either selected Levi. -/
def splitTorus (m : ℕ) : Subgroup (SplitGroup m) :=
  closure {x | ∃ r t, x = torusWord m r t}

/-- The full split parabolic associated to the selected orbit of simple roots. -/
def splitParabolic (m : ℕ) (s : Side) : Subgroup (SplitGroup m) :=
  splitTorus m ⊔ splitSeed m s

/-- The full parabolic as an actual subgroup of the Ree fixed-point carrier. -/
def parabolic (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitParabolic m s).subgroupOf (fixedSubgroup m)

/-- The positive fixed subgroup, with no Sylow assertion built into its definition. -/
def unipotent (m : ℕ) : Subgroup (Model m) :=
  (splitUnipotent m).subgroupOf (fixedSubgroup m)

/-- The specified positive root radical inside the actual Ree carrier. -/
def radical (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitRadical m s).subgroupOf (fixedSubgroup m)

/-- The root radical viewed inside its full parabolic, not defined by `pCore`. -/
def intrinsicRadical (m : ℕ) (s : Side) : Subgroup (parabolic m s) :=
  (radical m s).subgroupOf (parabolic m s)

theorem unipotent_le_parabolic (m : ℕ) (s : Side) :
    unipotent m ≤ parabolic m s := by
  intro x hx
  exact (show splitSeed m s ≤ splitParabolic m s from le_sup_right)
    (splitUnipotent_le_splitSeed m s hx)

theorem radical_le_unipotent (m : ℕ) (s : Side) :
    radical m s ≤ unipotent m :=
  fun _ hx => splitRadical_le_unipotent m s hx

theorem radical_le_parabolic (m : ℕ) (s : Side) :
    radical m s ≤ parabolic m s :=
  (radical_le_unipotent m s).trans (unipotent_le_parabolic m s)

theorem intrinsicRadical_map (m : ℕ) (s : Side) :
    (intrinsicRadical m s).map (parabolic m s).subtype = radical m s :=
  map_subgroupOf_eq_of_le (radical_le_parabolic m s)

theorem unipotent_isPGroup (m : ℕ) : IsPGroup 2 (unipotent m) :=
  (splitUnipotent_isPGroup m).comap_of_injective
    (fixedSubgroup m).subtype Subtype.val_injective

theorem radical_isPGroup (m : ℕ) (s : Side) : IsPGroup 2 (radical m s) :=
  (unipotent_isPGroup m).of_injective (inclusion (radical_le_unipotent m s))
    (inclusion_injective _)

theorem intrinsicRadical_isPGroup (m : ℕ) (s : Side) :
    IsPGroup 2 (intrinsicRadical m s) :=
  (radical_isPGroup m s).comap_of_injective
    (parabolic m s).subtype Subtype.val_injective

private theorem fixedIntersection_map {m : ℕ} (d : LocalBlockInput m)
    (H : Subgroup (SplitGroup m)) :
    (H.subgroupOf d.fixedGroup).map d.modelEquiv.toMonoidHom =
      H.subgroupOf (fixedSubgroup m) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change (d.modelEquiv y : SplitGroup m) ∈ H
    rwa [LocalBlockInput.modelEquiv_coe]
  · intro hx
    refine ⟨d.modelEquiv.symm x, ?_, d.modelEquiv.apply_symm_apply x⟩
    change (d.modelEquiv.symm x : SplitGroup m) ∈ H
    rw [← LocalBlockInput.modelEquiv_coe, d.modelEquiv.apply_symm_apply]
    exact hx

/-- The positive subgroup is exactly the one used by the existing fixed geometry. -/
theorem standardUnipotent_map_eq {m : ℕ} (d : LocalBlockInput m) :
    (standardUnipotent d).map d.modelEquiv.toMonoidHom = unipotent m :=
  fixedIntersection_map d (splitUnipotent m)

/-- The radicals agree with the existing root seeds under the actual matrix equivalence. -/
theorem standardRadical_map_eq {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    (standardRadical d s).map d.modelEquiv.toMonoidHom = radical m s :=
  fixedIntersection_map d (splitRadical m s)

/-- The existing seed embeds in the full parabolic by the proved model comparison. -/
theorem seed_map_le_parabolic {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    (standardSeed d s).map d.modelEquiv.toMonoidHom ≤ parabolic m s := by
  rintro x ⟨y, hy, rfl⟩
  change (d.modelEquiv y : SplitGroup m) ∈ splitParabolic m s
  rw [LocalBlockInput.modelEquiv_coe]
  exact (show splitSeed m s ≤ splitParabolic m s from le_sup_right) hy

end ReeF4.ConverseParabolics
