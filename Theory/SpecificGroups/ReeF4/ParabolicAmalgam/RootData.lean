module

public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.RootSubgroups

/-!
# Root-defined parabolics in the concrete Ree group

Adjoin all coroot torus words to the positive subgroup and to each of the two
root-generated local seeds. The exceptional field twist preserves the resulting
split Borel and parabolic subgroups. Their intersections with the actual fixed
subgroup `Model m` define the finite Borel and marked parabolic candidates.
The middle nodes give the Suzuki side; the end nodes give the linear side.

The torus words become identity at `m = 0`, so the binary Borel is exactly the
positive fixed subgroup and the binary parabolics are the existing fixed seeds.
This endpoint is the full fixed group ²F₄(2), not its Tits derived subgroup.
Exact Borel intersection, Sylow maximality and local Levi calculations are
separate obligations; twist stability alone does not establish them.

Source: Aschbacher–Smith, F.1.4–5 and F.1.12(I)(5), printed pp.260,263–264,
`refs/quasithin.pdf`; the root and coroot construction is Steinberg's standard
Chevalley construction with the exceptional F₄ field twist.
-/

@[expose] public section
noncomputable section

namespace ReeF4.Parabolics

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup

noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- The field map in the Ree twist on a specified root. -/
def rootFieldEnd (m : ℕ) (r : F4Chevalley.Root) :
    CoefficientField m →+* CoefficientField m := by
  classical
  exact if IsLongRoot r then iterateFrobenius (CoefficientField m) 2 m else titsEnd m

theorem rootFieldEnd_apply (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    rootFieldEnd m r t = exceptionalParameter r (t ^ (2 ^ m)) := by
  classical
  by_cases hr : IsLongRoot r
  · simp [rootFieldEnd, hr, exceptionalParameter_of_long hr, iterateFrobenius_def]
  · simp only [rootFieldEnd, if_neg hr, exceptionalParameter_of_short hr, titsEnd_apply]
    rw [← pow_mul, ← pow_succ]

@[simp] theorem rootFieldEnd_neg (m : ℕ) (r : F4Chevalley.Root) :
    rootFieldEnd m (-r) = rootFieldEnd m r := by
  classical
  simp only [rootFieldEnd, isLongRoot_neg_iff]

/-- A rank-one Weyl word in the actual split matrix carrier. -/
def weylWord (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) : SplitGroup m :=
  rootGeneratorInGroup m r t * rootGeneratorInGroup m (-r) (-t⁻¹) *
    rootGeneratorInGroup m r t

/-- A coroot torus word; its parameter is required to be nonzero. -/
def torusWord (m : ℕ) (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ) : SplitGroup m :=
  weylWord m r t * weylWord m r (-1)

theorem reeTwist_weylWord (m : ℕ) (r : F4Chevalley.Root) (t : CoefficientField m) :
    reeTwist m (weylWord m r t) =
      weylWord m (exceptionalRootPermutation r) (rootFieldEnd m r t) := by
  simp only [weylWord, map_mul, reeTwist_rootGenerator, ← rootFieldEnd_apply,
    rootFieldEnd_neg, exceptionalRootPermutation_neg, map_neg, map_inv₀]

theorem reeTwist_torusWord (m : ℕ) (r : F4Chevalley.Root)
    (t : (CoefficientField m)ˣ) :
    reeTwist m (torusWord m r t) =
      torusWord m (exceptionalRootPermutation r) (Units.map (rootFieldEnd m r) t) := by
  simp only [torusWord, map_mul, reeTwist_weylWord, map_neg, map_one]
  rfl

/-- All coroot words generate the split torus. -/
def splitTorus (m : ℕ) : Subgroup (SplitGroup m) :=
  closure {x | ∃ r t, x = torusWord m r t}

def splitBorel (m : ℕ) : Subgroup (SplitGroup m) :=
  splitUnipotent m ⊔ splitTorus m

/-- The complementary torus is present in the full parabolic. -/
def splitParabolic (m : ℕ) (s : Side) : Subgroup (SplitGroup m) :=
  splitSeed m s ⊔ splitTorus m

private theorem twist_map_eq_of_le (m : ℕ) (H : Subgroup (SplitGroup m))
    (hH : H.map (reeAutomorphism m).toMonoidHom ≤ H) : H.map (reeAutomorphism m).toMonoidHom = H := by
  apply le_antisymm hH
  intro x hx
  refine ⟨reeAutomorphism m x, hH (mem_map_of_mem _ hx), ?_⟩
  simpa only [MulEquiv.coe_toMonoidHom, reeAutomorphism_apply] using reeTwist_involutive m x

theorem splitTorus_invariant (m : ℕ) :
    (splitTorus m).map (reeAutomorphism m).toMonoidHom = splitTorus m := by
  apply twist_map_eq_of_le
  rw [map_le_iff_le_comap]
  apply (closure_le _).mpr
  rintro x ⟨r, t, rfl⟩
  change reeAutomorphism m (torusWord m r t) ∈ splitTorus m
  rw [reeAutomorphism_apply]
  exact subset_closure ⟨_, _, reeTwist_torusWord m r t⟩

theorem splitBorel_invariant (m : ℕ) :
    (splitBorel m).map (reeAutomorphism m).toMonoidHom = splitBorel m := by
  rw [splitBorel, Subgroup.map_sup, splitTorus_invariant]
  congr 1
  rw [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism]
  exact splitUnipotent_twist _

theorem splitParabolic_invariant (m : ℕ) (s : Side) :
    (splitParabolic m s).map (reeAutomorphism m).toMonoidHom = splitParabolic m s := by
  rw [splitParabolic, Subgroup.map_sup, splitTorus_invariant]
  congr 1
  rw [← (canonicalLocalBlockInput m).twist_eq_reeAutomorphism]
  exact splitSeed_twist _ _

/-- The fixed positive subgroup, not yet asserted to be Sylow. -/
def unipotent (m : ℕ) : Subgroup (Model m) :=
  (splitUnipotent m).comap (toSplitGroup m)

/-- The fixed root Borel, defined independently of the parabolic intersection. -/
def borel (m : ℕ) : Subgroup (Model m) :=
  (splitBorel m).comap (toSplitGroup m)

def parabolic (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitParabolic m s).comap (toSplitGroup m)

/-- The local seed without the complementary torus. -/
def seed (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitSeed m s).comap (toSplitGroup m)

/-- The root-defined radical, independently of the intrinsic two-core. -/
def radical (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (splitRadical m s).comap (toSplitGroup m)

theorem unipotent_le_borel (m : ℕ) : unipotent m ≤ borel m :=
  comap_mono le_sup_left

theorem borel_le_parabolic (m : ℕ) (s : Side) : borel m ≤ parabolic m s :=
  comap_mono (sup_le_sup_right (splitUnipotent_le_splitSeed m s) _)

theorem seed_le_parabolic (m : ℕ) (s : Side) : seed m s ≤ parabolic m s :=
  comap_mono le_sup_left

theorem unipotent_le_seed (m : ℕ) (s : Side) : unipotent m ≤ seed m s :=
  comap_mono (splitUnipotent_le_splitSeed m s)

theorem radical_le_unipotent (m : ℕ) (s : Side) : radical m s ≤ unipotent m :=
  comap_mono (splitRadical_le_unipotent m s)

/-- The inverse comparison also preserves the ambient split matrices. -/
theorem modelEquiv_symm_coe {m : ℕ} (d : LocalBlockInput m) (x : Model m) :
    (d.modelEquiv.symm x).val = x.val := by
  simpa only [MulEquiv.apply_symm_apply] using
    (d.modelEquiv_coe (d.modelEquiv.symm x)).symm

/-- The comparison with existing fixed seeds preserves the ambient matrices. -/
def seedEquiv (m : ℕ) (s : Side) :
    standardSeed (canonicalLocalBlockInput m) s ≃* seed m s where
  toFun x := ⟨(canonicalLocalBlockInput m).modelEquiv x.val, by
    change toSplitGroup m ((canonicalLocalBlockInput m).modelEquiv x.val) ∈ splitSeed m s
    rw [toSplitGroup_apply, LocalBlockInput.modelEquiv_coe]
    exact x.property⟩
  invFun x := ⟨(canonicalLocalBlockInput m).modelEquiv.symm x.val, by
    change ((canonicalLocalBlockInput m).modelEquiv.symm x.val).val ∈ splitSeed m s
    rw [modelEquiv_symm_coe]
    simpa only [seed, mem_comap, toSplitGroup_apply] using x.property⟩
  left_inv x := Subtype.ext ((canonicalLocalBlockInput m).modelEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext ((canonicalLocalBlockInput m).modelEquiv.apply_symm_apply x.val)
  map_mul' x y := Subtype.ext ((canonicalLocalBlockInput m).modelEquiv.map_mul x.val y.val)

@[simp] theorem seedEquiv_coe (m : ℕ) (s : Side)
    (x : standardSeed (canonicalLocalBlockInput m) s) :
    toSplitGroup m (seedEquiv m s x) = x.val.val := by
  exact (toSplitGroup_apply m _).trans ((canonicalLocalBlockInput m).modelEquiv_coe x.val)

private theorem rootGenerator_sq (m : ℕ) (r : F4Chevalley.Root)
    (t : CoefficientField m) : rootGeneratorInGroup m r t ^ 2 = 1 := by
  apply Subtype.ext
  change F4Chevalley.rootCurve r t ^ 2 = 1
  rw [pow_two, ← F4Chevalley.rootCurve_add, CharTwo.add_self_eq_zero,
    F4Chevalley.rootCurve_zero]

private theorem sandwich_sq {G : Type*} [Group G] (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) : (a * b * a) ^ 2 = 1 := by
  calc
    (a * b * a) ^ 2 = a * b * (a * a) * b * a := by simp only [pow_two, mul_assoc]
    _ = 1 := by rw [ha, mul_one, mul_assoc a b b, hb, mul_one, ha]

private theorem weylWord_one_sq (m : ℕ) (r : F4Chevalley.Root) :
    weylWord m r 1 ^ 2 = 1 := by
  simp only [weylWord, inv_one]
  exact sandwich_sq _ _
    (by simpa only [pow_two] using rootGenerator_sq m r 1)
    (by simpa only [pow_two] using rootGenerator_sq m (-r) (-1))

private theorem binary_unit_eq_one (t : (CoefficientField 0)ˣ) : t = 1 := by
  have ht : (t.val : CoefficientField 0) = 0 ∨ t.val = 1 := by
    apply eq_zero_or_one_of_sq_eq_self
    simpa using field_pow 0 t.val
  exact Units.ext (ht.resolve_left t.ne_zero)

/-- At q=2 every coroot torus word is identity in the actual split carrier. -/
@[simp] theorem torusWord_zero (r : F4Chevalley.Root) (t : (CoefficientField 0)ˣ) :
    torusWord 0 r t = 1 := by
  rw [binary_unit_eq_one t]
  have hneg : (-1 : CoefficientField 0) = 1 := CharTwo.neg_eq _
  simpa only [torusWord, Units.val_one, hneg, ← pow_two] using weylWord_one_sq 0 r

@[simp] theorem splitTorus_zero : splitTorus 0 = ⊥ := by
  apply le_antisymm _ bot_le
  apply (closure_le _).mpr
  rintro x ⟨r, t, rfl⟩
  exact mem_bot.mpr (torusWord_zero r t)

@[simp] theorem splitBorel_zero : splitBorel 0 = splitUnipotent 0 := by
  simp [splitBorel]

@[simp] theorem splitParabolic_zero (s : Side) : splitParabolic 0 s = splitSeed 0 s := by
  simp [splitParabolic]

@[simp] theorem borel_zero : borel 0 = unipotent 0 := by
  simp [borel, unipotent]

@[simp] theorem parabolic_zero (s : Side) : parabolic 0 s = seed 0 s := by
  simp [parabolic, seed]

end ReeF4.Parabolics
