module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.SplitGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Opposition on the full signed fixed Ree blocks

The explicit split opposition word conjugates every root curve to its negative
with unchanged parameter. Negation preserves Levi support and reverses sign, so
it exchanges the two entire generated block subgroups. Restriction to the
supplied twist-fixed group gives the asserted equality of fixed intersections.
The same opposition exchanges the signed unipotent subgroups, their intrinsic
normalizers, and their parabolic candidates. This includes all nonsimple roots
of the B₂ block, and needs no simplicity,
perfectness, index or field-size assumption.

Source: GLS3, 2.3.6–8 and 2.4.8, with the types V and VI blocks of Table 2.4,
in `refs/KGroup/GLS3/chapter2.tex`. The matrix opposition theorem used here is
`LocalBlockInput.PairNormalization.splitOpposition_conj_root`.
-/

noncomputable section
namespace ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LocalBlockInput.PairRigidity LocalBlockInput.PairNormalization
local instance recognitionIndexNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private theorem split_opposition_map_simpleBlock (m : ℕ) (s : LargeLocalSeeds.Side)
    (positive : Bool) :
    (splitSimpleBlock m s positive).map (MulAut.conj (splitOpposition m)).toMonoidHom =
      splitSimpleBlock m s (!positive) := by
  rw [splitSimpleBlock, MonoidHom.map_closure]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨r, t, hr, rfl⟩, rfl⟩
    exact ⟨-r, t, (isSimpleBlockRoot_neg_iff s positive r).mpr hr,
      splitOpposition_conj_root m r t⟩
  · rintro ⟨r, t, hr, rfl⟩
    refine ⟨rootGeneratorInGroup m (-r) t, ⟨-r, t, ?_, rfl⟩, ?_⟩
    · simpa only [Bool.not_not] using
        (isSimpleBlockRoot_neg_iff s (!positive) r).mpr hr
    · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, neg_neg] using
        splitOpposition_conj_root m (-r) t

/-- The explicit fixed opposition element exchanges both signs of each full block. -/
public theorem standard_opposition_map_simpleBlock {m : ℕ} (d : LocalBlockInput m)
    (s : LargeLocalSeeds.Side) (positive : Bool) :
    (LocalBlockInput.PairRigidity.simpleBlock d s positive).map
      (MulAut.conj (opposition d)).toMonoidHom =
        LocalBlockInput.PairRigidity.simpleBlock d s (!positive) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change splitOpposition m * y.val * (splitOpposition m)⁻¹ ∈
      splitSimpleBlock m s (!positive)
    rw [← split_opposition_map_simpleBlock m s positive]
    exact ⟨y.val, hy, rfl⟩
  · intro x hx
    refine ⟨(opposition d)⁻¹ * x * opposition d, ?_, ?_⟩
    · have hx' : x.val ∈ splitSimpleBlock m s (!positive) := hx
      rw [← split_opposition_map_simpleBlock m s positive] at hx'
      obtain ⟨y, hy, he⟩ := hx'
      change (splitOpposition m)⁻¹ * x.val * splitOpposition m ∈
        splitSimpleBlock m s positive
      rw [← he]
      change (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
        splitOpposition m ∈ splitSimpleBlock m s positive
      have hc : (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
          splitOpposition m = y := by group
      rw [hc]
      exact hy
    · simp [MulAut.conj_apply, mul_assoc]

private theorem opposition_mul_self {m : ℕ} (d : LocalBlockInput m) :
    opposition d * opposition d = 1 := by
  apply Subtype.ext
  change splitOpposition m * splitOpposition m = 1
  simpa only [splitOpposition_inv m] using inv_mul_cancel (splitOpposition m)

private theorem map_opposition_twice {m : ℕ} (d : LocalBlockInput m)
    (H : Subgroup d.fixedGroup) :
    (H.map (MulAut.conj (opposition d)).toMonoidHom).map
      (MulAut.conj (opposition d)).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj (opposition d)).toMonoidHom.comp
      (MulAut.conj (opposition d)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change opposition d * (opposition d * x * (opposition d)⁻¹) * (opposition d)⁻¹ = x
    have hi : (opposition d)⁻¹ = opposition d := by
      exact inv_eq_of_mul_eq_one_left (opposition_mul_self d)
    rw [hi]
    calc
      _ = (opposition d * opposition d) * x * (opposition d * opposition d) := by group
      _ = x := by rw [opposition_mul_self d, one_mul, mul_one]
  rw [he, Subgroup.map_id]

public theorem standard_opposition_map_signedUnipotent {m : ℕ} (d : LocalBlockInput m)
    (positive : Bool) :
    (signedUnipotent d positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedUnipotent d (!positive) := by
  cases positive
  · change (LocalBlockInput.oppositeUnipotent d).map _ = LargeLocalSeeds.standardUnipotent d
    rw [← opposition_map_unipotent d, map_opposition_twice]
  · exact opposition_map_unipotent d

public theorem standard_opposition_map_signedBorelNormalizer {m : ℕ} (d : LocalBlockInput m)
    (positive : Bool) :
    (signedBorelNormalizer d positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedBorelNormalizer d (!positive) := by
  rw [signedBorelNormalizer, Subgroup.map_normalizer_eq_of_bijective _
    (MulAut.conj (opposition d)).bijective, standard_opposition_map_signedUnipotent]
  rfl

public theorem standard_opposition_map_signedParabolic {m : ℕ} (d : LocalBlockInput m)
    (s : LargeLocalSeeds.Side) (positive : Bool) :
    (signedParabolic d s positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedParabolic d s (!positive) := by
  rw [signedParabolic, Subgroup.map_sup, standard_opposition_map_signedBorelNormalizer,
    standard_opposition_map_simpleBlock]
  rfl

end ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.LocalActions
