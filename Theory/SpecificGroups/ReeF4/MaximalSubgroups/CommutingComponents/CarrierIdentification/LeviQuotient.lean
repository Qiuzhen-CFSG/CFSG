module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration

/-!
# Restricting a Ree seed projection to its fixed Levi

Every element of a fixed seed has a unique Levi–radical expression. Hence a
surjective homomorphism whose kernel is the specified radical restricts to an
isomorphism on the fixed Levi: separation proves injectivity, and deleting
the radical factor proves surjectivity.

The radical is normal inside the seed by restriction of split normality.
Applying the construction to its quotient map identifies the fixed Levi with
the actual seed quotient, without any Suzuki identification or simplicity
assumption. The construction works on both sides and at every parameter.

Source: GLS3, 2.3.4–8 and §2.4, `refs/KGroup/GLS3/chapter2.tex`, for the
fixed Levi decomposition underlying Aschbacher–Smith F.1.12, pp.263–264.
-/

public noncomputable section

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

open Subgroup LargeLocalSeeds
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration

variable {m : ℕ}

/-- Inclusion of the full fixed subsystem Levi into its fixed seed. -/
def fixedLeviInclusion (d : LocalBlockInput m) (s : Side) :
    fixedLevi d s →* standardSeed d s :=
  inclusion (fixedLevi_le_seed d s)

/-- A seed projection with precisely the root-defined radical as kernel is
bijective on the fixed Levi. No model identification is assumed here. -/
theorem restrictedProjection_bijective (d : LocalBlockInput m) (s : Side)
    {H : Type*} [Group H] (π : standardSeed d s →* H)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d s) :
    Function.Bijective (π.comp (fixedLeviInclusion d s)) := by
  constructor
  · apply (injective_iff_map_eq_one (π.comp (fixedLeviInclusion d s))).mpr
    intro x hx
    have hr : fixedLeviInclusion d s x ∈ seedRadical d s :=
      hker ▸ (show fixedLeviInclusion d s x ∈ π.ker from hx)
    have he : x.val.val = 1 :=
      disjoint_def.mp (splitLevi_disjoint_splitRadical m s) x.property hr
    exact Subtype.ext (Subtype.ext he)
  · intro y
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨l, hl, r, hr, he⟩ := exists_fixed_levi_radical_factors d s x.val x.property
    let l' : fixedLevi d s := ⟨l, hl⟩
    let r' : standardSeed d s := ⟨r, standardRadical_le_seed d s hr⟩
    have hr' : π r' = 1 := by
      apply π.mem_ker.mp
      rw [hker]
      exact hr
    have he' : fixedLeviInclusion d s l' * r' = x := Subtype.ext he
    refine ⟨l', ?_⟩
    change π (fixedLeviInclusion d s l') = π x
    calc
      π (fixedLeviInclusion d s l') = π (fixedLeviInclusion d s l') * 1 := (mul_one _).symm
      _ = π (fixedLeviInclusion d s l') * π r' := congrArg _ hr'.symm
      _ = π (fixedLeviInclusion d s l' * r') := (π.map_mul _ _).symm
      _ = π x := congrArg π he'

/-- The equivalence is the given projection restricted to the actual Levi. -/
def fixedLeviEquivOfProjection (d : LocalBlockInput m) (s : Side)
    {H : Type*} [Group H] (π : standardSeed d s →* H)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d s) :
    fixedLevi d s ≃* H :=
  MulEquiv.ofBijective (π.comp (fixedLeviInclusion d s))
    (restrictedProjection_bijective d s π hπ hker)

@[simp] theorem fixedLeviEquivOfProjection_apply (d : LocalBlockInput m) (s : Side)
    {H : Type*} [Group H] (π : standardSeed d s →* H)
    (hπ : Function.Surjective π) (hker : π.ker = seedRadical d s)
    (x : fixedLevi d s) :
    fixedLeviEquivOfProjection d s π hπ hker x = π (fixedLeviInclusion d s x) := by rfl

/-- Normality of the specified radical is relative to the fixed seed. -/
theorem seedRadical_normal (d : LocalBlockInput m) (s : Side) :
    (seedRadical d s).Normal := by
  let f : standardSeed d s →* splitSeed m s :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let := radicalInSplitSeed_normal m s
  change ((radicalInSplitSeed m s).comap f).Normal
  infer_instance

/-- The fixed Levi is the quotient of its seed by the specified radical. -/
def fixedLeviEquivSeedQuotient (d : LocalBlockInput m) (s : Side) :
    letI := seedRadical_normal d s
    fixedLevi d s ≃* (standardSeed d s ⧸ seedRadical d s) := by
  letI := seedRadical_normal d s
  exact fixedLeviEquivOfProjection d s (QuotientGroup.mk' (seedRadical d s))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

@[simp] theorem fixedLeviEquivSeedQuotient_apply (d : LocalBlockInput m) (s : Side)
    (x : fixedLevi d s) :
    letI := seedRadical_normal d s
    fixedLeviEquivSeedQuotient d s x =
      QuotientGroup.mk' (seedRadical d s) (fixedLeviInclusion d s x) := by rfl

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
