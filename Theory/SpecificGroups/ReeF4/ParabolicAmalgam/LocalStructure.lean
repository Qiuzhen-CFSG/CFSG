module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RootData
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Positive subgroups and residuals of the Ree parabolics

The root-defined positive subgroup is a two-group, so it lies in the
prime-to-two residual of either containing parabolic. The root radicals
inherit the two-group property from it. The residuals are normal relative to
their respective parabolics; no ambient normality is asserted.

These facts hold also at q=2. Identifying each residual with the fixed local
seed, calculating its quotient and radical order, and establishing the odd
index needed for Sylow maximality remain separate root-geometry calculations.
In particular O^{2′} here is not the solvable residual L∞ used in F.1.12(II).

Source: Aschbacher–Smith F.1.12(I)(5) and (II), printed pp.263–264,
`refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section

namespace ReeF4.LargeLocalSeeds

/-- The specified fixed radical is a two-group, including at the binary endpoint. -/
theorem seedRadical_isPGroup {m : ℕ} (d : LocalBlockInput m) (s : Side) :
    IsPGroup 2 (seedRadical d s) :=
  ((standardUnipotent_isPGroup d).to_le (standardRadical_le_unipotent d s)).comap_subtype

end ReeF4.LargeLocalSeeds

namespace ReeF4.Parabolics

open Subgroup LargeLocalSeeds

/-- The positive fixed subgroup inherits the proved split two-group property. -/
theorem unipotent_isPGroup (m : ℕ) : IsPGroup 2 (unipotent m) :=
  (splitUnipotent_isPGroup m).comap_of_injective (toSplitGroup m) (toSplitGroup_injective m)

theorem radical_isPGroup (m : ℕ) (s : Side) : IsPGroup 2 (radical m s) :=
  (unipotent_isPGroup m).to_le (radical_le_unipotent m s)

/-- The embedded residual O^{2′}(P_i), separate from the whole parabolic. -/
def localFactor (m : ℕ) (s : Side) : Subgroup (Model m) :=
  (primeToResidual 2 (parabolic m s)).map (parabolic m s).subtype

theorem localFactor_le_parabolic (m : ℕ) (s : Side) :
    localFactor m s ≤ parabolic m s := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

@[simp] theorem localFactor_subgroupOf (m : ℕ) (s : Side) :
    (localFactor m s).subgroupOf (parabolic m s) = primeToResidual 2 (parabolic m s) :=
  comap_map_eq_self_of_injective (parabolic m s).subtype_injective _

/-- Normality is inside P_i, not in the full Ree group. -/
instance localFactor_normal (m : ℕ) (s : Side) :
    ((localFactor m s).subgroupOf (parabolic m s)).Normal := by
  rw [localFactor_subgroupOf]
  infer_instance

/-- Every two-element of the parabolic lies in its prime-to-two residual. -/
theorem mem_localFactor_of_pow (m : ℕ) (s : Side) (x : Model m)
    (hx : x ∈ parabolic m s) (n : ℕ) (hn : x ^ (2 ^ n) = 1) :
    x ∈ localFactor m s :=
  ⟨⟨x, hx⟩, mem_primeToResidual_of_pow (n := n) (Subtype.ext hn), rfl⟩

/-- The entire specified positive subgroup lies in each local residual. -/
theorem unipotent_le_localFactor (m : ℕ) (s : Side) :
    unipotent m ≤ localFactor m s := by
  intro x hx
  obtain ⟨n, hn⟩ := unipotent_isPGroup m ⟨x, hx⟩
  apply mem_localFactor_of_pow m s x
    ((unipotent_le_borel m).trans (borel_le_parabolic m s) hx) n
  exact congrArg Subtype.val hn

theorem radical_le_localFactor (m : ℕ) (s : Side) :
    radical m s ≤ localFactor m s :=
  (radical_le_unipotent m s).trans (unipotent_le_localFactor m s)

/-- The root radical inside the residual, before identifying it with O₂. -/
def localRadical (m : ℕ) (s : Side) : Subgroup (localFactor m s) :=
  (radical m s).subgroupOf (localFactor m s)

theorem localRadical_isPGroup (m : ℕ) (s : Side) : IsPGroup 2 (localRadical m s) :=
  (radical_isPGroup m s).comap_subtype

theorem localRadical_map (m : ℕ) (s : Side) :
    (localRadical m s).map (localFactor m s).subtype = radical m s :=
  map_subgroupOf_eq_of_le (radical_le_localFactor m s)

/-- Odd index is the remaining input for Sylow maximality of the fixed positive
subgroup. This conditional construction does not assume a two-group proof. -/
def sylowOfOddIndex (m : ℕ) (hindex : Odd (unipotent m).index) : Sylow 2 (Model m) :=
  (unipotent_isPGroup m).toSylow hindex.not_two_dvd_nat

@[simp] theorem sylowOfOddIndex_coe (m : ℕ) (hindex : Odd (unipotent m).index) :
    (sylowOfOddIndex m hindex : Subgroup (Model m)) = unipotent m := rfl

end ReeF4.Parabolics
