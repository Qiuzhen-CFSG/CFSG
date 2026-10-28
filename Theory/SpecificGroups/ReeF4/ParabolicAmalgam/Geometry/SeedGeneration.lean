module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.Targets
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.LinearWitness
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.SeedGeneration.SuzukiWitness
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.Radicals
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.LinearProjection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Projection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection

/-!
# Positive normal generation in the fixed Ree seeds

The root radical is contained in the positive subgroup. A concrete surjective
Levi projection therefore reduces positive normal generation to normal
generation in its target: the kernel already lies in the normal closure, and
a full image forces that closure to be the entire seed.

For the linear side, the explicit end-root witness in `LinearWitness` proves
that the positive image is nontrivial. For the Suzuki side, `SuzukiWitness`
and the proved B₂ matrix swap give a positive element whose square survives
the radical. `Targets` proves the required target statements for every
parameter, including the solvable groups PSL₂(2) and Sz(2). The comparison
with standard fixed seeds preserves the exact root kernel.

The final theorem supplies the concrete binary projections at m = 0 and the
standard fixed-seed projections at positive m, discharging every premise of
the retained conditional reductions. Normality is always inside the fixed
seed. No ambient Ree simplicity, residual equality, or preservation of split
generation by fixed points is used.

Source: the local Levi structure in Aschbacher–Smith F.1.12(I)(5), printed
pp.263–264 of `refs/quasithin.pdf`. At m = 0 this concerns the full ²F₄(2),
not the distinct Tits case F.1.12(I)(9).
-/

public section

namespace ReeF4.Parabolics
open Subgroup LargeLocalSeeds

private theorem eq_top_of_map_eq_top_of_ker_le {G H : Type*} [Group G] [Group H]
    (f : G →* H) (N : Subgroup G) (hN : N.map f = ⊤) (hker : f.ker ≤ N) :
    N = ⊤ := by
  have h := congrArg (Subgroup.comap f) hN
  simpa only [comap_map_eq, comap_top, sup_eq_left.mpr hker] using h

/-- Positive normal generation in the linear seed follows from a concrete
surjective Levi projection with the specified root kernel. -/
theorem positive_normalClosure_eq_top_of_linear_projection (m : ℕ)
    (f : seed m .linear →* LinearQuotient m)
    (hf : Function.Surjective f) (hker : f.ker = radicalInSeed m .linear) :
    normalClosure ((unipotent m).subgroupOf (seed m .linear) :
      Set (seed m .linear)) = ⊤ := by
  let U := (unipotent m).subgroupOf (seed m .linear)
  let N := normalClosure (U : Set (seed m .linear))
  have hUN : U ≤ N := subset_normalClosure
  have hRN : radicalInSeed m .linear ≤ N :=
    fun x hx => hUN (radical_le_unipotent m .linear hx)
  have hne : U.map f ≠ ⊥ := by
    intro he
    have hle : U ≤ radicalInSeed m .linear := hker ▸ (map_eq_bot_iff U).mp he
    apply SeedGeneration.unipotent_not_le_linear_radical m
    intro x hx
    exact hle (show (⟨x, unipotent_le_seed m .linear hx⟩ : seed m .linear) ∈ U from hx)
  let := (inferInstance : N.Normal).map f hf
  have hmap : N.map f = ⊤ := SeedGeneration.linear_normal_eq_top m (N.map f)
    (U.map f) ((unipotent_isPGroup m).comap_subtype.map f) (map_mono hUN) hne
  exact eq_top_of_map_eq_top_of_ker_le f N hmap (hker ▸ hRN)

/-- A positive fixed element whose square survives the radical supplies the
Suzuki-side normal generation, including the full binary group. The projection
and the surviving square are explicit root-calculation inputs. -/
theorem positive_normalClosure_eq_top_of_suzuki_projection (m : ℕ)
    (f : seed m .suzuki →* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hf : Function.Surjective f) (hker : f.ker = radicalInSeed m .suzuki)
    (hsquare : ∃ x ∈ unipotent m, x ^ 2 ∉ radical m .suzuki) :
    normalClosure ((unipotent m).subgroupOf (seed m .suzuki) :
      Set (seed m .suzuki)) = ⊤ := by
  let U := (unipotent m).subgroupOf (seed m .suzuki)
  let N := normalClosure (U : Set (seed m .suzuki))
  have hUN : U ≤ N := subset_normalClosure
  have hRN : radicalInSeed m .suzuki ≤ N :=
    fun x hx => hUN (radical_le_unipotent m .suzuki hx)
  obtain ⟨x, hx, hx2⟩ := hsquare
  let y : seed m .suzuki := ⟨x, unipotent_le_seed m .suzuki hx⟩
  have hy2 : f y ^ 2 ≠ 1 := by
    intro he
    have hk : y ^ 2 ∈ f.ker := by rwa [MonoidHom.mem_ker, map_pow]
    have hr : y ^ 2 ∈ radicalInSeed m .suzuki := hker ▸ hk
    exact hx2 hr
  let := (inferInstance : N.Normal).map f hf
  have hmap : N.map f = ⊤ := SeedGeneration.suzuki_normal_eq_top m (N.map f)
    (U.map f) ((unipotent_isPGroup m).comap_subtype.map f) (map_mono hUN)
    ⟨f y, mem_map_of_mem f hx, hy2⟩
  exact eq_top_of_map_eq_top_of_ker_le f N hmap (hker ▸ hRN)

/-- The matrix-preserving fixed-seed equivalence transports a projection without
changing its specified root kernel. -/
private theorem transported_projection_ker {m : ℕ} (s : Side)
    {H : Type*} [Group H]
    (f : standardSeed (canonicalLocalBlockInput m) s →* H)
    (hker : f.ker = seedRadical (canonicalLocalBlockInput m) s) :
    (f.comp (seedEquiv m s).symm.toMonoidHom).ker = radicalInSeed m s := by
  rw [← MonoidHom.comap_ker, hker, ← radicalInSeed_comap_seedEquiv, comap_comap]
  simp

/-- The linear quotient may be supplied on the existing standard fixed seed. -/
theorem positive_normalClosure_eq_top_of_standard_linear_projection (m : ℕ)
    (f : standardSeed (canonicalLocalBlockInput m) .linear →* LinearQuotient m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical (canonicalLocalBlockInput m) .linear) :
    normalClosure ((unipotent m).subgroupOf (seed m .linear) :
      Set (seed m .linear)) = ⊤ :=
  positive_normalClosure_eq_top_of_linear_projection m
    (f.comp (seedEquiv m .linear).symm.toMonoidHom)
    (hf.comp (seedEquiv m .linear).symm.surjective)
    (transported_projection_ker .linear f hker)

/-- The Suzuki quotient may be supplied on the existing standard fixed seed. -/
theorem positive_normalClosure_eq_top_of_standard_suzuki_projection (m : ℕ)
    (f : standardSeed (canonicalLocalBlockInput m) .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hf : Function.Surjective f)
    (hker : f.ker = seedRadical (canonicalLocalBlockInput m) .suzuki)
    (hsquare : ∃ x ∈ unipotent m, x ^ 2 ∉ radical m .suzuki) :
    normalClosure ((unipotent m).subgroupOf (seed m .suzuki) :
      Set (seed m .suzuki)) = ⊤ :=
  positive_normalClosure_eq_top_of_suzuki_projection m
    (f.comp (seedEquiv m .suzuki).symm.toMonoidHom)
    (hf.comp (seedEquiv m .suzuki).symm.surjective)
    (transported_projection_ker .suzuki f hker) hsquare

/-- The positive fixed subgroup normally generates each fixed Ree seed.
The normal closure is taken inside that seed, for every parameter including
the full binary Ree group at m = 0. -/
theorem positive_normalClosure_eq_top (m : ℕ) (s : Side) :
    normalClosure ((unipotent m).subgroupOf (seed m s) : Set (seed m s)) = ⊤ := by
  cases s with
  | suzuki =>
    have hsquare := SeedGeneration.exists_unipotent_square_not_mem_suzuki_radical m
      (RadicalCoordinates.FixedCoordinates.b2RootSwap m)
    cases m with
    | zero =>
      exact positive_normalClosure_eq_top_of_suzuki_projection 0
        BinarySuzuki.projection BinarySuzuki.projection_surjective
        BinarySuzuki.projection_ker hsquare
    | succ n =>
      exact positive_normalClosure_eq_top_of_standard_suzuki_projection (n + 1)
        (SuzukiLeviProjection.projection (canonicalLocalBlockInput (n + 1)))
        (SuzukiLeviProjection.projection_surjective (canonicalLocalBlockInput (n + 1)))
        (SuzukiLeviProjection.projection_ker (canonicalLocalBlockInput (n + 1))) hsquare
  | linear =>
    cases m with
    | zero =>
      exact positive_normalClosure_eq_top_of_linear_projection 0
        BinaryLinear.projection BinaryLinear.projection_surjective BinaryLinear.projection_ker
    | succ n =>
      exact positive_normalClosure_eq_top_of_standard_linear_projection (n + 1)
        (LinearProjection.projection (Nat.succ_pos n) (canonicalLocalBlockInput (n + 1)))
        (LinearProjection.projection_surjective (Nat.succ_pos n)
          (canonicalLocalBlockInput (n + 1)))
        (LinearProjection.projection_ker (Nat.succ_pos n) (canonicalLocalBlockInput (n + 1)))

end ReeF4.Parabolics
