module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.Reduction
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.SeedQuotients
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment.RootCapture
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.LinearCore.Projection
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection

/-!
# Containment of solvable Ree Sylow overgroups

Fixed Bruhat factorization reduces an overgroup of the positive Sylow subgroup
to fixed normalizer words. A word outside the Borel must generate a rank-one
seed with the positive subgroup; a surjective map from that seed to its
PSL₂ or Suzuki Levi target then contradicts solvability. Sylow conjugacy
transports the resulting containment to any ambient Sylow two-subgroup.

The assembly supplies root capture and both concrete Levi surjections from
their proved matrix constructions. For `m ≥ 1`, solvability and containment
of an ambient Sylow two-subgroup suffice. The source specialization retains
properness, simplicity and the restriction to primes two and three, although
the stronger theorem does not need them. No torus identity remains as a
premise, and the Borel is the actual root-defined `borel`.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), and F.1.12(I)(5), printed p.263.
-/

public section

namespace ReeF4.Parabolics.ThreeSylowContainment

open LargeLocalSeeds SectionGeometry.BNPair

/-- Conditional assembly retained for callers supplying their own root capture
and projections. The unconditional theorem below constructs these inputs. -/
theorem exists_conjugate_le_borel_of_root_generation_and_projections
    {m : ℕ} (hm : 1 ≤ m)
    (hcapture : ∀ n : Model m, n ∈ normalizerWords m → n ∉ borel m →
      ∃ s : Side, seed m s ≤
        unipotent m ⊔ (unipotent m).map (MulAut.conj n).toMonoidHom)
    (πL : standardSeed (canonicalLocalBlockInput m) .linear →* LinearQuotient m)
    (hπL : Function.Surjective πL)
    (πS : standardSeed (canonicalLocalBlockInput m) .suzuki →*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hπS : Function.Surjective πS)
    (U : Sylow 2 (Model m)) (K : Subgroup (Model m))
    (hK : Group.IsSolvable K) (hUK : (U : Subgroup (Model m)) ≤ K) :
    ∃ g : Model m, K.map (MulAut.conj g).toMonoidHom ≤ borel m := by
  apply exists_conjugate_le_borel_of_seed_capture hcapture _ U K hK hUK
  intro s
  cases s with
  | linear => exact linear_seed_not_isSolvable_of_surjective hm πL hπL
  | suzuki => exact suzuki_seed_not_isSolvable_of_surjective hm πS hπS

/-- Both actual fixed seeds are nonsolvable over a large Ree field, by their
surjections onto the concrete PSL₂ and Suzuki matrix groups. -/
theorem seed_not_isSolvable {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    ¬ Group.IsSolvable (seed m s) := by
  cases s with
  | linear =>
    exact linear_seed_not_isSolvable_of_surjective hm
      (LinearProjection.projection hm (canonicalLocalBlockInput m))
      (LinearProjection.projection_surjective hm (canonicalLocalBlockInput m))
  | suzuki =>
    exact suzuki_seed_not_isSolvable_of_surjective hm
      (SuzukiLeviProjection.projection (canonicalLocalBlockInput m))
      (SuzukiLeviProjection.projection_surjective (canonicalLocalBlockInput m))

/-- Every solvable overgroup of the standard positive subgroup lies in the
root Borel: a non-Borel Bruhat word would capture a nonsolvable seed. -/
theorem le_borel_of_solvable {m : ℕ} (hm : 1 ≤ m)
    (K : Subgroup (Model m)) (hK : Group.IsSolvable K) (hU : unipotent m ≤ K) :
    K ≤ borel m :=
  le_borel_of_seed_capture (RootCapture.exists_seed_le_sup_conjugate hm)
    (seed_not_isSolvable hm) K hK hU

/-- A solvable overgroup of any ambient Sylow two-subgroup is conjugate into
the root Borel. All fixed-root and Levi-projection premises are discharged. -/
theorem exists_conjugate_le_borel {m : ℕ} (hm : 1 ≤ m)
    (U : Sylow 2 (Model m)) (K : Subgroup (Model m))
    (hK : Group.IsSolvable K) (hUK : (U : Subgroup (Model m)) ≤ K) :
    ∃ g : Model m, K.map (MulAut.conj g).toMonoidHom ≤ borel m :=
  exists_conjugate_le_borel_of_seed_capture (RootCapture.exists_seed_le_sup_conjugate hm)
    (seed_not_isSolvable hm) U K hK hUK

/-- The precise proper two-and-three-prime overgroup statement used in the
Ree case of Proposition 1.3.4. The preceding stronger theorem shows that its
properness, simplicity and prime-divisor hypotheses are unnecessary here. -/
theorem exists_conjugate_le_borel_of_two_three_primes {m : ℕ} (hm : 1 ≤ m)
    [IsSimpleGroup (Model m)] (U : Sylow 2 (Model m)) (K : Subgroup (Model m))
    (hK : Group.IsSolvable K) (_hproper : K ≠ ⊤)
    (_hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card K → p = 2 ∨ p = 3)
    (hUK : (U : Subgroup (Model m)) ≤ K) :
    ∃ g : Model m, K.map (MulAut.conj g).toMonoidHom ≤ borel m :=
  exists_conjugate_le_borel hm U K hK hUK

end ReeF4.Parabolics.ThreeSylowContainment
