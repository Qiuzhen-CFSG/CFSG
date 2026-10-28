module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Commutators
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Linear

/-!
# Marked quotient sections for the higher MS93 layers

The records specify surjections from the actual subgroups, with their exact
relative kernels and ambient conjugation action. Every action uses the same
marking as CommonFacts.natural. Publishing a record does not construct it.

A nonzero invariant subgroup of the dual three-space is the whole space:
the actual SL3(2) action is transitive on its nonzero vectors. The resulting
lifting theorem is the saturation step used for (4.5.5).

Source audit: (4.5.4)(iv), printed p.898, says "dual to U". The proof on
p.899 instead says "isomorphic to U", agreeing with (4.5)(vii), p.895.
The pair-section record distinguishes the two literal actions. The moving
quotient in the intended assembly must use the natural action; its witness
still has to be constructed from the commutator calculations.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
open DistanceFour.Linear
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  (source : LocalSource L R) (common : CommonFacts R source geometry)

/-- A single dual natural section, with the literal source action and kernel. -/
structure MarkedDualSection (A N : Subgroup (FreeAmalgam R)) where
  local_group : A ≤ stabilizer R (alpha R)
  lower_le : N ≤ A
  normalized : Mbar R ≤ normalizer A
  quotient : A →* Multiplicative W
  onto : Function.Surjective quotient
  kernel : quotient.ker = N.subgroupOf A
  action : ∀ (m : M) (x y : A),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd =
      dual (common.natural.marking (source.projection m)) (quotient x).toAdd

/-- Two actual natural or dual factors. `isDual` selects inverse transpose,
not an unmarked abstract group-family identification. -/
structure MarkedPairSection (A N : Subgroup (FreeAmalgam R)) (isDual : Bool) where
  local_group : A ≤ stabilizer R (alpha R)
  lower_le : N ≤ A
  normalized : Mbar R ≤ normalizer A
  quotient : A →* Multiplicative (W × W)
  onto : Function.Surjective quotient
  kernel : quotient.ker = N.subgroupOf A
  action : ∀ (m : M) (x y : A),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (quotient y).toAdd =
      if isDual then
        (dual (common.natural.marking (source.projection m)) (quotient x).toAdd.1,
         dual (common.natural.marking (source.projection m)) (quotient x).toAdd.2)
      else
        ((common.natural.marking (source.projection m)).val.mulVec (quotient x).toAdd.1,
         (common.natural.marking (source.projection m)).val.mulVec (quotient x).toAdd.2)

variable {source common}

/-- Any invariant subgroup with nonzero image fills a marked dual section.
This is the nontrivial step from the local commutator estimates to equality
modulo Z in (4.5.5). -/
theorem MarkedDualSection.sup_eq_of_not_le
    {A N D : Subgroup (FreeAmalgam R)} (s : MarkedDualSection source common A N)
    (hDA : D ≤ A) (hD : Mbar R ≤ normalizer D) (hnon : ¬ D ≤ N) : D ⊔ N = A := by
  classical
  obtain ⟨x, hxD, hxN⟩ : ∃ x, x ∈ D ∧ x ∉ N := Set.not_subset.mp hnon
  let u : A := ⟨x, hDA hxD⟩
  have hu : (s.quotient u).toAdd ≠ 0 := by
    intro h
    apply hxN
    have hker : u ∈ s.quotient.ker := MonoidHom.mem_ker.mpr
      (Multiplicative.toAdd.injective h)
    rw [s.kernel] at hker
    exact hker
  apply le_antisymm (sup_le hDA s.lower_le)
  intro y hy
  let v : A := ⟨y, hy⟩
  by_cases hv : (s.quotient v).toAdd = 0
  · apply mem_sup_right
    have hker : v ∈ s.quotient.ker := MonoidHom.mem_ker.mpr
      (Multiplicative.toAdd.injective hv)
    rw [s.kernel] at hker
    exact hker
  · obtain ⟨g, hg⟩ := dual_orbit hu hv
    obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
    have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
    have hmbar : embedM R m ∈ Mbar R := ⟨m, rfl⟩
    have hzD : embedM R m * x * (embedM R m)⁻¹ ∈ D :=
      le_normalizer_iff.mp hD _ hmbar _ hxD
    let z : A := ⟨embedM R m * x * (embedM R m)⁻¹, hDA hzD⟩
    have hz : s.quotient z = s.quotient v := by
      apply Multiplicative.toAdd.injective
      rw [s.action m u z rfl, hmg]
      exact hg
    have hvz : v * z⁻¹ ∈ s.quotient.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hz, mul_inv_cancel]
    rw [s.kernel] at hvz
    have hprod := (D ⊔ N).mul_mem (mem_sup_right hvz) (mem_sup_left hzD)
    change y * (z : FreeAmalgam R)⁻¹ * (z : FreeAmalgam R) ∈ D ⊔ N at hprod
    simpa only [inv_mul_cancel_right] using hprod

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
