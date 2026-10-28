module
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreeSylowContainment
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.ThreePrimeBorel
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.CorootRealization

/-!
# Three-free solvable Sylow overgroups in Ree groups

For a large Ree group, a solvable overgroup of a full Sylow two-subgroup
is conjugate into the root-defined Borel. Coroot realization makes that
Borel's order prime to three. The same conclusion holds in an extension
with a two-group kernel: the restricted kernel and the image both have
order prime to three, so the kernel-image product formula applies.

This supplies the Ree Borel obstruction used in Aschbacher--Smith,
14.2.15, printed pp.985--986, through the Borel geometry of F.1.12.
-/

public section
open Subgroup
namespace ReeF4.Parabolics

/-- A solvable overgroup of a full Ree Sylow two-subgroup has three-free order. -/
theorem coprime_three_of_solvable_sylow_overgroup {m : ℕ} (hm : 1 ≤ m)
    (U : Sylow 2 (Model m)) (K : Subgroup (Model m))
    (hK : Group.IsSolvable K) (hUK : (U : Subgroup (Model m)) ≤ K) :
    Nat.Coprime 3 (Nat.card K) := by
  obtain ⟨g, hg⟩ := ThreeSylowContainment.exists_conjugate_le_borel hm U K hK hUK
  have hc := (ThreePrimeBorel.borel_coprime_three_of_torus m
    (splitTorus_eq_diagonalTorus m).le).of_dvd_right (card_dvd_of_le hg)
  rwa [card_map_of_injective (MulAut.conj g).injective] at hc

/-- A two-group kernel preserves the three-free Sylow-overgroup obstruction. -/
theorem coprime_three_of_solvable_sylow_overgroup_of_two_kernel
    {A : Type*} [Group A] [Finite A] {m : ℕ} (hm : 1 ≤ m)
    (f : A →* Model m) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (U : Sylow 2 A) (K : Subgroup A)
    (hK : Group.IsSolvable K) (hUK : (U : Subgroup A) ≤ K) :
    Nat.Coprime 3 (Nat.card K) := by
  let _ := hK
  have hc := coprime_three_of_solvable_sylow_overgroup hm (U.mapSurjective hf)
    (K.map f) (Group.isSolvable_of_surjective (f.subgroupMap_surjective K))
    (map_mono hUK)
  let q := f.comp K.subtype
  have hqk : IsPGroup 2 q.ker :=
    hk.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨n, hn⟩ := hqk.exists_card_eq
  have hkc : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hr : q.range = K.map f := by
    rw [MonoidHom.range_comp, range_subtype]
  have hcard : Nat.card K = Nat.card q.ker * Nat.card (K.map f) := by
    rw [← hr, ← index_ker, card_mul_index]
  rw [hcard]
  exact hkc.mul_right hc

end ReeF4.Parabolics
