module

public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.LargeAutomorphisms.FixedGeometryTransport

/-!
# Reducing Ree Sylow overgroups to fixed normalizer words

The positive root subgroup is a Sylow two-subgroup by the proved odd-index
calculation. Sylow conjugacy therefore puts any given Sylow overgroup into
standard position. In that position, fixed Bruhat factorization allows its
positive outer factors to be removed inside the overgroup itself.

An element outside the root-defined Borel consequently gives a fixed
normalizer word outside that Borel, together with both the positive subgroup
and its conjugate inside the overgroup. A root-generation theorem placing a
rank-one seed in their join, and nonsolvability of the seeds, will complete
the containment argument. Those two inputs remain explicit below.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3 2.3.4–5, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.ThreeSylowContainment

open Subgroup LargeLocalSeeds SectionGeometry.BNPair
open scoped Pointwise

/-- The actual root-defined positive subgroup is Sylow, with no model-order
formula or simplicity assumption. -/
def positiveSylow (m : ℕ) : Sylow 2 (Model m) :=
  sylowOfOddIndex m
    (OuterLocal.LargeAutomorphisms.unipotent_index_odd_of_standard
      (canonicalLocalBlockInput m)
      (FixedBruhat.standardUnipotent_index_odd (canonicalLocalBlockInput m)))

@[simp] theorem positiveSylow_coe (m : ℕ) :
    (positiveSylow m : Subgroup (Model m)) = unipotent m := by
  exact sylowOfOddIndex_coe m _

/-- Conjugation places an arbitrary Sylow subgroup in the actual positive
root subgroup. The conjugation convention is `x ↦ g * x * g⁻¹`. -/
theorem exists_conjugate_eq_unipotent {m : ℕ} (U : Sylow 2 (Model m)) :
    ∃ g : Model m,
      (U : Subgroup (Model m)).map (MulAut.conj g).toMonoidHom = unipotent m := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model m) U (positiveSylow m)
  exact ⟨g, congrArg Sylow.toSubgroup hg⟩

/-- Removing positive Bruhat factors retains membership in the overgroup,
and cannot turn an element outside the Borel into a middle factor inside it. -/
theorem exists_normalizerWord_mem_of_not_le_borel {m : ℕ}
    (K : Subgroup (Model m)) (hU : unipotent m ≤ K) (hB : ¬ K ≤ borel m) :
    ∃ n : Model m, n ∈ normalizerWords m ∧ n ∈ K ∧ n ∉ borel m := by
  obtain ⟨x, hx, hxB⟩ := Set.not_subset.mp hB
  obtain ⟨u, hu, n, hn, v, hv, he⟩ := Overlap.exists_fixed_normal_form m x
  have hnK : n ∈ K := by
    have h := K.mul_mem (K.mul_mem (K.inv_mem (hU hu)) hx) (K.inv_mem (hU hv))
    simpa only [he, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using h
  refine ⟨n, hn, hnK, ?_⟩
  intro hnB
  apply hxB
  rw [he]
  exact (borel m).mul_mem ((borel m).mul_mem (unipotent_le_borel m hu) hnB)
    (unipotent_le_borel m hv)

/-- An overgroup containing the positive subgroup and a middle factor also
contains the join with its positive conjugate. -/
theorem unipotent_sup_conjugate_le {m : ℕ} (K : Subgroup (Model m))
    (hU : unipotent m ≤ K) {n : Model m} (hn : n ∈ K) :
    unipotent m ⊔ (unipotent m).map (MulAut.conj n).toMonoidHom ≤ K := by
  refine sup_le hU ?_
  rintro _ ⟨u, hu, rfl⟩
  exact K.mul_mem (K.mul_mem hn (hU hu)) (K.inv_mem hn)

/-- Conditional root-theoretic reduction. Its first input must be proved from
the fixed root groups: it is not a consequence of Bruhat coverage alone. -/
theorem le_borel_of_seed_capture {m : ℕ}
    (hcapture : ∀ n : Model m, n ∈ normalizerWords m → n ∉ borel m →
      ∃ s : Side, seed m s ≤
        unipotent m ⊔ (unipotent m).map (MulAut.conj n).toMonoidHom)
    (hseed : ∀ s : Side, ¬ Group.IsSolvable (seed m s))
    (K : Subgroup (Model m)) (hK : Group.IsSolvable K) (hU : unipotent m ≤ K) :
    K ≤ borel m := by
  by_contra hB
  obtain ⟨n, hn, hnK, hnB⟩ := exists_normalizerWord_mem_of_not_le_borel K hU hB
  obtain ⟨s, hs⟩ := hcapture n hn hnB
  let _ : Group.IsSolvable K := hK
  exact hseed s (Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion (hs.trans (unipotent_sup_conjugate_le K hU hnK)))
    (Subgroup.inclusion_injective _))

/-- Sylow conjugacy and the preceding reduction give the arbitrary-Sylow
statement once root capture and seed nonsolvability have been established. -/
theorem exists_conjugate_le_borel_of_seed_capture {m : ℕ}
    (hcapture : ∀ n : Model m, n ∈ normalizerWords m → n ∉ borel m →
      ∃ s : Side, seed m s ≤
        unipotent m ⊔ (unipotent m).map (MulAut.conj n).toMonoidHom)
    (hseed : ∀ s : Side, ¬ Group.IsSolvable (seed m s))
    (U : Sylow 2 (Model m)) (K : Subgroup (Model m))
    (hK : Group.IsSolvable K) (hUK : (U : Subgroup (Model m)) ≤ K) :
    ∃ g : Model m, K.map (MulAut.conj g).toMonoidHom ≤ borel m := by
  obtain ⟨g, hg⟩ := exists_conjugate_eq_unipotent U
  refine ⟨g, le_borel_of_seed_capture hcapture hseed _ ?_ ?_⟩
  · let _ : Group.IsSolvable K := hK
    exact Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective K)
  · rw [← hg]
    exact map_mono hUK

end ReeF4.Parabolics.ThreeSylowContainment
