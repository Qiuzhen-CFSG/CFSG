module
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A normalized conjugate coset is a subgroup orbit

Let `M` be a finite subgroup normalized by the centralizer of an element `j`,
with trivial intersection with that centralizer. Then the conjugation orbit
of `j` under `M` is the left coset `jM`. The orbit uses the subgroup transported
to `ConjAct G`; the coset uses the ordinary multiplication action of `G`.

This is the group-action step in Brauer, *On finite Desarguesian planes I*,
(2B), article page 119. The public equality supports both the coset-block
argument and the subsequent stabilizer and cardinality calculations.

Conjugation by `j` preserves `M` and is fixed-point-free there. On a finite
group its commutator map is surjective: applying this to the conjugate of an
element `m` gives `c * j * c⁻¹ = j * m`. The other orbit inclusion uses
normalization directly. This reduction does not require `j` to be an
involution or the ambient group to be finite.
-/

open scoped Pointwise
namespace Theory.GroupTheory
/-- The conjugation orbit under a centralizer-normalized subgroup disjoint
from the centralizer is the corresponding left coset. -/
public theorem orbit_conjugate_eq_coset
    {G : Type*} [Group G] (M : Subgroup G) [Finite M] (j : G)
    (hn : Subgroup.centralizer ({j} : Set G) ≤ Subgroup.normalizer (M : Set G))
    (hd : Disjoint M (Subgroup.centralizer ({j} : Set G))) :
    MulAction.orbit ↥(M.map ConjAct.toConjAct.toMonoidHom : Subgroup (ConjAct G)) j =
      j • (M : Set G) := by
  let N : Subgroup (ConjAct G) := M.map ConjAct.toConjAct.toMonoidHom
  have hj : j ∈ Subgroup.normalizer (M : Set G) :=
    hn (by simp [Subgroup.mem_centralizer_singleton_iff])
  let φ : MulAut M := M.normalizerMonoidHom ⟨j, hj⟩
  have hφ : MonoidHom.FixedPointFree φ := by
    intro m hm
    apply Subtype.ext
    have heq : j * (m : G) * j⁻¹ = (m : G) := congrArg Subtype.val hm
    have hc : (m : G) ∈ Subgroup.centralizer ({j} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    have hmem : (m : G) ∈ M ⊓ Subgroup.centralizer ({j} : Set G) := ⟨m.property, hc⟩
    change (m : G) = 1
    simpa only [hd.eq_bot, Subgroup.mem_bot] using hmem
  change MulAction.orbit (↥N) j = j • (M : Set G)
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨m, hm, hmc⟩ := c.property
    have hc : (c : ConjAct G) = ConjAct.toConjAct m := hmc.symm
    change (c : ConjAct G) • j ∈ j • (M : Set G)
    rw [hc]
    change m * j * m⁻¹ ∈ j • (M : Set G)
    refine Set.mem_smul_set.mpr ⟨j⁻¹ * m * j * m⁻¹, ?_, ?_⟩
    · have hmj : j⁻¹ * m * j ∈ M := by
        simpa only [inv_inv, SetLike.mem_coe] using ((Subgroup.normalizer (M : Set G)).inv_mem hj m).mp hm
      exact M.mul_mem hmj (M.inv_mem hm)
    · simp only [smul_eq_mul, mul_assoc, mul_inv_cancel_left]
  · intro hx
    obtain ⟨m, hm, rfl⟩ := Set.mem_smul_set.mp hx
    obtain ⟨c, hc⟩ := hφ.commutatorMap_surjective (φ ⟨m, hm⟩)
    have heq := congrArg Subtype.val hc
    change (c : G) / (j * (c : G) * j⁻¹) = j * m * j⁻¹ at heq
    have heq' : (c : G) * j * (c : G)⁻¹ = j * m := by
      apply mul_right_cancel (b := j⁻¹)
      simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc] using heq
    refine ⟨⟨ConjAct.toConjAct (c : G), ?_⟩, heq'⟩
    exact ⟨c, c.property, rfl⟩

end Theory.GroupTheory
