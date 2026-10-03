module
public import Theory.GroupTheory.Signalizer.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Common-subgroup conjugation of signalizer subgroups

The intersection of all values of a signalizer family is fixed pointwise
by the actor. Conjugation by one of its elements therefore commutes with
the given action. Since that element also belongs to every family value,
it normalizes those values. Thus conjugation preserves the family bounds,
and hence the entire signalizer-subgroup predicate.

These are the elementary conjugation properties used in the transitivity
argument of Kurzweil–Stellmacher, *The Theory of Finite Groups*, Lemma 11.1.8,
printed p.309. The conjugator belongs to the actual common infimum of
family values, not merely to the full fixed subgroup of the ambient group.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

variable {A G : Type*} [Group A] [Group G] [MulDistribMulAction A G]

public theorem common_le_fixed (θ : TwoSignalizerFamily A G) :
    θ.common ≤ fixedPointSubgroup A G := by
  intro x hx a
  by_cases ha : a = 1
  · simp [ha]
  · exact θ.le_fixed ⟨a, ha⟩ (θ.common_le ⟨a, ha⟩ hx) ⟨a, Subgroup.mem_zpowers a⟩

public theorem IsSignalizerSubgroup.map_conj_of_mem_common {θ : TwoSignalizerFamily A G}
    {U : Subgroup G} (hU : θ.IsSignalizerSubgroup U) {c : G} (hc : c ∈ θ.common) :
    θ.IsSignalizerSubgroup (U.map (MulAut.conj c)) := by
  let _ := hU.2.1
  have hfix := θ.common_le_fixed hc
  have hcomm (a : A) (x : G) :
      a • (MulAut.conj c x) = MulAut.conj c (a • x) := by
    simp only [MulAut.conj_apply, smul_mul', smul_inv', hfix a]
  have hinv : IsInvariant A G (U.map (MulAut.conj c)) := by
    refine ⟨fun a x => ?_⟩
    have forward (b : A) (y : G) (hy : y ∈ U.map (MulAut.conj c)) :
        b • y ∈ U.map (MulAut.conj c) := by
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨b • z, (hU.2.2.1.invariant b z).mp hz, (hcomm b z).symm⟩
    exact ⟨forward a x, fun h => by simpa using forward a⁻¹ (a • x) h⟩
  refine ⟨?_, ?_, hinv, ?_⟩
  · rw [Subgroup.card_map_of_injective
      (f := (MulAut.conj c : G →* G)) (show Function.Injective (MulAut.conj c : G →* G) from
        (MulAut.conj c).injective)]
    exact hU.1
  · let e : U ≃* U.map (MulAut.conj c : G →* G) :=
      U.equivMapOfInjective (MulAut.conj c : G →* G)
        (show Function.Injective (MulAut.conj c : G →* G) from (MulAut.conj c).injective)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx.1
    have hyfix : y ∈ FixedPoints.subgroup (Subgroup.zpowers a.val) G := by
      intro b
      apply (MulAut.conj c).injective
      exact (hcomm b.val y).symm.trans (hx.2 b)
    have hcval : c ∈ θ.subgroup a := θ.common_le a hc
    exact (θ.subgroup a).mul_mem
      ((θ.subgroup a).mul_mem hcval (hU.2.2.2 a ⟨hy, hyfix⟩))
      ((θ.subgroup a).inv_mem hcval)

end Theory.GroupTheory.TwoSignalizerFamily
