module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Reduction
public import Theory.GroupAction.LargeOrbitNormalizer

/-!
# Local conjugacy and six-point normalizer calculations

Conjugation by an element of a literal local overgroup preserves its two-core
and induces actual conjugation in M/O₂(M). The quotient-image and normalizer
transport below therefore respect the restriction to M.

A six-point action with a four-point residual-core orbit bounds every
intermediate normalizer once the pair product is the preimage of the block
stabilizer. The action homomorphism and preimage equality remain explicit;
no quotient identification is inferred from an order or a group-family name.

Sources: GLS3 Table 5.3p and the ATLAS max3/max4 local definitions. These
lemmas support the additional Held calculation for Aschbacher–Smith,
printed pp.509–511 and 747–748; they do not assert the model witnesses.
-/

public section

open Subgroup
open scoped Pointwise
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner

/-- Restriction and quotient image preserve containment. -/
theorem localImage_mono (i : Bool) {H K : Subgroup Held.He} (h : H ≤ K) :
    localImage i H ≤ localImage i K := map_mono (comap_mono h)

/-- Relative normality preserves the embedded local two-core. -/
theorem localTwoCore_map_conj (i : Bool) (g : localOvergroup i) :
    (localTwoCore i).map (MulAut.conj g.val).toMonoidHom = localTwoCore i :=
  mem_normalizer_iff_map_conj_eq.mp (localOvergroup_le_normalizer_localTwoCore i g.property)

/-- Ambient local conjugation becomes conjugation by its actual quotient image. -/
theorem localImage_map_conj (i : Bool) (g : localOvergroup i)
    (H : Subgroup Held.He) (hH : H ≤ localOvergroup i) :
    localImage i (H.map (MulAut.conj g.val).toMonoidHom) =
      (localImage i H).map (MulAut.conj (localQuotientMap i g)).toMonoidHom := by
  have hHm : H.map (MulAut.conj g.val).toMonoidHom ≤ localOvergroup i := by
    rintro _ ⟨x, hx, rfl⟩
    exact (localOvergroup i).mul_mem
      ((localOvergroup i).mul_mem g.property (hH hx)) ((localOvergroup i).inv_mem g.property)
  have hr : (H.map (MulAut.conj g.val).toMonoidHom).subgroupOf (localOvergroup i) =
      (H.subgroupOf (localOvergroup i)).map (MulAut.conj g).toMonoidHom := by
    apply map_injective (localOvergroup i).subtype_injective
    rw [map_subgroupOf_eq_of_le hHm, map_map]
    have he : (localOvergroup i).subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj g.val).toMonoidHom.comp (localOvergroup i).subtype := by
      ext x
      rfl
    rw [he, ← map_map, map_subgroupOf_eq_of_le hH]
  unfold localImage
  rw [hr, map_map, map_map]
  congr 1

/-- Descend a core commutator calculation along local conjugation. -/
theorem local_commutator_eq_of_conj (i : Bool) (g : localOvergroup i)
    (R : Subgroup Held.He)
    (h : ⁅localTwoCore i, R.map (MulAut.conj g.val).toMonoidHom⁆ = localTwoCore i) :
    ⁅localTwoCore i, R⁆ = localTwoCore i := by
  apply map_injective (f := (MulAut.conj g.val).toMonoidHom) (MulAut.conj g.val).injective
  rw [map_commutator, localTwoCore_map_conj]
  exact h

/-- Descend a quotient normalizer inclusion along the same local conjugation. -/
theorem local_normalizer_le_of_conj (i : Bool) (g : localOvergroup i)
    (U K : Subgroup Held.He) (hU : U ≤ localOvergroup i) (hK : K ≤ localOvergroup i)
    (h : normalizer (localImage i (U.map (MulAut.conj g.val).toMonoidHom) :
        Set (LocalQuotient i)) ≤ localImage i (K.map (MulAut.conj g.val).toMonoidHom)) :
    normalizer (localImage i U : Set (LocalQuotient i)) ≤ localImage i K := by
  rw [localImage_map_conj i g U hU, localImage_map_conj i g K hK,
    ← map_equiv_normalizer_eq] at h
  exact (map_le_map_iff_of_injective (MulAut.conj (localQuotientMap i g)).injective).mp h

/-- A four-point orbit in an actual six-point action controls the whole
interval from the residual two-core to the pair product. -/
theorem local_normalizer_le_of_sixPointAction
    (i : Bool) (S R U : Subgroup Held.He)
    (f : LocalQuotient i →* Equiv.Perm (Fin 6)) (B : Set (Fin 6)) (x : Fin 6)
    (hB : B.ncard = 4)
    (hK : (MulAction.stabilizer (Equiv.Perm (Fin 6)) B).comap f = localImage i (R ⊔ S))
    (horbit : MulAction.orbit ((localImage i (twoCore S R)).map f) x = B)
    (hQU : twoCore S R ≤ U) (hUK : U ≤ R ⊔ S) :
    normalizer (localImage i U : Set (LocalQuotient i)) ≤ localImage i (R ⊔ S) := by
  apply normalizer_le_of_large_orbit_preimage f (localImage i (twoCore S R))
    (localImage i U) (localImage i (R ⊔ S)) B x
    (localImage_mono i hQU) (localImage_mono i hUK) hK horbit
  simp [hB]

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
