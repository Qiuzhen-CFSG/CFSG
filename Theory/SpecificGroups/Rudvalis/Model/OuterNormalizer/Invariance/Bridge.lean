module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Relation

/-!
# Identifying an invariant table with the Rudvalis relation

A binary relation invariant under the two actual ATLAS generators is invariant
under every word in them. If its row at zero is the forest component rooted at
one, transporting the first argument to zero identifies it with `adj`.
Thus a cached matrix needs only its two invariance checks and its base row
checked; no assumption about the full point stabilizer is needed.

This supplies the table-to-relation bridge for the rank-three action in
GLS3, Table 5.3r, printed p.279.
-/

namespace Rudvalis.OuterNormalizer.InvarianceCertificate

private def cacheAut (r : Fin 4060 → Fin 4060 → Prop) :
    Subgroup (Equiv.Perm (Fin 4060)) where
  carrier := {g | ∀ x y, r (g x) (g y) ↔ r x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro p q hp hq x y
    exact (hp (q x) (q y)).trans (hq x y)
  inv_mem' := by
    intro p hp x y
    simpa using (hp (p⁻¹ x) (p⁻¹ y)).symm

/-- Generator invariance and the base row identify a table with the relation
defined by the actual transitivity words. -/
public theorem eq_adj (r : Fin 4060 → Fin 4060 → Prop)
    (ha : ∀ x y, r (aPerm x) (aPerm y) ↔ r x y)
    (hb : ∀ x y, r (bPerm x) (bPerm y) ↔ r x y)
    (hzero : ∀ y, r 0 y ↔ PrimitiveData.root y = 1) (x y : Fin 4060) :
    r x y ↔ adj x y := by
  have hG : modelSubgroup ≤ cacheAut r := by
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | hg)
    · exact ha
    · exact Set.mem_singleton_iff.mp hg ▸ hb
  have h := hG (toBase (PrimitiveData.transDepth x) x).property x y
  change r (toBase (PrimitiveData.transDepth x) x • x)
    (toBase (PrimitiveData.transDepth x) x • y) ↔ r x y at h
  rw [toBase_smul] at h
  exact h.symm.trans (hzero _)

end Rudvalis.OuterNormalizer.InvarianceCertificate
