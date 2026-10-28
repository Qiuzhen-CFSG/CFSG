module

public import GorensteinWalter.Classification
public import Glauberman.DicksonClassification

/-!
# The actual `PSL₂` intersection inside `PGL₂`

For an actual subgroup `A ≤ PGL₂(F)`, the subgroup lying in the canonical
`PSL₂` layer is represented by the comap of `ProjectiveSpecialLinearGroup.toPGL`.
This module records the exact Dickson classification of that subgroup,
including the subfield witnesses.  The dihedral-Sylow and no-normal-complement
properties are deliberately not fabricated here: they require a separate
transfer argument for the particular subgroup under study.

This is the intersection/reduction interface for ABG II.4, Lemma 8, using
Huppert II.8.27 (Dickson).  No alternative is discarded at this layer.
-/

namespace GorensteinWalter

universe u

open Matrix

/-- The actual preimage in `PSL₂(F)` of an actual subgroup of `PGL₂(F)`. -/
public def pgl2PSL2Intersection
    {F : Type u} [Field F] [Finite F]
    (A : Subgroup (PGL2 F)) : Subgroup (PSL2 F) :=
  Subgroup.comap (Matrix.ProjectiveSpecialLinearGroup.toPGL
    (n := Fin 2) (R := F)) A

/-- Dickson's classification applied to the actual `PSL₂` intersection of
an actual subgroup of `PGL₂`. -/
public theorem pgl2_psl2_intersection_dickson_classification
    {F : Type u} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (A : Subgroup (PGL2 F)) :
    IsElementaryAbelian p (pgl2PSL2Intersection A) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card (pgl2PSL2Intersection A) = z ∧
        IsCyclic (pgl2PSL2Intersection A)) ∨
      (∃ z : ℕ,
        ((z ∣ (Nat.card F - 1) / Nat.gcd (Nat.card F - 1) 2) ∨
          (z ∣ (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)) ∧
        Nat.card (pgl2PSL2Intersection A) = 2 * z ∧
        Nonempty (pgl2PSL2Intersection A ≃* DihedralGroup z)) ∨
      ((p ≠ 2 ∨ Even f) ∧
        Nonempty (pgl2PSL2Intersection A ≃* alternatingGroup (Fin 4))) ∨
      ((16 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (pgl2PSL2Intersection A ≃* Equiv.Perm (Fin 4))) ∨
      ((p = 5 ∨ 5 ∣ p ^ (2 * f) - 1) ∧
        Nonempty (pgl2PSL2Intersection A ≃* alternatingGroup (Fin 5))) ∨
      (∃ m t : ℕ,
        t ∣ p ^ m - 1 ∧
        t ∣ (p ^ f - 1) / Nat.gcd (p ^ f - 1) 2 ∧
        ∃ N C : Subgroup (pgl2PSL2Intersection A),
          N.Normal ∧ IsElementaryAbelian p N ∧ Nat.card N = p ^ m ∧
          IsCyclic C ∧ Nat.card C = t ∧ Disjoint N C ∧ N ⊔ C = ⊤) ∨
      (∃ m : ℕ, m ≠ 0 ∧ m ∣ f ∧
        Nonempty (pgl2PSL2Intersection A ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p m)) ∧
        Nonempty (Glauberman.Dickson.SubfieldConjugacyWitness p m
          (pgl2PSL2Intersection A))) ∨
      (∃ m : ℕ, m ≠ 0 ∧ 2 * m ∣ f ∧
        Nonempty (pgl2PSL2Intersection A ≃* PGL2 (GaloisField p m)) ∧
        Nonempty (Glauberman.Dickson.SubfieldConjugacyWitness p m
          (pgl2PSL2Intersection A))) := by
  unfold pgl2PSL2Intersection
  exact Glauberman.Dickson.huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield
    (F := F) hFcard (Subgroup.comap
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := F)) A)

end GorensteinWalter
