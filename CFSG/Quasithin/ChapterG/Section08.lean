module

public import CFSG.Quasithin.ChapterG.Section08.Basic
public import CFSG.Quasithin.ChapterG.Section08.FaithfulComplements
public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.PrescribedPrime
public import CFSG.Quasithin.ChapterG.Section08.ThetaFaithfulness

/-!
# G.8: An extension of Thompson's dihedral lemma

The source is Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, printed pp.349–351. All results
G.8.2–9 are proved and re-exported here. The faithful-complement theorem
G.8.2 supplies the input to the dihedral induction, including its relative
split and prescribed-prime refinement. The products are actual injective
homomorphisms from products of concrete dihedral groups.

The terminal G.8.9 uses relative subnormality in F*(H) and the intended
centralizer C_{F*(H)}(X), as in the printed proof and A.4.4(b); see the
source correction in `Section08.Defs`. Its Θ-subgroups use actual
supercritical subgroups and are proved characteristic and nonempty.
Consumer adapters are in `Section08.Applications`.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section08

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- G.8.6: Thompson's dihedral lemma, with the faithful-complement input
discharged. The product contains the given actor and lies inside XA. -/
theorem lemma_G_8_6 (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card A = 2 ^ n) :
    ∃ D : DihedralProduct G n,
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A :=
  lemma_G_8_6_of_faithfulComplement (faithfulComplementTheorem G)
    A X hA hX hodd hnorm hfaith n hn hcard

/-- G.8.7: split the actor at its kernel on an invariant subgroup.
The two embedded dihedral products commute; their prime divisors are
retained, so they can be combined by `DihedralProduct.exists_join`.
The final printed proof sentence cites G.8.5 where it uses G.8.6. -/
theorem lemma_G_8_7 (A X Y B : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (hYX : Y ≤ X) (hAY : A ≤ normalizer (Y : Set G))
    (hB : B = A ⊓ centralizer (Y : Set G))
    (n m : ℕ) (hcard : Nat.card A = 2 ^ n) (hBcard : Nat.card B = 2 ^ m)
    (_hm : 0 < m) (hmn : m < n) :
    ∃ (D : Subgroup G) (L : DihedralProduct G m) (R : DihedralProduct G (n - m)),
      B ⊓ D = ⊥ ∧ B ⊔ D = A ∧
      B ≤ L.embedding.range ∧
      L.embedding.range ≤ (X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G)) ⊔ B ∧
      D ≤ R.embedding.range ∧ R.embedding.range ≤ Y ⊔ D ∧
      L.embedding.range ≤ centralizer (R.embedding.range : Set G) ∧
      (∀ i, L.prime i ∣ Nat.card X) ∧ (∀ i, R.prime i ∣ Nat.card Y) :=
  relative_dihedral_extraction (faithfulComplementTheorem G)
    A X Y B hA hX hodd hnorm hfaith hYX hAY hB n m hcard hBcard hmn.le

/-- G.8.8: a nontrivial action on the actual O_p(X) image selects p as
the first factor prime. Positive rank and oddness of p follow from the
constructed product, without extra assumptions. -/
theorem lemma_G_8_8 (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (p : ℕ) (hp : p.Prime)
    (hnon : ¬ A ≤ centralizer ((pCore p X).map X.subtype : Set G))
    (n : ℕ) (hcard : Nat.card A = 2 ^ n) :
    ∃ (hn : 0 < n) (D : DihedralProduct G n),
      A ≤ D.embedding.range ∧ D.embedding.range ≤ X ⊔ A ∧
      D.prime ⟨0, hn⟩ = p ∧ ∀ i, D.prime i ∣ Nat.card X :=
  lemma_G_8_8_of_faithfulComplement (faithfulComplementTheorem G)
    A X hA hX hodd hnorm hfaith p hp hnon n hcard

end CFSG.Quasithin.ChapterG.Section08
