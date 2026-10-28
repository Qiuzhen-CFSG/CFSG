module

public import Theory.SpecificGroups.PSL3Three.NodeExtensions.Check

/-!
# Exact finite lists for the certified ternary matrix subgroups

A list is certified by determinant-one entries, distinct codes, a rooted
spanning tree of positive generator products, and closure under each generator
and its inverse. The spanning tree proves inclusion in the generated subgroup;
word induction proves the reverse inclusion. Thus the list gives the exact
order, rather than merely a coset-cover bound.

These checks support the SL₃(3) input in Bender (1974), (4.1), printed p.225,
citing Janko (1966), Lemma 3.1. The subgroup generators and matrix coding are
exactly those of `PSL3Three.CertifiedEnumeration`.
-/

namespace TernaryFusedFour.MatrixClassification
open Matrix Matrix.PSL3Three Matrix.PSL3Three.CertifiedEnumeration
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration
open Matrix.PSL3Three.CertifiedEnumeration.CosetCheck
open Matrix.PSL3Three.CertifiedEnumeration.ExtensionCheck (allFin allFin_sound)

public structure Listing (i : Fin 50) (n : Nat) where
  code : Fin n → MatrixCode
  previous : Fin n → Fin n
  letter : Fin n → Fin (generatorCodes i).length
  next : Fin ((generatorCodes i).length + (generatorCodes i).length) → Fin n → Fin n

@[expose] public def Listing.check {i : Fin 50} {n : Nat} (d : Listing i n) : Bool :=
  allFin (fun r => decide (codeDet (d.code r) = 1)) &&
  decide (Function.Injective d.code) &&
  allFin (fun r => if r.val = 0 then matrixEq (decodeMatrix (d.code r)) 1 else
    decide ((d.previous r).val < r.val) &&
    matrixEq (decodeMatrix (d.code r))
      ((generator i (d.letter r)).val * decodeMatrix (d.code (d.previous r)))) &&
  allFin (fun j => allFin (fun r =>
    matrixEq ((nodeGenerator i j).val * decodeMatrix (d.code r))
      (decodeMatrix (d.code (d.next j r)))))

public theorem Listing.sound {i : Fin 50} {n : Nat} (hn : 0 < n) (d : Listing i n)
    (h : d.check = true) :
    Nat.card (properNode i) = n ∧
    ∀ x ∈ properNode i, ∃ r, x.val = decodeMatrix (d.code r) := by
  simp only [Listing.check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hdet, hinj⟩, hprev⟩, hstep⟩ := h
  have hd (r : Fin n) : codeDet (d.code r) = 1 := of_decide_eq_true (allFin_sound hdet r)
  let rep (r : Fin n) : SL := finiteModelEquiv ⟨d.code r, hd r⟩
  have hm : ∀ r, rep r ∈ properNode i := by
    intro r
    induction k : r.val using Nat.strong_induction_on generalizing r with
    | h k ih =>
      have hp := allFin_sound hprev r
      by_cases hr : r.val = 0
      · simp only [hr, ↓reduceIte] at hp
        have he : rep r = 1 := Subtype.ext (matrixEq_sound hp)
        rw [he]
        exact (properNode i).one_mem
      · simp only [hr, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hp
        have he : rep r = generator i (d.letter r) * rep (d.previous r) :=
          Subtype.ext (matrixEq_sound hp.2)
        rw [he]
        exact (properNode i).mul_mem (Subgroup.subset_closure ⟨d.letter r, rfl⟩)
          (ih _ (k ▸ hp.1) _ rfl)
  have hbase : rep ⟨0, hn⟩ = 1 := by
    have hp := allFin_sound hprev ⟨0, hn⟩
    simp only [↓reduceIte] at hp
    exact Subtype.ext (matrixEq_sound hp)
  have hs (j) (r) : nodeGenerator i j * rep r = rep (d.next j r) :=
    Subtype.ext (matrixEq_sound (allFin_sound (allFin_sound hstep j) r))
  have hcover (x : SL) (hx : x ∈ properNode i) : ∃ r, rep r = x := by
    rw [properNode_eq_wordSubgroup] at hx
    obtain ⟨w, rfl⟩ := hx
    induction w with
    | nil => exact ⟨⟨0, hn⟩, hbase⟩
    | cons j w ih =>
      obtain ⟨r, hr⟩ := ih
      exact ⟨d.next j r, by rw [evalWord, ← hr, hs]⟩
  let f : Fin n → properNode i := fun r => ⟨rep r, hm r⟩
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      apply hinj
      have hh := congrArg (fun x : properNode i => matrixCodeEquiv x.val.val) h
      change matrixCodeEquiv (decodeMatrix (d.code r)) =
        matrixCodeEquiv (decodeMatrix (d.code s)) at hh
      simpa only [encode_decode] using hh
    · intro x
      obtain ⟨r, hr⟩ := hcover x x.property
      exact ⟨r, Subtype.ext hr⟩
  refine ⟨?_, ?_⟩
  · simpa using (Nat.card_congr (Equiv.ofBijective f hf)).symm
  · intro x hx
    obtain ⟨r, hr⟩ := hcover x hx
    exact ⟨r, congrArg Subtype.val hr.symm⟩

end TernaryFusedFour.MatrixClassification
