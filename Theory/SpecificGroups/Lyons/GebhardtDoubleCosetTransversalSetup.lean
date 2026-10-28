module

public import Theory.SpecificGroups.Lyons.GebhardtCosetGeometry
public import Theory.GroupTheory.ConjugateIntersectionCosets
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Option

/-!
# Assembling the Gebhardt double-coset transversal

The stabilizer of `H * r` in `H` consists of the local elements whose conjugate
by `r` is local. Its right-coset quotient supplies actual representatives for
`H * r * H`. We combine the four nonidentity quotients with one identity
representative and embed this finite family into `Fin 8835156`.

The construction below takes explicit finiteness and subdegree bounds. It
does not assert these missing local calculations. In particular, the ordering
of the proposed subdegree multiset is not silently assigned to the four words:
the bounds include a permutation making that assignment, with its proof.

Source: Gebhardt, Experimental Mathematics 9 (2000), 333–338, Sections 2 and
3B. The local-order and stabilizer calculations are separate inputs to the
assembly; no identification of the ambient group is used.
-/

namespace Lyons.Gebhardt
public section

/-- The stabilizer of the indicated right coset, as a subgroup of `H`. -/
@[expose] def localDoubleCosetStabilizer (i : Fin 5) : Subgroup localSubgroup :=
  localSubgroup.conjugateIntersection (doubleCosetRepresentative i)

@[simp] theorem mem_localDoubleCosetStabilizer (i : Fin 5) (h : localSubgroup) :
    h ∈ localDoubleCosetStabilizer i ↔
      doubleCosetRepresentative i * h.val * (doubleCosetRepresentative i)⁻¹ ∈
        localSubgroup := Iff.rfl

/-- The proposed four nontrivial subdegrees, without assigning them to words. -/
@[expose] def proposedSubdegree (i : Fin 4) : ℕ :=
  match i.val with
  | 0 => 19530
  | 1 => 968750
  | 2 => 2034375
  | _ => 5812500

theorem sum_proposedSubdegree : ∑ i, proposedSubdegree i = 8835155 := by
  simp [Fin.sum_univ_succ, proposedSubdegree]

/-- The local index calculations required for assembly. These inequalities
are used only with a separate proof that `localSubgroup` is finite. -/
structure LocalSubdegreeBounds where
  assignment : Equiv.Perm (Fin 4)
  index_le : ∀ i, (localDoubleCosetStabilizer i.succ).index ≤
    proposedSubdegree (assignment i)

private abbrev LocalCosets (i : Fin 4) :=
  Quotient (QuotientGroup.rightRel (localDoubleCosetStabilizer i.succ))

private abbrev TransversalIndices := Option (Σ i, LocalCosets i)

private noncomputable def transversalValue : TransversalIndices → Presentation
  | none => 1
  | some ⟨i, q⟩ => doubleCosetRepresentative i.succ * (q.out : localSubgroup).val

private theorem transversalValue_covers (i : Fin 5) (h : localSubgroup) :
    ∃ (k : localSubgroup) (p : TransversalIndices),
      doubleCosetRepresentative i * h.val = k.val * transversalValue p := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨h, none, by simp [transversalValue]⟩
  · obtain ⟨k, hk⟩ := localSubgroup.conjugateIntersection_covers
      (doubleCosetRepresentative j.succ) h
    exact ⟨k, some ⟨j, Quotient.mk _ h⟩, hk⟩

private theorem transversalIndices_card_le [Finite localSubgroup]
    (bounds : LocalSubdegreeBounds) : Nat.card TransversalIndices ≤ 8835156 := by
  have hc (i : Fin 4) : Nat.card (LocalCosets i) =
      (localDoubleCosetStabilizer i.succ).index :=
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)
  have hs : (∑ i, Nat.card (LocalCosets i)) ≤ 8835155 := calc
    _ = ∑ i : Fin 4, (localDoubleCosetStabilizer i.succ).index :=
      by simp_rw [hc]
    _ ≤ ∑ i : Fin 4, proposedSubdegree (bounds.assignment i) :=
      Finset.sum_le_sum (fun i _ => bounds.index_le i)
    _ = ∑ i : Fin 4, proposedSubdegree i :=
      Finset.sum_equiv bounds.assignment (by simp) (by simp)
    _ = 8835155 := sum_proposedSubdegree
  let := Fintype.ofFinite (Σ i, LocalCosets i)
  have ho : Nat.card TransversalIndices = Nat.card (Σ i, LocalCosets i) + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_option]
  rw [ho, Nat.card_sigma]
  omega

/-- Finite local stabilizer quotients give the requested witness-based
transversal. Repeated or unused representatives are harmless. -/
noncomputable def doubleCosetTransversalOfSubdegreeBounds [Finite localSubgroup]
    (bounds : LocalSubdegreeBounds) : DoubleCosetTransversal := by
  classical
  letI := Fintype.ofFinite TransversalIndices
  have hcard : Fintype.card TransversalIndices ≤ Fintype.card (Fin 8835156) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      transversalIndices_card_le bounds
  let e : TransversalIndices ↪ Fin 8835156 :=
    Classical.choice (Function.Embedding.nonempty_of_card_le hcard)
  let decode : Fin 8835156 → TransversalIndices := Function.invFun e
  have hdecode (p : TransversalIndices) : decode (e p) = p :=
    Function.leftInverse_invFun e.injective p
  refine { repr := fun j => transversalValue (decode j)
           initial := e none
           initial_eq := ?_
           cover := ?_ }
  · rw [hdecode]
    rfl
  · intro i h
    obtain ⟨k, p, hp⟩ := transversalValue_covers i h
    exact ⟨k, e p, by simpa only [hdecode] using hp⟩

end
end Lyons.Gebhardt
