/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/AntipodalCounting.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.AntipodalStabilizer
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Counting fixed-point-free antipodal quotients.
Two-element fibers give the cardinality of the quotient by negation.

Source: Gerald Höhn, `Atlas/Conway/AntipodalCounting.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- Antipodal pairs represented in an intrinsic subset of the lattice. -/
def AntipodalImage (S : Set leech) :=
  {l : LeechAntipodalLine // ∃ v ∈ S, antipodalLine v = l}

def toAntipodalImage (S : Set leech) (v : S) : AntipodalImage S :=
  ⟨antipodalLine v.val,v.val,v.prop,rfl⟩

theorem toAntipodalImage_surjective (S : Set leech) :
    Function.Surjective (toAntipodalImage S) := by
  rintro ⟨l,v,hv,h⟩
  exact ⟨⟨v,hv⟩,Subtype.ext h⟩

instance antipodalImage_finite (S : Set leech) [Finite S] : Finite (AntipodalImage S) :=
  Finite.of_surjective _ (toAntipodalImage_surjective S)

theorem antipodalImage_card (S : Set leech) [Finite S]
    (hn : ∀ v ∈ S, -v ∈ S) (hz : ∀ v ∈ S, v ≠ 0) :
    2 * Nat.card (AntipodalImage S) = Nat.card S := by
  let : Fintype S := Fintype.ofFinite _
  let : Fintype (AntipodalImage S) := Fintype.ofFinite _
  have hf (l : AntipodalImage S) :
      (Finset.univ.filter (fun v : S => toAntipodalImage S v = l)).card = 2 := by
    obtain ⟨v,hv,he⟩ := l.prop
    let a : S := ⟨v,hv⟩
    let b : S := ⟨-v,hn v hv⟩
    have hab : a ≠ b := fun h => leech_ne_neg_of_ne_zero v (hz v hv) (congrArg Subtype.val h)
    have hs : Finset.univ.filter (fun v : S => toAntipodalImage S v = l) = {a,b} := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
      change (⟨antipodalLine w.val, _⟩ : AntipodalImage S) = l ↔ w = a ∨ w = b
      constructor
      · intro h
        have hh : antipodalLine w.val = antipodalLine v := (congrArg Subtype.val h).trans he.symm
        exact ((antipodalLine_eq_iff _ _).mp hh).imp Subtype.ext Subtype.ext
      · rintro (rfl | rfl)
        · exact Subtype.ext he
        · exact Subtype.ext ((antipodalLine_neg v).trans he)
    rw [hs,Finset.card_pair hab]
  have hc := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset (AntipodalImage S)))
    (f := toAntipodalImage S) (fun _ _ => Finset.mem_univ _)
  simp_rw [hf] at hc
  simpa [Nat.card_eq_fintype_card,Nat.mul_comm] using hc.symm

end Atlas.Conway
