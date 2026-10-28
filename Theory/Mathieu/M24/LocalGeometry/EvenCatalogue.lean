module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order

/-!
# Explicit candidates for the normal elementary subgroups of an M₂₄ Sylow subgroup

Each row lists positions in the existing certified enumeration of the marked
order-1024 subgroup. The associated subgroup is formed inside that subgroup,
then mapped to the actual Witt-design M₂₄ by its inclusion. Zero denotes the
identity entry and pads each generator list to length six.

These are concrete candidate definitions, not a classification assertion.
Exhaustiveness among nontrivial normal elementary subgroups and the ambient
normalizer calculations are separate obligations. The last two rows are the
candidates treated in `EvenCandidates`.

Source context: Aschbacher–Smith, condition E and Theorem 0.1.2(5), printed
pp.3–4; GLS3, Table 5.3e. The exploratory normal-subgroup calculation is saved
with the source generator; none of its group-theoretic outputs is trusted.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
open Subgroup SylowNormalizer

def generatorIndex : Fin 22 → Fin 6 → Fin 1024
  | 0 => ![106,0,0,0,0,0]
  | 1 => ![106,115,0,0,0,0]
  | 2 => ![106,758,0,0,0,0]
  | 3 => ![642,106,0,0,0,0]
  | 4 => ![106,57,115,0,0,0]
  | 5 => ![106,701,115,0,0,0]
  | 6 => ![642,106,758,0,0,0]
  | 7 => ![642,106,502,0,0,0]
  | 8 => ![642,512,744,0,0,0]
  | 9 => ![106,412,701,115,0,0]
  | 10 => ![106,27,57,115,0,0]
  | 11 => ![642,106,948,502,0,0]
  | 12 => ![642,106,701,758,0,0]
  | 13 => ![642,106,624,758,0,0]
  | 14 => ![642,106,112,758,0,0]
  | 15 => ![642,106,481,758,0,0]
  | 16 => ![642,512,744,130,0,0]
  | 17 => ![642,512,744,502,0,0]
  | 18 => ![642,106,624,481,758,0]
  | 19 => ![642,512,744,502,112,0]
  | 20 => ![642,106,129,624,481,758]
  | _ => ![642,512,744,502,2,112]

/-- Each candidate is an intrinsic subgroup of the fixed Sylow carrier. -/
noncomputable def subgroup (i : Fin 22) : Subgroup candidate :=
  closure (Set.range (fun j => OrderEnumeration.element (generatorIndex i j)))

/-- Its actual image in the Witt-design automorphism group. -/
noncomputable def ambient (i : Fin 22) : Subgroup M24 :=
  (subgroup i).map candidate.subtype

/-- The full ambient normalizer, with no asserted order or shape. -/
noncomputable def localGroup (i : Fin 22) : Subgroup M24 :=
  normalizer (ambient i : Set M24)

theorem ambient_le_candidate (i : Fin 22) : ambient i ≤ candidate := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue
