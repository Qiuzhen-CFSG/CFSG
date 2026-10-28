module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.Coordinates

/-!
# Six-point cocode geometry: avoidance consequences

The canonical map from the even core on the native fixed points sends pairs
to the actual cocode O₂ set. When this map is bijective, pulling a subspace
back and counting quotient cosets gives the M₂₄ bound two. For M₂₃, one
fixed pair containing point zero forces a proper subspace, giving the bound
four once the fixed-space dimension is five.

These are conditional steps in Aschbacher–Smith H.15.7(3), printed
pp.401–402 (1 March 2004 manuscript). The bijectivity and dimension premises,
the sextet normalizer, and the fixed-line equality remain separate obligations.
-/

public section

open Sporadic.Mathieu
open Representation.BinaryOffender
namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

/-- Pair avoidance transferred through the canonical fixed-point map. -/
theorem finrank_le_two_of_bijective_fixedPoint_map (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6) (hmap : Function.Bijective (toFixedCocode D))
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation D)
    (havoid : Disjoint (I : Set Cocode) cocodeO2) : Module.finrank (ZMod 2) I ≤ 2 := by
  let e := LinearEquiv.ofBijective (toFixedCocode D) hmap
  let J := I.comap (fixedSpace cocodeRepresentation D).subtype
  let U := J.comap e.toLinearMap
  have hdim : Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) I :=
    (e.ofSubmodule' J).finrank_eq.trans (Submodule.comapSubtypeEquivOfLe hI).finrank_eq
  rw [← hdim]
  apply finrank_le_two_of_avoids_pairs (by simpa only [Nat.card_eq_fintype_card] using hD)
  intro i j hij hu
  have hv : toCocode D (pair i j) ∈ I := hu
  exact Set.disjoint_left.mp havoid hv (toCocode_pair_mem D i j hij)

/-- For M₂₃, a fixed pair through point zero already forces properness.
Only the fixed-space dimension is needed for this bound. -/
theorem finrank_le_four_of_fixed_finrank (D : Subgroup M24)
    (hD : Nat.card (FixedPoint D) = 6)
    (h0 : (0 : Fin 24) ∈ MulAction.fixedPoints D (Fin 24))
    (hdim : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ fixedSpace cocodeRepresentation D)
    (havoid : Disjoint (I : Set Cocode) m23CocodeO2) : Module.finrank (ZMod 2) I ≤ 4 := by
  have hc : Fintype.card (FixedPoint D) = 6 := by simpa only [Nat.card_eq_fintype_card] using hD
  have : Nontrivial (FixedPoint D) := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let i : FixedPoint D := ⟨0, h0⟩
  obtain ⟨j, hj⟩ := exists_ne i
  have hp := toCocode_pointPair_mem D i j rfl (Ne.symm hj)
  have hW := toCocode_mem_fixedSpace D (pair i j)
  have hnot : toCocode D (pair i j) ∉ I := fun hi => Set.disjoint_left.mp havoid hi hp
  have hlt : I < fixedSpace cocodeRepresentation D := lt_of_le_of_ne hI (by
    intro he
    exact hnot (he ▸ hW))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  omega

end
end MathieuCode.SixPoint
