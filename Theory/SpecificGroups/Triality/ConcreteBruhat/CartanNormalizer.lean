module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Tits
public import Theory.SpecificGroups.Triality.ConcreteBruhat.Torus
public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore

/-!
# The normalizer of the binary triality positive subgroup

The descended Borel normalizes its positive subgroup. Conversely, the concrete
Tits system classifies every overgroup of the Borel by its simple Bruhat cells.
Neither simple representative can normalize the positive subgroup: conjugating
the positive folded root element at parameter one gives an element outside the
Borel. Thus the normalizer has no simple cells and is exactly the Borel.

All subgroups and witnesses belong to the original elementary graph-field
fixed group modulo its center. The argument includes q = 2 and requires no
simplicity or perfectness hypothesis.

Source: the Bruhat and root-group structure in GLS3 2.3.4–8,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.ConcreteBruhat
open Parabolics

theorem borel_le_normalizer_unipotent (P : Parameters) (hp : P.prime = 2) :
    borel P ≤ Subgroup.normalizer (unipotent P) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (unipotent_le_borel P)).mp
    (unipotent_normal_in_borel P hp)

private theorem simple_not_mem_normalizer (n : ℕ) (hn : 0 < n) (a : Node) :
    simpleRepresentative (binaryParameters n hn) rfl a ∉
      Subgroup.normalizer (unipotent (binaryParameters n hn)) := by
  intro h
  have hc := (Subgroup.mem_normalizer_iff.mp h _).mp
    (positive_mem_unipotent (binaryParameters n hn) rfl a 1)
  have hi : (simpleRepresentative (binaryParameters n hn) rfl a)⁻¹ =
      simpleRepresentative (binaryParameters n hn) rfl a :=
    inv_eq_of_mul_eq_one_left (by
      simpa only [pow_two] using simpleRepresentative_sq (binaryParameters n hn) rfl a)
  rw [hi] at hc
  exact FoldedCellGeometry.positive_conjugate_not_borel n hn a (unipotent_le_borel _ hc)

private theorem normalizer_unipotent_binary (n : ℕ) (hn : 0 < n) :
    Subgroup.normalizer (unipotent (binaryParameters n hn)) =
      borel (binaryParameters n hn) := by
  let P := binaryParameters n hn
  let T := titsSystem n hn
  let H := Subgroup.normalizer (unipotent P : Set (Carrier P))
  have hB : T.B ≤ H := borel_le_normalizer_unipotent P rfl
  have hI : T.simpleIndices H = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hsS, hsH⟩ := (T.mem_simpleIndices_iff H s).mp hs
    change s ∈ (titsSystem n hn).S at hsS
    rw [titsSystem_S] at hsS
    obtain ⟨a, rfl⟩ := hsS
    have ha : simpleRepresentative P rfl a ∈
        T.bruhatCell (simpleReflection n hn a) := by
      rw [simpleReflection, ← cell_eq_bruhatCell]
      exact (mem_cell_iff P rfl _ _).mpr
        ⟨1, (borel P).one_mem, 1, (borel P).one_mem, by
          simpa only [one_mul, mul_one] using (weylRepresentative_simple P rfl a).symm⟩
    exact simple_not_mem_normalizer n hn a (hsH ha)
  calc
    H = T.standardParabolic (T.simpleIndices H) :=
      T.subgroup_eq_standardParabolic_simpleIndices H hB
    _ = T.B := by rw [hI, T.standardParabolic_empty]

/-- The actual positive subgroup has precisely the descended Borel as normalizer. -/
theorem normalizer_unipotent_eq_borel (P : Parameters) (hp : P.prime = 2) :
    Subgroup.normalizer (unipotent P) = borel P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact normalizer_unipotent_binary n hn

end Triality.Standard.ConcreteBruhat
