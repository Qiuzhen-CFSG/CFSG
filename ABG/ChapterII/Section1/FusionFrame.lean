module
public import ABG.ChapterII.Section1.SmallSubgroups
public import ABG.ChapterII.Section1.FusionPatterns

/-!
# Choosing the quasi-dihedral fusion frame

A finite group with a specified quasi-dihedral Sylow two-subgroup admits
ambient four and quaternion subgroups forming the frame used in the fusion
alternatives. These are actual subgroups contained in the specified Sylow
subgroup, not merely abstract models.

Lemma II.1.1(ii) supplies four and quaternion representatives inside the
Sylow subgroup. Map them along the Sylow subtype homomorphism; its injectivity
preserves the four-group cardinality and exponent and transports the
quaternion isomorphism. The image subgroups retain the required inclusions.
This justifies the choices preceding ABG Chapter II §1 Proposition 1,
article page 10 of `refs/latex/alperin-brauer-gorenstein.tex`.
-/

namespace ABG
/-- A quasi-dihedral Sylow subgroup admits actual ambient four and quaternion representatives. -/
public theorem exists_quasiDihedralFusionFrame
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hS : Stellmacher.IsSemidihedralGroup S) :
    ∃ T Q : Subgroup G, QuasiDihedralFusionFrame S T Q := by
  obtain ⟨U, V, hU, ⟨hV⟩, _, _, _⟩ := QuasiDihedral.four_quaternion_subgroups hS
  let eU := U.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
  let eV := V.equivMapOfInjective (S : Subgroup G).subtype (S : Subgroup G).subtype_injective
  refine ⟨U.map (S : Subgroup G).subtype, V.map (S : Subgroup G).subtype,
    hS, Subgroup.map_subtype_le U, Subgroup.map_subtype_le V, ?_, ?_⟩
  · exact {
      card_four := (Nat.card_congr eU.symm.toEquiv).trans hU.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eU.symm).trans hU.exponent_two }
  · exact ⟨eV.symm.trans hV⟩
end ABG
