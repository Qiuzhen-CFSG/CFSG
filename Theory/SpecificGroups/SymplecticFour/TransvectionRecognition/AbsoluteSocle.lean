module
public import Theory.Representation.RankOneNormalizer
public import Theory.SpecificGroups.SymplecticFour.InvolutionTypes
public import Theory.Representation.SymplecticNatural

/-!
# Absolute irreducibility of the literal transvection socle

G.4.9 supplies an F-irreducible socle normalized by the original group.
Any original rank-one element normalizes this same socle. The generic
commuting-algebra argument then upgrades irreducibility to absolute
irreducibility over F. No transvection inside the socle is required.
This removes the extension-field natural alternative in the representation
inspection of Aschbacher--Smith G.4.1, printed p.342.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open Subgroup InvolutionTypes
variable {F : Type*} [Field F]

/-- The actual irreducible subgroup is absolutely irreducible when an
ambient rank-one element normalizes it. -/
theorem subgroup_absolutelyIrreducible_of_isB1_normalizer
    (N : Subgroup (Sp F))
    (hi : Representation.IsIrreducible ((Representation.symplecticNatural 2).comp N.subtype))
    (t : Sp F) (ht : t∈normalizer (N:Set (Sp F))) (hr : IsB1 t) :
    Representation.IsAbsolutelyIrreducible
      ((Representation.symplecticNatural 2).comp N.subtype) := by
  let _ := hi
  apply Representation.RankOneNormalizer.subgroup_absolutelyIrreducible_of_rank_one_normalizer
    (Representation.symplecticNatural 2) N t ht
  · simp
  · exact hr.2
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
