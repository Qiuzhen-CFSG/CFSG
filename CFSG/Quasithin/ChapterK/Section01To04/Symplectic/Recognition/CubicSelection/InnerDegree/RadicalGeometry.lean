module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.RadicalGeometry.Placement
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.RadicalGeometry.Invariant

/-!
# Radical geometry for inner symplectic offenders

Every elementary abelian two-subgroup of Sp₄(2ʳ) lies in a conjugate of one
of the two parabolic radicals. A nontrivial subgroup of either radical
invariant under its full normalizer is its distinguished central root or
the whole radical. Both central-root alternatives are retained.

The placement proof uses the two outside Sylow coordinates and their square
formula. The invariant-subgroup proof uses the actual natural central
quotient, commutator generation in the determinant-one local group, and
the diagonal torus action on the central root.

The source application below discharges these two geometry premises of the
inner degree reduction. Five-root and two-radical conjugate generation
remain explicit independent premises, owned by the final assembly.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2
part 1A, author manuscript pp.38--39; Aschbacher--Smith K.3.4, printed
pp.456--457 of the combined manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree

variable {F V G : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Group G] [Finite G] {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The actual ambient inner offender gives degree at most 12r once the
independent root and radical conjugate-generation premises are supplied. -/
theorem source_ambient_inner_degree_of_radical_geometry {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hF : Nat.card F = 2 ^ r) (hr : 1 < r)
    (e : L ⧸ center L ≃* Sp F)
    (hroot : ∀ i : Bool, ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (hrad : ∀ i : Bool, ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r :=
  source_ambient_inner_degree_of_geometry h hF e
    (elementary_placement hF (by omega)) (normalized_radical_subgroup hF hr)
    hroot hrad A hAL hA hcodim

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
