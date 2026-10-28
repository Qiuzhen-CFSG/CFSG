module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.Representation.AlternatingSevenConjugatePair.Model
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Cubic

/-!
# The S₇ and triple-M₂₂ branches of 14.4.6

The conjugate-pair theorem gives moved rank four for every involution of S₇.
The H.12 bound gives at least four on the faithful irreducible binary
12-space of the genuine triple cover, including ambient outer involutions.
Both calculations are applied to the literal H/O₂(H) action on U/Z(U)
through `SourceAction`; a group isomorphism alone is insufficient.

The notation Z₂/M̂₂₂ is an extension of the triple cover by an involution,
not a double central cover of M₂₂. Its cubic center is retained by
`IsTripleM22` and the actual generalized Fitting subgroup equality.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, 14.4.2(4),(6)
and 14.4.6, printed pp.1006,1008; H.8 and H.12.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory

variable {H V : Type*} [Group H] [Finite H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]

omit [Finite H] in
/-- The source S₇ alternative has moved rank four, including the odd involutions. -/
theorem SourceAction.symmetricSeven_movedRank
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 7))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Module.Finite (ZMod 2) W]
    (D : AlternatingSevenConjugatePair.Pair W) (f : V ≃ₗ[ZMod 2] W)
    (hf : ∀ a v, f (d.representation a v) = D.representation (e a) (f v))
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) : d.movedRank a = 4 := by
  have he := fixedCodim_map_equivariant d.representation D.representation
    e.toMonoidHom f hf (zpowers a)
  rw [MonoidHom.map_zpowers] at he
  change fixedCodim d.representation (zpowers a) =
    fixedCodim D.representation (zpowers (e a)) at he
  rw [D.involution_fixedCodim (e a) ((orderOf_injective e.toMonoidHom e.injective a).trans ha)] at he
  simpa only [SourceAction.movedRank, SourceAction.moved,
    fixedCodim_zpowers_eq_displacement_rank] using he

/-- The source triple-M₂₂ alternative moves at least four binary dimensions.
The actor, its generalized Fitting subgroup, and the cubic center all remain
in the literal two-core quotient. -/
theorem SourceAction.tripleM22_movedRank
    (d : SourceAction H U V)
    (L : Subgroup (H ⧸ pCore 2 H))
    (hL : CFSG.Quasithin.ChapterH.Section10To12.IsTripleM22 L)
    (hF : generalizedFitting (H ⧸ pCore 2 H) = L)
    [d.representation.IsIrreducible] (hd : Module.finrank (ZMod 2) V = 12)
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) : 4 ≤ d.movedRank a := by
  change 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (d.representation a - LinearMap.id))
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  exact CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.four_le_fixedCodim_involution
    L hL hF d.representation d.faithful hd a ha

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
