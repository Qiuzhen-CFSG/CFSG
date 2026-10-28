module

public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Direct
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceHeld
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models

/-!
# The six remaining sporadic FF source branches

On the original B.4 source domain, the actual Theorem C list reduces to
M12, M22, M23, M24, J2 and HS. The four direct FF exclusions and the full
Held cubic exclusion discharge every other entry. Each surviving alternative
retains the literal central quotient of the original component; no model
recognition or no-offender conclusion is assumed for these six alternatives.

Source: Aschbacher--Smith B.4.2, printed p.86; K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The exact remaining quotient alternatives, with all five exclusions applied
to the actual source action. -/
theorem remaining_central_quotient (h : RankOne.SourceHypotheses ρ L)
    (hff : IsFFModule ρ)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel (L ⧸ center L)) :
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m22.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m23.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m24.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.j2.Carrier) ∨
    Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.hs.Carrier) := by
  rcases hm with ⟨name, hne, he⟩ | he
  · cases name with
    | m11 => exact (not_ff_m11 h he hff).elim
    | m12 => exact Or.inl he
    | m22 => exact Or.inr (Or.inl he)
    | m23 => exact Or.inr (Or.inr (Or.inl he))
    | m24 => exact Or.inr (Or.inr (Or.inr (Or.inl he)))
    | j2 => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he))))
    | hs => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he))))
    | j3 => exact (hne rfl).elim
    | j4 => exact (not_ff_j4 h he hff).elim
    | he => exact (held_impossible h he).elim
    | ru => exact (not_ff_ru h he hff).elim
  · exact (not_ff_j1 h he hff).elim

end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
