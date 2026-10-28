module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCentralizer.FixedGeometry
public import Theory.Representation.BinaryNaturalDual.RadicalFixedBound
public import Theory.GroupTheory.PRadicalSylowNormalizer

/-!
# Radical fixed spaces under the published natural-plus-dual marking

Transport the literal radical through the same actor equivalence used by the
module marking. The binary matrix and linear-automorphism actions agree
pointwise. The native radical bound therefore bounds the original fixed space
by the natural degree, with no compatible-parabolic premise.
Source: Aschbacher--Smith B.5.1 and C.4.8, pp.99--103,154.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The published natural-plus-dual action has radical fixed dimension at most d. -/
theorem finrank_radical_fixed_le (ρ : Representation (ZMod 2) G V)
    (P : Subgroup G) (hP : P.IsPRadical 2) {d : ℕ} (hd : 0 < d)
    (hnat : IsNaturalPlusDual ρ d) :
    Module.finrank (ZMod 2) (fixedSpace ρ P) ≤ d := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨a⟩ := hnat
  let E : V ≃ₗ[ZMod 2] BinaryNaturalDual.CoordinateSpace d := a.linearEquiv
  let e := a.groupEquiv.trans (BinaryLinear.OuterCyclic.slEquivLinear d)
  have hi (g : G) (v : V) : E (ρ g v) =
      BinaryNaturalDual.naturalDualRepresentation (e g) (E v) := by
    change a.linearEquiv (ρ g v) = _
    rw [a.intertwines]
    exact action_apply d (a.groupEquiv g) (E v)
  have he := fixedSpace_map_equivariant ρ
    (BinaryNaturalDual.naturalDualRepresentation (V := BinaryLinear.OuterCyclic.Space d))
    e.toMonoidHom E hi P
  have hdim := (E.ofSubmodules _ _ he).finrank_eq
  rw [hdim]
  simpa only [Module.finrank_fin_fun] using
    BinaryNaturalDual.finrank_fixedSpace_radical_le (V := BinaryLinear.OuterCyclic.Space d)
      (P.map e.toMonoidHom) (hP.map_equiv e)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.NaturalDualCentralizer
