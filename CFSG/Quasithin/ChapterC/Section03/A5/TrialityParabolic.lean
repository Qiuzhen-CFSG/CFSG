module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreAction
public import CFSG.Quasithin.Chapter1.Section01
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Central
public import Theory.GroupTheory.PPerfectHom

/-!
# Full-Sylow local obstructions in the triality parabolics

A short local C-component has square-one commutator with the full parabolic
radical. At the arms node, the perfect-actor root calculation kills it; at
the central node, first-layer rigidity puts it inside the radical. In either
case it is a two-perfect two-group, contradicting its nonzero block module.
Both full parabolics have characteristic two, including their torus factors.

These are the intrinsic He and full-Sylow nonlocality clauses in the selected
parabolic escape for Aschbacher--Smith 2.4.25, printed p.543. The proof applies
at q=2 and needs no global subnormality or Sylow index hypothesis.
-/

public section
namespace CFSG.Quasithin.ChapterC
open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

/-- Neither full triality parabolic admits a short member of its full-Sylow
local C-component family. -/
theorem triality_parabolic_not_local_short (P : Parameters) (hp : P.prime = 2)
    (a : Node) (B : Subgroup (parabolic P a)) (hb : IsShort B)
    (S : Sylow 2 (parabolic P a)) :
    B ∉ ChapterA.Section03.localCComponents S := by
  intro hl
  have hsq : ∀ x ∈ ⁅(radical P a).subgroupOf (parabolic P a), B⁆,
      (x : parabolic P a) ^ 2 = 1 := by
    rw [← parabolic_twoCore_eq P hp a]
    exact fun _ hx => local_short_core_commutator_square S B hb hl hx
  let H := B ⊔ (S : Subgroup (parabolic P a))
  let : Group.IsPerfect (B.subgroupOf H) := hl.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f :=
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ H from le_sup_left)).surjective
  have htwo : IsPGroup 2 B := by
    cases a with
    | arms =>
      rw [arms_perfect_eq_bot_of_commutator_squares P hp B hsq]
      exact IsPGroup.of_bot
    | central =>
      exact (RadicalCoordinates.radical_isPGroup P hp .central).comap_subtype.to_le
        (CentralRootSquare.le_radical_of_commutator_squares P hp B hsq)
  have hone := hb.twoPerfect.hom_eq_one_of_isPGroup htwo (MonoidHom.id B)
  apply hb.blockU_ne_bot
  apply eq_bot_iff.mpr
  intro b _
  exact mem_bot.mpr (DFunLike.congr_fun hone b)

/-- The full root parabolic has characteristic two, including its torus. -/
theorem triality_parabolic_mem_He (P : Parameters) (hp : P.prime = 2) (a : Node) :
    parabolic P a ∈ Chapter1.He (Carrier P) := by
  apply Chapter1.mem_He_iff.mpr
  rw [parabolic_twoCore_eq P hp a]
  intro x hx
  apply parabolic_centralizer_radical_le P hp a
  refine ⟨x.property, ?_⟩
  intro r hr
  exact congrArg Subtype.val (hx ⟨r, radical_le_parabolic P a hr⟩ hr)

end CFSG.Quasithin.ChapterC
