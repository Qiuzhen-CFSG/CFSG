module

public import CFSG.Quasithin.Chapter10.SourceA5PointParabolicCenter
public import Theory.AtlasPort.LinearGroups.G2.LongLocalFixer

/-!
# The marked G₂ component in the original A5 point-centralizer proof

The first local residual is impossible by the core-center bound. An actor
normalizing the containing perfect component and centralizing the original
local subgroup therefore fixes a marked second local residual on its central
quotient. The model restriction theorem and faithful central descent imply
that the actor centralizes the containing component itself.

These are the two marked G₂(4) alternatives in the quasisimple inspection
of Aschbacher–Smith 10.2.9, printed pp.750–751. The marking remains an actual
subgroup equality under the literal central quotient map.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
  {L I U : Subgroup G}

/-- Actors fixing the original local subgroup centralize a perfect component
when its literal central image is the second G₂ parabolic residual. -/
theorem source_g2_second_local_component_centralized
    [Group.IsPerfect I] {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (eI : (I ⧸ center I) ≃* Atlas.G2.Model F)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        Atlas.G2.LieParabolicSetup.local₂)
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  intro u hu
  let a : MulAut I := I.normalizerMonoidHom ⟨u, hUN hu⟩
  have ha : a = 1 := by
    apply Atlas.G2.LieParabolicSetup.perfect_cover_local₂_fixer_eq_one hq eI
      (L.subgroupOf I) hmark a
    intro l hl
    apply Subtype.ext
    change u * l.val * u⁻¹ = l.val
    exact mul_inv_eq_iff_eq_mul.mpr ((hUL hu l.val hl).symm)
  intro i hi
  have hh := congrArg (fun f : MulAut I => (f ⟨i, hi⟩ : G)) ha
  change u * i * u⁻¹ = i at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- Both standard G₂(4) markings give the required centralization in the
actual original A5 setup; the first marking is ruled out internally. -/
theorem source_a5_g2_component_centralized
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hLI : L ≤ I) [Group.IsPerfect I]
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (eI : (I ⧸ center I) ≃* Atlas.G2.Model F)
    (hmark : (L.subgroupOf I).map
      (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        Atlas.G2.LieParabolicSetup.local₁ ∨
      (L.subgroupOf I).map (eI.toMonoidHom.comp (QuotientGroup.mk' (center I))) =
        Atlas.G2.LieParabolicSetup.local₂)
    (hUN : U ≤ normalizer (I : Set G)) (hUL : U ≤ centralizer (L : Set G)) :
    U ≤ centralizer (I : Set G) := by
  rcases hmark with hmark | hmark
  · exact (source_a5_point_not_g2_first_parabolic D e hLI hF eI hmark).elim
  · exact source_g2_second_local_component_centralized (by omega) eI hmark hUN hUL

end CFSG.Quasithin.Chapter10
