module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.EndNodeRank
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Excluding the exterior-five row for the rank-one source actor

Restrict the original actor to the marked component and map it by the source
SL₅(2) identification. Both maps preserve its binary rank. Therefore a rank-one
actor cannot have the literal end-node image demanded by the exterior-five row.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.6.4,
printed pp.345–346, using the offender clause of B.4.2(11), printed p.86.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource

/-- The exact marked image of the original rank-one actor is not an end-node radical. -/
theorem not_endNodeRadical_of_rank_one {G : Type*} [Group G]
    {A L : Subgroup G} (hAL : A ≤ L) (hA : rank A = 1)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) :
    ¬ IsEndNodeRadical ((A.subgroupOf L).map e.toMonoidHom) := by
  intro h
  have hr := h.rank
  rw [rank_map_injective _ e.injective] at hr
  have he : rank (A.subgroupOf L) = rank A :=
    congrArg (Nat.log 2) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv)
  rw [he, hA] at hr
  omega

/-- The exterior-five offender clause contradicts the original rank-one best offender. -/
theorem exteriorFive_offender_contradiction {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) {A L : Subgroup G}
    (hAL : A ≤ L) (hA : rank A = 1) (hbest : IsBestOffender ρ A)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hoff : ∀ B, IsBestOffender ρ B →
      IsEndNodeRadical ((B.subgroupOf L).map e.toMonoidHom)) : False :=
  not_endNodeRadical_of_rank_one hAL hA e (hoff A hbest)

end CFSG.Quasithin.ChapterG.Section06
