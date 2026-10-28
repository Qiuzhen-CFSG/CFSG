module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard.Cardinality
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Marked inputs for the nonbinary natural Chapter 12 branch

The central quotient is the literal D.space / C_D.space(L). Its projection
is transported to V using the original ambient inclusion, so pulling back
a nonzero subspace gives a nontrivial elementary abelian subgroup of G.
The action alternatives retain the full SL3 group, rank-two symplectic
matrices and the six-dimensional natural action of the concrete G2 family.

NonbinaryNaturalInput records only the source hypotheses and the explicit
preceding FF, normalization and action-marking inputs. No elimination or
local-component conclusion is a field. It is the shared input to the missing
11.1--11.5 geometry, not a proof of 11.0.1 or of 12.2.2.
Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
3.2.8(2--4), 11.0.2 and 12.2.2, printed pp.582,759--760,795.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The three actual marked central-quotient actions at issue in 11.0.2(2).
The field-degree restriction is supplied separately. -/
inductive NaturalRankTwoAction (F : BinaryField) : Prop where
  | sl3 (marking : Nonempty (ActionEquiv D.centralQuotientAction (linearNatural F 3)))
  | sp4 (marking : Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2))))
  | g2 (marking : Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural F.Carrier))))

/-- Quotient by the fixed vectors, on the original ambient subgroup V. -/
def toCentralQuotient : V →* Multiplicative D.chosenCentralQuotient :=
  (Submodule.mkQ ((fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype)).toAddMonoidHom.toMultiplicative.comp
      D.spaceEquiv.symm.toMonoidHom

omit [Finite G] in
theorem toCentralQuotient_surjective : Function.Surjective D.toCentralQuotient := by
  intro q
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective
    ((fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
      (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype) q.toAdd
  refine ⟨D.spaceEquiv (Multiplicative.ofAdd v), ?_⟩
  change Multiplicative.ofAdd (Submodule.Quotient.mk
    (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd v))).toAdd) = q
  rw [D.spaceEquiv.symm_apply_apply]
  exact congrArg Multiplicative.ofAdd hv

/-- The actual inverse image in G of a subspace of the chosen central quotient. -/
def centralQuotientPreimage (U : Submodule (ZMod 2) D.chosenCentralQuotient) : Subgroup G :=
  (U.toAddSubgroup.toSubgroup.comap D.toCentralQuotient).map V.subtype

omit [Finite G] in
theorem centralQuotientPreimage_le (U : Submodule (ZMod 2) D.chosenCentralQuotient) :
    D.centralQuotientPreimage U ≤ V := map_subtype_le _

omit [Finite G] in
theorem centralQuotientPreimage_elementary (U : Submodule (ZMod 2) D.chosenCentralQuotient) :
    IsElementaryAbelian 2 (D.centralQuotientPreimage U) := by
  let := D.elementary
  exact IsElementaryAbelian.of_le (D.centralQuotientPreimage_le U)

omit [Finite G] in
theorem centralQuotientPreimage_ne_bot (U : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hU : U ≠ ⊥) : D.centralQuotientPreimage U ≠ ⊥ := by
  intro hz
  apply hU
  apply bot_unique
  intro q hq
  obtain ⟨v, hv⟩ := D.toCentralQuotient_surjective (Multiplicative.ofAdd q)
  have hvU : v ∈ U.toAddSubgroup.toSubgroup.comap D.toCentralQuotient := by
    change (D.toCentralQuotient v).toAdd ∈ U
    rw [hv]
    exact hq
  have hvG : (v : G) ∈ D.centralQuotientPreimage U := mem_map_of_mem _ hvU
  have hv1 : v = 1 := Subtype.ext (mem_bot.mp (hz ▸ hvG))
  have hq0 : q = 0 := by
    have hh := hv.symm
    rw [hv1, map_one] at hh
    exact congrArg Multiplicative.toAdd hh
  exact hq0

omit [Finite G] in
theorem centralQuotientPreimage_twoLocal (U : Submodule (ZMod 2) D.chosenCentralQuotient)
    (hU : U ≠ ⊥) : IsTwoLocal (normalizer (D.centralQuotientPreimage U : Set G)) :=
  ⟨D.centralQuotientPreimage U, D.centralQuotientPreimage_ne_bot U hU,
    @IsElementaryAbelian.isPGroup 2 _ _ (D.centralQuotientPreimage_elementary U), rfl⟩

/-- The explicit inputs retained from the preceding FF and seed reductions.
Every model marking includes its actual group and its intertwining map. -/
structure NonbinaryNaturalInput where
  source : Hypothesis1223 KnownSimple.IsKnownSimple T L
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  sylow_normalizes : (T : Subgroup G) ≤ normalizer (V : Set G)
  ff : IsFFModule (normalizerRepresentation D.chosenAction)
  field : BinaryField
  nonbinary : 1 < field.degree
  faithful : Function.Injective D.centralQuotientAction
  natural : D.NaturalRankTwoAction field

namespace NonbinaryNaturalInput
variable {D} (S : D.NonbinaryNaturalInput)

/-- The original FSU seed remains V under the supplied T-normalization. -/
theorem unchanged_seed : (D.fundamentalSetup S.source.toHypothesis1221).moduleSubgroup = V := by
  rw [D.fundamentalSetup_module]
  exact le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
    S.sylow_normalizes) (le_componentOrbit V T)

include S in
/-- The multiple-overgroup premise supplies the actual standing guard. -/
theorem outside_of_many (M : Subgroup G) (hM : IsMaximalTwoLocal M)
    (hTM : (T : Subgroup G) ≤ M) : Chapter3.HasMaximalOutside T M :=
  Chapter3.hasMaximalOutside_of_many T S.many M hM hTM

end NonbinaryNaturalInput

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
