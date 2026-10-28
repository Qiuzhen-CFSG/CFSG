module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionSetup
public import CFSG.Quasithin.ChapterC.Section02.SourceHypotheses
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Literal residuals in the exceptional branch of 12.3.3

The point residual is O²(C_{N(V)}(z)), embedded in the original group;
its perfect residual is the solvable residual, not the two-core. The
local point stabilizers in N(L) and N(V) agree by the original TI theorem.
Characteristicity of both residuals makes V normalize the perfect residual.
Thus the source commutator equality already implies V is contained in it,
before proving its normality in the full point centralizer.

`FourResidualData` states the earlier source conclusions needed for the
remaining component and block arguments. Its construction is an outstanding
obligation; this module does not assert C.2.8 from the A₇ setup.
Source: Aschbacher--Smith, Lemma 12.3.3, printed p.808, using 12.2.12.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup

/-- G_z, the full ambient point centralizer. -/
abbrev fourPointCentralizer (_S : Setup T L V) (z : G) : Subgroup G :=
  centralizer ({z} : Set G)

/-- M_z=C_{N(L)}(z). -/
abbrev fourPointLocal (_S : Setup T L V) (z : G) : Subgroup G :=
  normalizer (L : Set G) ⊓ centralizer ({z} : Set G)

/-- C_{M_V}(z), with M_V=N_G(V). -/
abbrev fourPointModuleNormalizer (_S : Setup T L V) (z : G) : Subgroup G :=
  normalizer (V : Set G) ⊓ centralizer ({z} : Set G)

/-- The source L_z is the two-residual, embedded along the subgroup inclusion. -/
def fourPointResidual (S : Setup T L V) (z : G) : Subgroup G :=
  (pResidual 2 (S.fourPointModuleNormalizer z)).map
    (S.fourPointModuleNormalizer z).subtype

/-- K_z=L_z^∞ is the solvable residual of the literal L_z. -/
def fourPointPerfect (S : Setup T L V) (z : G) : Subgroup G :=
  (solvableResidual (S.fourPointResidual z)).map (S.fourPointResidual z).subtype

/-- Q=O₂(K_z T), with the original T. -/
abbrev fourPointCore (S : Setup T L V) (z : G) : Subgroup G :=
  (S.fourPointPerfect z ⊔ (T : Subgroup G)).pCoreIn 2

/-- Y=C_{G_z}(K_z/O₂(K_z)); normalizing K_z is part of membership. -/
abbrev fourPointSection (S : Setup T L V) (z : G) : Subgroup G :=
  ChapterA.Section04.twoSectionCentralizer (S.fourPointPerfect z)
    (S.fourPointCentralizer z)

variable (S : Setup T L V)

/-- The two source point-local subgroups really are equal. -/
theorem four_pointLocal_eq
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointLocal z = S.fourPointModuleNormalizer z := by
  apply le_antisymm
  · exact le_inf (S.hypothesis.source_point_normalizes_chosen structural S.chosen hz hz1 le_rfl)
      inf_le_right
  · exact inf_le_inf_right _ (S.normalizer_le_component structural)

/-- The perfect point residual is normalized by the actual point-local group. -/
theorem four_pointLocal_normalizes_perfect
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointLocal z ≤ normalizer (S.fourPointPerfect z : Set G) := by
  rw [S.four_pointLocal_eq structural hz hz1]
  exact (le_normalizer_embedded_pResidual 2 (S.fourPointModuleNormalizer z)).trans
    (normalizer_le_normalizer_characteristic_image (S.fourPointResidual z)
      (solvableResidual (S.fourPointResidual z)))

/-- V lies in M_z because it is elementary abelian and lies in T. -/
theorem four_module_le_pointLocal {z : G} (hz : z ∈ V) :
    V ≤ S.fourPointLocal z := by
  let := S.chosen.elementary
  refine le_inf (S.chosen.le_sylow.trans S.chosen.sylow_normalizes_component) ?_
  intro v hv
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg V.subtype (mul_comm (⟨v,hv⟩ : V) ⟨z,hz⟩)

/-- Escape supplies the strict local inclusion needed in C.2.8 applications. -/
theorem four_pointLocal_lt
    (escape : CentralizerEscape T)
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    S.fourPointLocal z < S.fourPointCentralizer z := by
  refine lt_of_le_of_ne inf_le_right ?_
  intro he
  exact S.four_all_pointCentralizers_escape escape e hd hz hz1 (he.symm.le.trans inf_le_left)

/-- Earlier-source output to be constructed from the four-dimensional setup.
There is no ambient normality or exclusion conclusion in this interface. -/
structure FourResidualData (z : G) : Prop where
  pushingUp : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple
    (S.fourPointCentralizer z) (S.fourPointLocal z) (S.fourPointPerfect z)
    (S.fourPointCore z) V
  faithful : ChapterA.Section04.IsFaithfulSignalizerType (S.fourPointPerfect z)
  local_member : S.fourPointPerfect z ∈ Chapter1.L G (T : Subgroup G)
  quotient : ClassicalGroup.IsPSL ((S.fourPointPerfect z) ⧸ pCore 2 (S.fourPointPerfect z)) 3 2
  moved : V = ⁅V, S.fourPointPerfect z⁆
  section_sylow : Chapter1.IsSylowIn 2 (S.fourPointCore z) (S.fourPointSection z)

/-- The original commutator equality puts V inside K_z, using its already
proved local normalization; no normality in G_z is presumed. -/
theorem FourResidualData.module_le {S : Setup T L V} {z : G}
    (D : S.FourResidualData z)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hz : z ∈ V) (hz1 : z ≠ 1) : V ≤ S.fourPointPerfect z := by
  exact D.moved.le.trans (le_normalizer_iff_commutator_le_right.mp
    ((S.four_module_le_pointLocal hz).trans
      (S.four_pointLocal_normalizes_perfect structural hz hz1)))

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
