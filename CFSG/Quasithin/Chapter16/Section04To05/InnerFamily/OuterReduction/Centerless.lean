module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Consequences

/-!
# The centerless part of the outer-action reduction

This file records the model facts which are used after the alternatives in
16.4.9 have been reduced to the centerless case.  The two sporadic rows
`M₂₂` and `HS` are kept as separate interfaces: in those rows the proof uses
the subgroup `T_r`, its centre, and a normalizer element which fuses `r` with
`rv`.  Every other row uses the two source calculations that remain after the
16.4.6 exclusions: the residual has even order and the involutions in `rL`
are conjugate under `L`.

The interfaces deliberately contain actual subgroup maps and conjugation
equations.  A family name or an isomorphism of a centralizer does not supply
either of these facts.  Thus the source model calculations can be discharged
in their own modules and then fed to the two small assembly lemmas below.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1190--1191.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction

open Subgroup
open CFSG.Quasithin.Chapter16.Intersections

variable {G : Type*} [Group G]

/-- The image in `G` of the centre of an ambient subgroup.  This is useful
because `Subgroup.center Tr` is a subgroup of the subtype `Tr`, whereas the
source writes the centre as a subgroup of the ambient group. -/
def centerImage (Tr : Subgroup G) : Subgroup G :=
  (Subgroup.center Tr).map Tr.subtype

/-- The concrete data in the centerless `M₂₂` and `HS` rows.

`Tr` is the source `T_r`.  The equality `center_eq` and `center_disjoint`
express the direct-product centre `⟨r⟩ × ⟨v⟩`; the two membership fields keep
the equality tied to the actual subgroup rather than to an abstract group
family.  The last field is the model normalizer calculation. -/
structure CenterlessCoverFusionData (T : Sylow 2 G) (r : G)
    (L : Subgroup G) where
  Tr : Subgroup G
  Tr_le_sylow : Tr ≤ (T : Subgroup G)
  r_mem_Tr : r ∈ Tr
  v : G
  v_mem_Tr : v ∈ Tr
  center_eq : centerImage Tr = zpowers r ⊔ zpowers v
  center_disjoint : Disjoint (zpowers r) (zpowers v)
  r_mem_center : r ∈ centerImage Tr
  v_mem_center : v ∈ centerImage Tr
  centerless : Subgroup.center L = ⊥
  v_mem_residual : v ∈ OuterResidual.involutionResidual L r
  v_ne_one : v ≠ 1
  conjugator : ∃ l ∈ L, l ∈ normalizer (Tr : Set G) ∧
    MulAut.conj l r = r * v

/-- The `M₂₂` specialization of the centerless cover interface.  It has its
own name so the source assembly can discharge it independently of `HS`. -/
abbrev M22CenterlessFusionData {G : Type*} [Group G] :=
  CenterlessCoverFusionData (G := G)

/-- The `HS` specialization of the centerless cover interface.  It has its own
name so the source assembly can discharge it independently of `M₂₂`. -/
abbrev HSCenterlessFusionData {G : Type*} [Group G] :=
  CenterlessCoverFusionData (G := G)

/-- The model calculation for every centerless row other than `M₂₂` and `HS`.
The second field is intentionally quantified over the actual residual
elements; it is the conjugacy premise needed by
`residualFusionWitness_of_even_of_coset_conjugacy`. -/
structure RemainingCenterlessFusionData (r : G) (L : Subgroup G) where
  centerless : Subgroup.center L = ⊥
  residual_even : Even (Nat.card (OuterResidual.involutionResidual L r))
  involutions_conjugate : ∀ v ∈ L, orderOf (r * v) = 2 →
    ∃ l ∈ L, MulAut.conj l r = r * v

/-- The three source rows handled by this file.  In particular, the two
sporadic rows are not hidden in the remaining-model alternative. -/
inductive CenterlessResidualFusionData (T : Sylow 2 G) (r : G) (L : Subgroup G)
  | m22 (data : M22CenterlessFusionData T r L)
  | hs (data : HSCenterlessFusionData T r L)
  | remaining (data : RemainingCenterlessFusionData r L)

/-- The normalizer calculation in the centerless `M₂₂` row gives the forbidden
residual fusion witness. -/
theorem residualFusionWitness_of_m22_centerless
    {T : Sylow 2 G} {r : G} {L : Subgroup G}
    (data : M22CenterlessFusionData T r L) :
    ResidualFusionWitness L r := by
  obtain ⟨l, hl, _, hconj⟩ := data.conjugator
  exact ⟨l, hl, data.v, data.v_mem_residual, data.v_ne_one, hconj⟩

/-- The normalizer calculation in the centerless `HS` row gives the forbidden
residual fusion witness. -/
theorem residualFusionWitness_of_hs_centerless
    {T : Sylow 2 G} {r : G} {L : Subgroup G}
    (data : HSCenterlessFusionData T r L) :
    ResidualFusionWitness L r := by
  obtain ⟨l, hl, _, hconj⟩ := data.conjugator
  exact ⟨l, hl, data.v, data.v_mem_residual, data.v_ne_one, hconj⟩

/-- Even residual order and conjugacy of the involutions in `rL` produce the
witness in every remaining centerless model. -/
theorem residualFusionWitness_of_remaining_centerless
    [Finite G] {r : G} {L : Subgroup G} (hr2 : orderOf r = 2) (hrL : r ∉ L)
    (data : RemainingCenterlessFusionData r L) :
    ResidualFusionWitness L r := by
  exact residualFusionWitness_of_even_of_coset_conjugacy hr2 hrL
    data.residual_even data.involutions_conjugate

/-- Assemble the three centerless model rows. -/
theorem residualFusionWitness_of_centerless_models
    [Finite G] {T : Sylow 2 G} {r : G} {L : Subgroup G}
    (hr2 : orderOf r = 2) (hrL : r ∉ L)
    (data : CenterlessResidualFusionData T r L) :
    ResidualFusionWitness L r := by
  cases data with
  | m22 data => exact residualFusionWitness_of_m22_centerless data
  | hs data => exact residualFusionWitness_of_hs_centerless data
  | remaining data => exact residualFusionWitness_of_remaining_centerless hr2 hrL data

/-- The full 16.4.9 centerless contract, with all earlier source outputs kept
explicit.  The local setup, the empty-family assumption, `pCore 2 L = ⊥`, and
the exclusion of the two exceptional alternatives belong to the caller; this
theorem only consumes the actual model calculations recorded above. -/
theorem residualFusionWitness_of_centerless
    {K : CFSG.Quasithin.GroupClass} [Finite G]
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (_hG : CFSG.Quasithin.Chapter16.Hypothesis1611 K G)
    (_h : IntersectionSetup T z L g R)
    (_hr : r ∈ R) (hr2 : orderOf r = 2)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (_hsmall : OrderTwoOutsideDeltaZero L)
    (_hempty : ¬ (deltaZero L).Nonempty)
    (_hpCore : pCore 2 L = ⊥)
    (_hnotExceptional : ¬ InnerFamilyExceptionalCase L r)
    (data : CenterlessResidualFusionData T r L) :
    ResidualFusionWitness L r := by
  have hrL : r ∉ L := by
    intro hrL
    exact hrout (Subgroup.mem_sup_right hrL)
  exact residualFusionWitness_of_centerless_models hr2 hrL data

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction
