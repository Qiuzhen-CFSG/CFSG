module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallChiefKernel
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenDisplacement
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions
public import Theory.GroupAction.NormalPChiefSeries.FixedCodimension
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter

/-!
# The two-chief-factor displacement bound on the chosen span

The literal elementary H-span has two noncentral chief factors, each with
action kernel O₂(H). The actual S₃ wreath C₂ quotient makes H solvable.
The proved solvable irreducible-action theorem excludes strong offenders on
each faithful chief image, so every elementary actor pays at least its
rank modulo O₂(H) on each factor. Superadditivity along the genuine chief
flag then gives twice that rank as a lower bound on total displacement.
The quotient maps are the original chief projections; no extension is split.

This proves the numerical consequence of the transvection argument directly,
without needing simultaneous markings of the two natural actions or assuming
that the actor is quadratic. The marked-plane construction remains with the
independent offender-plane development. The sole additional source premise is
the preceding residual uniqueness, whose producer is the small-parabolic
development; this module assumes no displacement or corank estimate.

The conjugate application combines this bound with the opposite-span upper
bound three. Inverse conjugation and the terminal contradiction belong to the
critical-track assembly.

Source: Aschbacher--Smith, 15.1.12, Notation 15.2.9 and the end of Section 15.2,
printed pp.1090, 1110 and 1120; the solvable estimate is B.1.8(3), printed p.70.
-/

public section

open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterD ChapterD.UniqueFactor ChapterE NoncentralChiefRefinement

private theorem wreath_core_solvable {H : Type*} [Group H] [Finite H]
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))) :
    Group.IsSolvable H := by
  obtain ⟨e⟩ := he
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr
    ⟨inferInstance, inferInstance⟩

private theorem solvable_chief_rank_lower {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (hs : Group.IsSolvable H) (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hk : (Representation.BinaryOffender.actionHom ρ).ker = pCore 2 H) :
    Nat.log 2 ((pCore 2 H).relIndex A) ≤ fixedCodim ρ A := by
  have hratio := ChapterB.solvable_irreducible_image_ratio_ge_one ρ hs
  have hn : ¬ IsStrongFFModule (Representation.BinaryOffender.imageRepresentation ρ) :=
    fun h => (not_lt_of_ge hratio) ((isStrongFFModule_iff_quadraticRatio_lt_one _).mp h)
  have hb : rank (actionSubgroup ρ A) ≤ fixedCodim ρ A := by
    by_cases hz : actionSubgroup ρ A = ⊥
    · rw [hz, Representation.BinaryOffender.rank_bot]
      exact Nat.zero_le _
    · by_contra! hlt
      apply hn
      refine ⟨actionSubgroup ρ A, ⟨hz, IsElementaryAbelian.map _⟩, ?_⟩
      simpa only [fixedCodim_actionSubgroup] using hlt
  rwa [rank, actionSubgroup, ← relIndex_ker, hk] at hb

variable {G : Type*} [Group G] [Finite G]

private theorem normal_fixedCodim_ambient (H U A : Subgroup G)
    (hUH : U ≤ H) (hAH : A ≤ H) [(U.subgroupOf H).Normal]
    [IsElementaryAbelian 2 (U.subgroupOf H)] :
    fixedCodim (normalRepresentation (U.subgroupOf H)) (A.subgroupOf H) =
      subgroupCorank U (U ⊓ centralizer (A : Set G)) := by
  have hm : ((U.subgroupOf H) ⊓ centralizer (A.subgroupOf H : Set H)).map H.subtype =
      U ⊓ centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, fun a ha => congrArg Subtype.val (hy.2 ⟨a, hAH ha⟩ ha)⟩
    · intro hx
      exact ⟨⟨x, hUH hx.1⟩, ⟨hx.1, fun a ha => Subtype.ext (hx.2 a ha)⟩, rfl⟩
  rw [normalRepresentation_fixedCodim_eq_rank_difference,
    Subgroup.log_card_sub_log_card_eq_log_relIndex _ _ inf_le_left,
    ← relIndex_map_map_of_injective _ _ H.subtype_injective,
    hm, map_subgroupOf_eq_of_le hUH]
  rfl

omit [Finite G] in
private theorem core_corank_subgroupOf (H A : Subgroup G) (hAH : A ≤ H) :
    subgroupCorank A (A ⊓ twoCoreIn H) =
      Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) := by
  rw [subgroupCorank, inf_relIndex_left,
    ← relIndex_map_map_of_injective _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le hAH]
  rfl

/-- The exact lower estimate used by the critical-track consumer, uniformly
for every elementary abelian subgroup of H. Residual uniqueness is the
preceding 15.2 small-parabolic input. -/
theorem chosen_span_chief_displacement_lower
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAH : A ≤ H) :
    2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
      subgroupCorank (conjugateSpan H V)
        (conjugateSpan H V ⊓ centralizer (A : Set G)) := by
  classical
  let := h.prepared.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (h.prepared.chief_data h.ambient T h.empty h.maximal h.centralizing H hg.outside).1
  have hUH : conjugateSpan H V ≤ H := by
    rw [UniqueFactor.conjugateSpan_eq]
    exact conjugateSpanBy_le_self
      ((h.prepared.inside_core H hg.outside).trans (twoCore_le H))
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  obtain ⟨s⟩ := SeriesOn.exists_series U
  obtain ⟨i, j, hij, ⟨_, hki, _⟩, ⟨_, hkj, _⟩⟩ :=
    h.two_faithful_chief_factors_of_residual_unique hunique hg.outside s
  have hs := wreath_core_solvable hg.quotient
  have hi : Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) ≤
      fixedCodim (s.factorRepresentation i) (A.subgroupOf H) := by
    let := s.factorRepresentation_irreducible i
    exact solvable_chief_rank_lower _ hs _ hki
  have hj : Nat.log 2 ((pCore 2 H).relIndex (A.subgroupOf H)) ≤
      fixedCodim (s.factorRepresentation j) (A.subgroupOf H) := by
    let := s.factorRepresentation_irreducible j
    exact solvable_chief_rank_lower _ hs _ hkj
  have hpair := Finset.sum_le_sum_of_subset
    (f := fun k => fixedCodim (s.factorRepresentation k) (A.subgroupOf H))
    (show ({i, j} : Finset (Fin s.series.length)) ⊆ Finset.univ from Finset.subset_univ _)
  rw [Finset.sum_pair hij] at hpair
  have hsum := s.sum_factor_fixedCodim_le (A.subgroupOf H)
  dsimp only [U] at hsum
  rw [core_corank_subgroupOf H A hAH,
    ← normal_fixedCodim_ambient H (conjugateSpan H V) A hUH hAH]
  omega

/-- Applying the two-chief estimate to the literal conjugate of V and the
opposite-span displacement bound gives the required corank at most one. -/
theorem chosen_conjugate_corank_le_one
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (g : G) (hAH : V.map (MulAut.conj g).toMonoidHom ≤ H)
    (hU : conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 := by
  let := h.prepared.elementary
  have hlo := chosen_span_chief_displacement_lower T h hg hunique _
    (IsElementaryAbelian.map _) hAH
  have hup := chosen_span_displacement_le_three T h hg hr g hU
  omega
end CFSG.Quasithin.Chapter15.Section02
