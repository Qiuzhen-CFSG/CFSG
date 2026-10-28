module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent.Projections
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent.Recognition
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.SecondComponent.ResidualPlacement
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.RestrictionComparison

/-!
# The second-component construction in B.5.9

A proper natural seed gives a nontrivial centralizer projection and hence a
distinct component M moved by A. The universal preliminary conclusion recognizes
its genuine natural seed: properness gives |A|>2, and A is not contained in M,
excluding the other alternatives. Full Theorem A bounds the three-rank of E(G)
through the literal SQTK cover; the two centerless natural components exhaust
E(G). Residual functoriality and generalized-Fitting self-centralization then
give the embedded prime-to-three residual identity and A ≤ LM.

The two-core of LA lies in the centralizer projection A_C: use the direct
product L A_C and the trivial two-core of the natural, centerless component.
Perfectness gives [[V,L],L]=[V,L]. Thus if A_C fixed [V,L], the literal seed
[C_V(O₂(LA)),L] would equal [V,L]. A proper seed therefore forces a nontrivial
cross action. When A ≤ LM for two distinct components, projection places
A_C inside M and gives [[V,L],M] ≠ 0.

`secondComponent_of_proper_seed` assembles all these constructions into the
literal `SecondComponent` record. Its only earlier-source parameter beyond
`Setup` is universal full Theorem A, with every source clause retained in
`ChapterA.Section02.TheoremA`. The universal preliminary conclusion is the
permitted intermediate input in `Setup`; neither a second seed nor placement
nor a counterexample hypothesis remains an additional premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, beginning of the final paragraph. The perfect-commutator proof
reuses the quotient argument in BinaryOffender/SingleNoncentralFlag.lean.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
universe u v
variable {G : Type u} {V : Type v}
  [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem localTwoCore_le_centralProjection {A L : Subgroup G}
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L) (d : InnerProjections A L) :
    localTwoCore L A ≤ d.centralProjection := by
  let : IsQuasisimple L := hL.2
  have hz := seed_center_eq_bot ρ seed
  have hLcore : pCore 2 L = ⊥ :=
    le_bot_iff.mp ((IsQuasisimple.pCore_le_center 2).trans hz.le)
  let C := d.centralProjection
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting L C
    (d.disjoint hz) (le_centralizer_iff.mp d.centralProjection_le)
  have hcore : pCore 2 ↥(L ⊔ C) =
      ((⊥ : Subgroup L).prod (pCore 2 C)).map e.toMonoidHom := by
    rw [← pCore_map_iso 2 e, pCore_prod, hLcore]
  unfold localTwoCore
  rw [d.join_eq, hcore]
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  have hz1 : z.1 = 1 := hz.1
  change (e (z.1, z.2) : G) ∈ C
  rw [he, hz1, OneMemClass.coe_one, one_mul]
  exact z.2.property

omit [Finite G] in
/-- Perfectness gives [[V,L],L]=[V,L]. This is the quotient argument from
`BinaryOffender/SingleNoncentralFlag.lean`, specialized to the actual moved space. -/
private theorem moved_perfect (L : Subgroup G) [L.Normal] [Group.IsPerfect L] :
    subspaceCommutator ρ (moved ρ L) L = moved ρ L := by
  let J := (MovedSection.ofNormal ρ L).space
  let D := subspaceCommutator ρ J.toSubmodule L
  have hJ : J.toSubmodule = moved ρ L := rfl
  have hJstab : L ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact J.apply_mem_toSubmodule k hv
  have hDstab : L ≤ subspaceStabilizer ρ D :=
    subspaceCommutator_invariant_normalizer ρ hJstab L.le_normalizer
  have hDle : D ≤ J.toSubmodule := subspaceCommutator_le_of_invariant ρ hJstab
  let Drep : Subrepresentation (ρ.comp L.subtype) :=
    ⟨D, by intro k v hv; exact (hDstab k.property v).2 hv⟩
  let qρ := Drep.quotientRepresentation
  have hqC : subspaceCommutator qρ ⊤ (⊤ : Subgroup L) ≤ fixedSpace qρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, v, _, rfl⟩
    intro k
    induction v using Submodule.Quotient.induction_on with
    | _ w =>
      change qρ k (qρ x (Drep.toSubmodule.mkQ w) - Drep.toSubmodule.mkQ w) =
        qρ x (Drep.toSubmodule.mkQ w) - Drep.toSubmodule.mkQ w
      rw [map_sub, Subrepresentation.quotientRepresentation_mk,
        Subrepresentation.quotientRepresentation_mk]
      apply (Submodule.Quotient.eq D).mpr
      have hdJ : ρ x.val w - w ∈ J.toSubmodule :=
        Submodule.subset_span ⟨x.val, x.property, w, Submodule.mem_top, rfl⟩
      exact Submodule.subset_span
        ⟨k.val, k.val.property, ρ x.val w - w, hdJ, by
          simp only [map_sub, ← Module.End.mul_apply]
          rfl⟩
  have hqfix : (⊤ : Submodule (ZMod 2) (V ⧸ D)) ≤ fixedSpace qρ (⊤ : Subgroup L) :=
    le_fixedSpace_of_commutator_le_fixedSpace qρ (⊤ : Subgroup L) ⊤
      (le_subspaceStabilizer qρ ⊤ (by simp)) hqC
  have hJleD : J.toSubmodule ≤ D := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    have hfix := hqfix (show Drep.toSubmodule.mkQ v ∈
      (⊤ : Submodule (ZMod 2) (V ⧸ D)) from by trivial)
    have hfixx := hfix ⟨⟨x, hx⟩, by simp⟩
    change Drep.toSubmodule.mkQ (ρ x v) = Drep.toSubmodule.mkQ v at hfixx
    apply (Submodule.Quotient.mk_eq_zero D).mp
    change Drep.toSubmodule.mkQ (ρ x v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hfixx
  exact le_antisymm hDle hJleD

/-- Properness forces the centralizer projection to move W. -/
theorem centralProjection_cross_action {A L : Subgroup G} [L.Normal]
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L)
    (hproper : seed.space.toSubmodule < moved ρ L) (d : InnerProjections A L) :
    subspaceCommutator ρ (moved ρ L) d.centralProjection ≠ ⊥ := by
  intro hz
  let : IsQuasisimple L := hL.2
  have hw : moved ρ L ≤ fixedSpace ρ (localTwoCore L A) :=
    ((subspaceCommutator_eq_bot_iff ρ (moved ρ L) d.centralProjection).mp hz).trans
      (fixedSpace_antitone ρ (localTwoCore_le_centralProjection ρ seed hL d))
  have hle : moved ρ L ≤ seed.space.toSubmodule := by
    rw [seed.space_eq]
    exact (moved_perfect ρ L).ge.trans (subspaceCommutator_mono_left ρ hw L)
  exact (not_le_of_gt hproper) hle

/-- The source cross action follows from genuine containment A ≤ LM;
no numerical or cross-action estimate is assumed. -/
theorem cross_action_of_offender_le_join {A L M : Subgroup G} [L.Normal]
    (seed : NaturalSeed ρ A L) (hL : IsComponent G L) (hM : IsComponent G M)
    (hne : L ≠ M) (hproper : seed.space.toSubmodule < moved ρ L)
    (hA : A ≤ L ⊔ M) : subspaceCommutator ρ (moved ρ L) M ≠ ⊥ := by
  let d := innerProjections ρ seed
  have hMC : M ≤ centralizer (L : Set G) := le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hM hne))
  have hdM := d.centralProjection_le_second (seed_center_eq_bot ρ seed) hMC hA
  intro hz
  apply centralProjection_cross_action ρ seed hL hproper d
  apply (subspaceCommutator_eq_bot_iff ρ (moved ρ L) d.centralProjection).mpr
  exact ((subspaceCommutator_eq_bot_iff ρ (moved ρ L) M).mp hz).trans
    (fixedSpace_antitone ρ hdM)

/-- Assemble the published record after the two remaining construction steps.
The cross-action field is proved here from properness and offender placement. -/
theorem secondComponent_of_seed_and_placement {K : GroupClass} {A L M : Subgroup G}
    (setup : Setup ρ K A) (hL : IsComponent G L) (hM : IsComponent G M)
    (hne : L ≠ M) (hMA : ⁅M, A⁆ = M)
    (seed : NaturalSeed ρ A L) (hproper : seed.space.toSubmodule < moved ρ L)
    (secondSeed : NaturalSeed ρ A M) (hA : A ≤ L ⊔ M)
    (hres : L ⊔ M =
      (primeToResidual 3 ↥(componentLayer G)).map (componentLayer G).subtype) :
    Nonempty (SecondComponent ρ A L) := by
  let : L.Normal := setup.component_normal L hL
  exact ⟨{
    second := M
    isComponent := hM
    distinct := hne
    commutator_eq := hMA
    seed := secondSeed
    offender_le := hA
    residual_eq := hres
    cross_action := cross_action_of_offender_le_join ρ seed hL hM hne hproper hA }⟩

/-- A proper natural seed produces the complete second-component configuration
of B.5.9. Full Theorem A is the sole additional earlier-source input. -/
theorem secondComponent_of_proper_seed {K : GroupClass.{u}} {A L : Subgroup G}
    (setup : Setup ρ K A)
    (theoremA : ∀ (D : Type u) [Group D] [Finite D], ChapterA.Section02.TheoremA K D)
    (hL : IsComponent G L) (hLA : ⁅L, A⁆ = L)
    (seed : NaturalSeed ρ A L) (hproper : seed.space.toSubmodule < moved ρ L) :
    Nonempty (SecondComponent ρ A L) := by
  obtain ⟨M, hM, hne, hMA, hAM⟩ :=
    exists_distinct_moved_component ρ setup hL hLA seed hproper
  obtain ⟨secondSeed⟩ :=
    second_component_naturalSeed ρ setup hLA seed hproper hM hMA hAM
  obtain ⟨hA, hres⟩ := ResidualPlacement.residual_and_offender_placement
    ρ setup theoremA hL hM hne seed secondSeed
  exact secondComponent_of_seed_and_placement
    ρ setup hL hM hne hMA seed hproper secondSeed hA hres

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
