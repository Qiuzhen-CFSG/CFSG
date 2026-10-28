module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource
public import CFSG.Quasithin.Chapter12.Section08.Setup.Consumers
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalSolvable
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.NaturalSection.Models
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.SectionCentralizer

/-!
# Applications of the conditional 12.2 structural assembly

In the marked A₆ configuration, the actual natural module has no fixed
vectors. Its original conjugation coordinates therefore give TI, and its
given normalization supplies normalizer control. This discharges the
Structural1222 input of the literal 13.3.14(b) consumer in this branch.
The conditional structural assembly also supplies the section-action kernel
used in 14.7.70. For the higher-rank local-kernel center product, the separate
full 12.2.13 input supplies escape. Full-catalogue A/C discharge uniqueness.
The section kernel also has a local version requiring only T-invariance of
the original V, so a multiple-overgroup source producer suffices there.

These are conditional consumer applications. The natural marking is the
original higher-rank hypothesis, not a seven-case classification theorem;
neither that classification nor 12.2.13 is proved here.
Source: Aschbacher--Smith, 12.2.2, 12.2.13, 12.8.10(5), 13.3.14(b),
14.5.15(4) and 14.7.70, with the original subgroup and quotient maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.SourceAssembly
universe u

/-- Full-catalogue A/C supply the actual universal uniqueness theorem. -/
theorem uniqueness127_knownSimple : Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
  intro X _ _ hX T L hL
  exact Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX T hL

/-- Transport the fixed-free A₆ action through the original coordinates,
using the literal quotient map from L. -/
theorem natural_fixed_space
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Chapter13.Section08.SourceCompletion.NaturalSetup T L V P E U M H) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  apply le_bot_iff.mp
  rintro v ⟨hv, hc⟩
  have hf : (d.coordinate ⟨v, hv⟩).toAdd ∈
      Representation.invariants (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) := by
    intro a
    obtain ⟨q, rfl⟩ := d.local_quotient.surjective a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ q
    rw [← d.conjugation l ⟨v, hv⟩]
    apply congrArg (fun w : V => (d.coordinate w).toAdd)
    apply Subtype.ext
    change (l : G) * v * (l : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc) l l.property)
  have hz : (d.coordinate ⟨v, hv⟩).toAdd = 0 :=
    Chapter13.Section08.TransvectionParabolic.Marking.NaturalSection.natural_fixed_eq_bot.le hf
  have hv1 : (⟨v, hv⟩ : V) = 1 := d.coordinate.injective (by
    simpa only [map_one] using (show d.coordinate ⟨v, hv⟩ = 1 from hz))
  exact congrArg Subtype.val hv1

/-- The original marked action discharges the structural input of the
13.3.14(b) consumer; no universal 12.2.2 premise is needed in this branch. -/
theorem natural_reduction_b
    {G : Type u} [Group G] [Finite G]
    {T : Sylow 2 G} {L V P E U M H : Subgroup G}
    (d : Chapter13.Section08.SourceCompletion.NaturalSetup T L V P E U M H)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hescape : ¬ H ≤ M) (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Chapter13.Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Chapter13.Section05.AmbientSource.planeAction E)) = 3) :
    let Y := Chapter13.Section03.Noncentrality.centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 := by
  let : Group.IsPerfect (L.subgroupOf (L ⊔ (T : Subgroup G))) :=
    d.counterexample.local_component.1.1.perfect
  let e : (L.subgroupOf (L ⊔ (T : Subgroup G))) ≃* L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hu := h.toHypothesis1221.sylow_normalized_maximal_unique d.normalizes_L
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hN : normalizer (V : Set G) ≤ normalizer (L : Set G) := by
    let := d.chosen.elementary
    exact normalizer_le_of_unique_maximalTwoLocal hu.2
      (IsElementaryAbelian.isPGroup 2 V) d.chosen.ne_bot d.normalizes_V
  apply Chapter13.Section03.Noncentrality.natural_residual_solvable_and_odd_rank d
    (d.chosen.ti_of_normalizer_or_fixedSpace h.toHypothesis1221
      (Or.inr (natural_fixed_space d))) hN ?_ hescape X hXL hx
  intro N hN hLN
  exact (hu.2 N hN hLN).trans d.local_normalizer.symm

open scoped commutatorElement in
private theorem section_action_kernel_iff
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W)
    (h : F.H) : h ∈ d.action.ker ↔ ∀ a ∈ F.U, ⁅(h : G), a⁆ ∈ F.Vi 1 := by
  have displacement (a : F.U) :
      (d.conjugationSection.coordinates (F.uAction h a * a⁻¹)).toAdd =
        d.action h (d.conjugationSection.coordinates a).toAdd -
          (d.conjugationSection.coordinates a).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
    rw [show (d.conjugationSection.coordinates (F.uAction h a)).toAdd =
      d.action h (d.conjugationSection.coordinates a).toAdd from
        d.conjugationSection.equivariant h a]
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh a ha
    let aU : F.U := ⟨a, ha⟩
    have hc : d.conjugationSection.coordinates (F.uAction h aU * aU⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      change (d.conjugationSection.coordinates (F.uAction h aU * aU⁻¹)).toAdd = 0
      rw [displacement, hh]
      simp
    exact (d.conjugationSection.coordinates_eq_one_iff _).mp hc
  · intro hh
    apply LinearMap.ext
    intro w
    change d.action h w = w
    obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
    have hc : d.conjugationSection.coordinates (F.uAction h a * a⁻¹) = 1 :=
      (d.conjugationSection.coordinates_eq_one_iff _).mpr (hh a a.property)
    have hz := congrArg Multiplicative.toAdd hc
    rw [displacement] at hz
    simpa only [ha, toAdd_ofAdd] using sub_eq_zero.mp hz

/-- The literal section kernel needs only invariance of this V. In particular,
the source producer may use the actual ambient multiple-overgroup hypothesis. -/
theorem sectionCentralizer_of_sylow_invariance
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W)
    (hnV : (T : Subgroup G) ≤ normalizer (V : Set G)) : d.SectionCentralizer := by
  let := d.natural.chosen.elementary
  have hnL := d.natural.chosen.sylow_normalizes_component
  have hu := d.natural.source.toHypothesis1221.sylow_normalized_maximal_unique hnL
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huniq : {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N} =
      {normalizer (L : Set G)} := by
    ext N
    constructor
    · rintro ⟨hN, hLN⟩
      exact Set.mem_singleton_iff.mpr (hu.2 N hN hLN)
    · intro hN
      obtain rfl := Set.mem_singleton_iff.mp hN
      exact ⟨hu.1, sup_le L.le_normalizer hnL⟩
  have hC : centralizer (V : Set G) ≤ normalizer (L : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans
      (normalizer_le_of_unique_maximalTwoLocal hu.2 (IsElementaryAbelian.isPGroup 2 V)
        d.natural.chosen.ne_bot (sup_le d.natural.chosen.normalizes hnV))
  have hH : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton _
  have hk : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H :=
    F.localKernel_eq_pCore d.counterexample.qtke L (normalizer (L : Set G)) F.H
      (by decide : 2 ≤ 3) d.natural.chosen.le_sylow d.natural.chosen.normalizes hnL
      d.natural.residual (fun _ => ⟨d.natural.naturalMarking⟩) rfl huniq hC
      d.natural.centralizer_L hH
  change d.action.ker = (F.H.pCoreIn 2).subgroupOf F.H
  calc
    d.action.ker = (F.localTildeAction F.H le_rfl).ker := by
      ext h
      exact (section_action_kernel_iff d h).trans
        (F.mem_localTildeAction_ker_iff F.H le_rfl h).symm
    _ = pCore 2 F.H := hk
    _ = (F.H.pCoreIn 2).subgroupOf F.H := by
      change pCore 2 F.H = ((pCore 2 F.H).map F.H.subtype).comap F.H.subtype
      rw [comap_map_eq_self_of_injective F.H.subtype_injective]

variable (normalization : SourceNormalization1222 KnownSimple.IsKnownSimple.{u})
  (branches : SourceBranches1222 KnownSimple.IsKnownSimple.{u})
include normalization branches

/-- The original section-action kernel used in 14.7.70, with no additional
uniqueness premise. -/
theorem sectionCentralizer
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {F : Section08.InvariantFlag T V 3} {W : Type u}
    [AddCommGroup W] [Module (ZMod 2) W]
    (d : Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data T L V F W) :
    d.SectionCentralizer :=
  d.sectionCentralizer_of_earlier_setup
    (structural1222_of_source_branches normalization branches) uniqueness127_knownSimple

/-- The actual natural-branch local-kernel application also uses the separate
full 12.2.13 theorem. Its nonabelian and conjugate-containment antecedents are retained. -/
theorem localKernel_center_product
    (recognition : Theorem12213 KnownSimple.IsKnownSimple.{u})
    {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
    (h : Section08.HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (F : Section08.InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Section08.conjugate F.ZU g ≤ F.U →
      (F.ZU = Section08.centerIn (F.I₂ L) ⊔ F.Vi 1 ∧
        Disjoint (Section08.centerIn (F.I₂ L)) (F.Vi 1) ∧
        ∃ e : Section08.centerIn (F.I₂ L) × F.Vi 1 ≃* F.ZU,
          ∀ a b, (e (a, b) : G) = (a : G) * (b : G)) ∧
      ⁅L, Section08.centerIn (F.I₂ L)⁆ = ⊥ :=
  h.localKernel_center_product
    ⟨structural1222_of_source_branches normalization branches,
      uniqueness127_knownSimple, recognition⟩ F hne g hgP hgH

end CFSG.Quasithin.Chapter12.Section02.SourceAssembly
