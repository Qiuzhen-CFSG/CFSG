module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.Fusion
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.LocalAction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.TorusConstruction
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.UnitaryPlacement
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure
public import CFSG.Quasithin.Chapter16.Section04To05.IntersectionStructure.Local
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.NormalFour.Preparation
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# Construction of the Bender geometry

The genuine center = O₂(L) theorem transports the source quotient into
`RankOneAt`. The actual rank-one tori, normalizer and fusion arguments then
construct every field of `Geometry`. In the unitary alternative the intrinsic
involution centralizer calculation and 16.4.8 place T_L in L^g, so the original
source conjugator preserves T_L. In the linear and Suzuki alternatives, weak
closure and Burnside fusion construct the moving conjugator.

`geometry_of_rankOneAt` discharges all three premises of the preserved
conditional helper `geometry_of_local_action`. The exceptional Suzuki cover
is excluded by the ambient covered-case argument using genuine earlier cover
data; centerlessness and disjointness of the two omega factors are not inputs.
The Delta-zero definition supplies the omega containment for the chosen R,
and the proved 16.4.2(1) supplies its faithfulness and centralizer isomorphism.

`exists_geometry_of_source_quotient` constructs the parameter and geometry
from Hypothesis 16.1.1 with the full known-simple catalogue. The earlier cover
data and the specified 16.4.2(4), 16.4.6, 16.4.8 and 16.4.10 outputs remain
explicit. No actor, local-action record, weak closure or moving-conjugator
conclusion is assumed. The GLS application and final J₁ identification remain
with the Proposition 16.5.1 assembly owner.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed pp.1194–1195, with 16.1.2 and 16.4.2, 16.4.10–11.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The Bender alternatives have a genuine rank-one parameter, including the odd Suzuki degree. -/
theorem exists_rankOneAt_of_bender (L : Subgroup G)
    (hb : ClassificationModels.IsBenderModel (L ⧸ center L)) :
    ∃ n : ℕ, 2 ≤ n ∧ RankOneAt (L ⧸ center L) n := by
  cases hb with
  | linear n hn he => exact ⟨n, hn, Or.inl he⟩
  | unitary n hn he => exact ⟨n, hn, Or.inr (Or.inl he)⟩
  | suzuki m hm he => exact ⟨2 * m + 1, by omega, Or.inr (Or.inr ⟨m, hm, rfl, he⟩)⟩

/-- Use the proved center equality, rather than silently replacing the source quotient. -/
theorem exists_rankOneAt_of_source_quotient {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (hEven : HasEvenTypeCentralizers G) (h : CentralComponentSetup T z L)
    (hb : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L)) :
    ∃ n : ℕ, 2 ≤ n ∧ RankOneAt (L ⧸ center L) n := by
  have he := hEven.component_center_eq_twoCore h.involution h.component
  exact exists_rankOneAt_of_bender L
    (hb.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq he))

/-- Conditional assembly. The local action, weak closure, and unitary placement
are the outstanding model obligations, and must be discharged by the source owner. -/
theorem geometry_of_local_action {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}
    (h : IntersectionSetup T z L g R)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n)
    (d : LocalAction T L R n)
    (hweak : ¬ ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      ∀ a : G, (benderSpace T L).conjBy a ≤ (T : Subgroup G) →
        (benderSpace T L).conjBy a = benderSpace T L)
    (hplace : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      componentSylow T L ≤ L.conjBy g) :
    Nonempty (Geometry T L R n) := by
  let := d.commuting_elementary
  let := d.component_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  have hmover : ∃ a : G, a ∈ normalizer (benderSpace T L : Set G) ∧
      (omegaOneAmbient (commutingSylow T L)).conjBy a = omegaOneAmbient R ∧
      (ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
        a ∈ normalizer (componentSylow T L : Set G)) := by
    by_cases hu : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n)
    · obtain ⟨hTL, hV, hUC⟩ := unitary_transport h hR htransport (hplace hu) d.omega_le
      exact ⟨g, hV, hUC, fun _ => hTL⟩
    · obtain ⟨a, ha, hUC⟩ := fusion_mover (hweak hu)
        (h.eq_conjugate_commutingSylow hR htransport) d.omega_le
      exact ⟨a, ha, hUC, fun hh => (hu hh).elim⟩
  obtain ⟨a, ha, hUC, hu⟩ := hmover
  obtain ⟨hT, hTC⟩ := sylow_normalizes_factors h.toStandardSetup
  exact ⟨{
    degree := hn
    model := hmodel
    actor := d.actor
    actor_le := d.actor_le
    actor_normalizes := actor_normalizes_space d.actor_le
    actor_cyclic := d.actor_cyclic
    actor_card := d.actor_card
    elementary := inferInstance
    fixed_eq := d.fixed_eq
    disjoint := d.disjoint
    span := d.span
    moved_card := d.moved_card
    regular := d.regular
    fixed_intersection := fixed_intersection_of_fixed_eq (d.actor_le.trans inf_le_left) d.fixed_eq
    actor_normal_in_stabilizer := actor_normal_in_stabilizer_of_image h.toStandardSetup d.image_eq
    sylow_normalizes := hT
    sylow_fixes := hTC
    mover := a
    mover_normalizes := ha
    mover_eq := hUC
    unitary_mover := hu }⟩

/-- Construct the full geometry at a specified rank-one parameter. The only
additional inputs are the genuine earlier cover data, Sylow and transport
conclusions, universal 16.4.6 exclusion, and unitary 16.4.8 alternatives.
In particular, the actor, weak closure and unitary placement are proved here. -/
theorem geometry_of_rankOneAt {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}
    (h : IntersectionSetup T z L g R)
    (hdelta : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hcover : center L ≠ ⊥ →
      CoverAndSylowElimination.SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (hn : 2 ≤ n) (hmodel : RankOneAt (L ⧸ center L) n)
    (h1646 : WeakClosure.SmallLinear.FiveOuterPGLExclusion T z L)
    (h1648 : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      ∀ u ∈ R, orderOf u = 2 →
        involutionTwoResidual L u ≤ L.conjBy g ∨
          (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
            (involutionTwoResidual L u).subtype ≤ L.conjBy g)) :
    Nonempty (Geometry T L R n) := by
  obtain ⟨_, ⟨eR⟩, _, hdisj⟩ := h.normalizer_structure
  have hfaith : Disjoint R (centralizer (L : Set G)) := disjoint_iff.mpr hdisj
  have homega := h.omega_le_of_mem_deltaZero hdelta
  obtain ⟨d⟩ := TorusConstruction.exists_localAction
    h hcover hR eR htransport homega hfaith hn hmodel
  apply geometry_of_local_action h hR htransport hn hmodel d
  · exact WeakClosure.space_weakly_closed h hcover hR eR htransport hfaith
      hn hmodel d (fun _ => h1646)
  · intro hu
    have hZ := TorusConstruction.CoveredCase.center_eq_bot
      h hcover hR eR htransport homega hfaith
    exact UnitaryPlacement.componentSylow_le_conjugate
      h hR htransport hfaith hn hu hZ d (h1648 hu)

/-- The geometry construction under the source hypotheses of 16.5.1.
The quotient by O₂(L) is transported through the proved equality with Z(L).
The unitary residual alternatives retain their dependence on the fixed-field
exponent, and 16.4.6 retains its scope over all applicable conjugates.
The explicit earlier-source premises must be discharged by the proposition's
assembly owner; no geometry or principal construction conclusion is a premise. -/
theorem exists_geometry_of_source_quotient
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (hG : Hypothesis1611 KnownSimple.IsKnownSimple G)
    (h : IntersectionSetup T z L g R)
    (hdelta : (centralizer (L : Set G)).conjBy g ∈ deltaZero L)
    (hb : ClassificationModels.IsBenderModel (L ⧸ pCore 2 L))
    (hcover : center L ≠ ⊥ →
      CoverAndSylowElimination.SuzukiCoverInput T L ∧ Nat.card (center L) ≤ 4)
    (hR : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (h1646 : WeakClosure.SmallLinear.FiveOuterPGLExclusion T z L)
    (h1648 : ∀ n : ℕ, 2 ≤ n →
      ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ n) →
      ∀ u ∈ R, orderOf u = 2 →
        involutionTwoResidual L u ≤ L.conjBy g ∨
          (n ≠ 3 ∧ (pResidual 3 (involutionTwoResidual L u)).map
            (involutionTwoResidual L u).subtype ≤ L.conjBy g)) :
    ∃ n : ℕ, Nonempty (Geometry T L R n) := by
  obtain ⟨n, hn, hmodel⟩ := exists_rankOneAt_of_source_quotient
    hG.evenType h.toStandardSetup.toCentralComponentSetup hb
  exact ⟨n, geometry_of_rankOneAt h hdelta hcover hR htransport hn hmodel
    h1646 (h1648 n hn)⟩

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction
