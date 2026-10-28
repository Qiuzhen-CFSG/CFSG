module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Selection
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.PreDescentSource
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceCompletion

/-!
# Source assembly of the singular-line normalizers

The earlier natural orthogonal action and local conclusions prove all seven
clauses of 15.3.66. The original offender geometry, its same-I classification
and Frattini descent then give every clause of 15.3.67 on the original G_E.
The full KnownSimple adequate B.5 implication is an explicit earlier-source
input, alongside simple QTKE and the actual Z_S normalizer restriction.

The rank-two entry point first constructs an escaping singular four-group,
including its actual Klein-four equivalence, and performs the M-conjugacy
adjustment before applying these results. Its input record contains only facts
that precede that choice. Neither source conclusion nor a temporary-core
identification is an input.

This assembly imports the checked action comparison through PreDescentSource.
Its public reexport belongs above OriginalSource at the Section03 boundary.
The parent retains the earlier local/fusion results, the rank-two bound and
the universal classification discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1152–1154, PDF pp.1169–1171.
-/

@[expose] public section

open Subgroup Stellmacher OrthogonalFourBinary
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource

open LocalStructure GoldschmidtCore.LocalRelations
open TerminalSourceEndgame

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

/-- The seven source clauses of 15.3.66, with the actual orthogonal action
and the published subgroup constructions. -/
def LineGeometry (d : NaturalAction (localModule T M) M) (Mc P E : Subgroup G) : Prop :=
    actionImage d (lineT T E) =
        actionImage d (T : Subgroup G) ⊓ (OrthogonalFourBinary.omega :
          Subgroup OrthogonalFourBinary.IndexTwoNormalizer.IsometryGroup) ∧
      (lineT T E).relIndex (T : Subgroup G) = 2 ∧
      (IsKleinFour (actionImage d (lineT T E)) ∧
        actionImage d (lineT T E) ≠ actionImage d (planeStabilizer T P)) ∧
      centralInvolutions T ≤ E ∧
      (Nonempty (((lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G) ⧸
          pCore 2 (lineY (residualY M Mc) E ⊔ lineT T E : Subgroup G)) ≃*
            Equiv.Perm (Fin 3)) ∧
        localModule T M = ⁅localModule T M, lineY (residualY M Mc) E⁆ ∧
        lineQ E ≤ centralizer (E : Set G) ∧
        Stellmacher.twoCoreAmbient (lineY (residualY M Mc) E ⊔ lineT T E) =
          (lineY (residualY M Mc) E ⊔ lineT T E) ⊓ centralizer (E : Set G)) ∧
      (lineNormalizer E : Set G) =
        (lineY (residualY M Mc) E : Set G) * (lineT T E : Set G) *
          (centralizer (E : Set G) : Set G) ∧
      centralizer (E : Set G) ≤ Mc

/-- All four clauses of 15.3.67. Normalities are in the original G_E;
quotients carry actual group equivalences and products are setwise. -/
def LineStructure (T : Sylow 2 G) (M Mc E : Subgroup G) : Prop :=
    (∃ S : Sylow 2 (lineNormalizer E),
      (S : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) ∧
    lineB T E ≤ (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (lineB T E).characteristicNormalizerClosure ≤ M ∧
    centralizer (localModule T M : Set G) =
      (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (M : Set G) = (residualY M Mc : Set G) * (T : Set G) ∧
    (lineNormalizer E : Set G) =
      (lineY (residualY M Mc) E : Set G) * (lineX E : Set G) * (lineT T E : Set G) ∧
    ((lineY (residualY M Mc) E).subgroupOf (lineNormalizer E)).Normal ∧
    ((lineX E).subgroupOf (lineNormalizer E)).Normal ∧
    Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((lineY (residualY M Mc) E ⧸ pCore 2 (lineY (residualY M Mc) E)) ≃*
      Multiplicative (ZMod 3)) ∧
    ¬ lineX E ≤ M ∧
    Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    lineX E = ⁅lineX E,
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G))⁆

/-- Source 15.3.66 from the earlier local data and the Sylow-adjusted line. -/
theorem lemma_15_3_66 (s : EarlierData T M Mc P E) :
    LineGeometry s.natural Mc P E := by
  exact Orthogonal.source_lemma_15_3_66 s.natural Mc T P E s.ordering.1.2
    s.plane_le s.plane_card s.plane_definite s.line_le s.line_card s.line_singular
    s.central_fixed s.residual_image s.residual_core_module s.other_centralizer
    s.selected s.selected_map

/-- Source 15.3.67 after removing the temporary normalizer assumption.
The universal B.5 input uses the full known-simple catalogue. -/
theorem lemma_15_3_67 (s : EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple.{u} G)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      KnownSimple.IsKnownSimple.{u}) :
    LineStructure T M Mc E :=
  PreDescentSource.source_lemma_15_3_67 s hG hZ classify

/-- The final S₃ × S₃ identification preserves the original marked first
projection, the centralizer factor and both residual factors. Its kernel is
the original Q_E, with no identification with the temporary two-core. -/
theorem quotient_compatibility (s : EarlierData T M Mc P E)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple.{u} G)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      KnownSimple.IsKnownSimple.{u}) :
    let := OriginalSource.standard_elementary s.natural
    let a := PreDescentSource.descentInputs s hG hZ classify
    let q := Descent.QuotientIdentification.originalProductMap a.quotientInputs
    let e := Descent.QuotientIdentification.originalProductEquiv a.quotientInputs
    q.ker.map (lineNormalizer E).subtype = lineQ E ∧
    (∀ z, (e z).1 = (a.marked.equiv z).1) ∧
    ((lineY (residualY M Mc) E ⊔ zpowers a.marked.tau).subgroupOf (lineNormalizer E)).map q =
      (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ ∧
    ((centralizer (E : Set G)).subgroupOf (lineNormalizer E)).map q =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ ∧
    ((lineX E).subgroupOf (lineNormalizer E)).map q =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) ∧
    ((lineY (residualY M Mc) E).subgroupOf (lineNormalizer E)).map q =
      (alternatingGroup (Fin 3)).prod (⊥ : Subgroup (Equiv.Perm (Fin 3))) ∧
    (lineX E).pCoreIn 2 = lineX E ⊓ lineQ E ∧
    (lineY (residualY M Mc) E).pCoreIn 2 = lineY (residualY M Mc) E ⊓ lineQ E ∧
    lineY (residualY M Mc) E ⊓ lineX E = (lineY (residualY M Mc) E).pCoreIn 2 ⊓ (lineX E).pCoreIn 2 := by
  let := OriginalSource.standard_elementary s.natural
  exact Descent.quotient_compatibility (PreDescentSource.descentInputs s hG hZ classify)

/-- The genuine earlier local conclusions before choosing E. In particular
this record contains no line, Sylow-adjustment or normalizer-recognition field. -/
structure BeforeLine (T : Sylow 2 G) (M Mc P : Subgroup G) where
  natural : NaturalAction (localModule T M) M
  ordering : ChapterA.Section05To06.IsOrderingMaximal T M
  module_le : localModule T M ≤ (T : Subgroup G)
  plane_le : P ≤ localModule T M
  plane_card : Nat.card P = 4
  plane_definite : ∀ v : P, v ≠ 1 →
    ¬ natural.singular ⟨v, plane_le v.property⟩
  central_fixed : centralInvolutions T =
    localModule T M ⊓ centralizer (T : Set G)
  central_card : Nat.card (centralInvolutions T) = 2
  other_centralizer : Mc = centralizer (centralInvolutions T : Set G)
  residual_image : actionImage natural (residualY M Mc) =
    pResidual 2 TerminalLines.IsometryGroup
  residual_core_module : twoCoreAmbient (residualY M Mc) =
    residualY M Mc ⊓ centralizer (localModule T M : Set G)
  residual_core_center : (residualY M Mc).pCoreIn 2 =
    residualY M Mc ⊓ centralizer (centralInvolutions T : Set G)
  core_movement : ⁅fixedPlane (localModule T M) (planeStabilizer T P), Mc.pCoreIn 2⁆ =
    centralInvolutions T
  local_span_abelian : IsMulCommutative (conjugateSpanBy (localModule T M) Mc)
  /-- The singular-intersection conclusion of 15.3.46(2). -/
  singular_intersection : ∀ g : G, g ∉ M →
    ∀ x : ↥(localModule T M ⊓ (localModule T M).map (MulAut.conj g).toMonoidHom),
      natural.singular ⟨x, x.property.1⟩

/-- Construct the selected source line, retaining the literal earlier action.
The only rank hypothesis is the parent's explicit r(G,V)=2. -/
theorem exists_earlierData_of_rank_two (d : BeforeLine T M Mc P)
    (hr : ChapterE.globalR (localModule T M) = 2) :
    ∃ (E : Subgroup G) (s : EarlierData T M Mc P E),
      s.natural = d.natural ∧ Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) := by
  let := OriginalSource.standard_elementary d.natural
  have hcard : Nat.card (localModule T M) = 16 := by
    rw [Nat.card_congr d.natural.coordinates.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hV : localModule T M ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcard
    omega
  have hM : M = normalizer (localModule T M : Set G) :=
    d.ordering.1.1.eq_of_le
      ⟨localModule T M, hV, IsElementaryAbelian.isPGroup 2 _, rfl⟩ d.natural.normalizes
  obtain ⟨E, hEV, hEcard, hfour, hescape, hsingular, S, hS⟩ :=
    exists_singular_escaping_four_with_sylow_lineT T (localModule T M) M d.natural
      d.ordering.1.2 hcard hM hr d.singular_intersection
  let s : EarlierData T M Mc P E := {
    natural := d.natural
    ordering := d.ordering
    module_le := d.module_le
    plane_le := d.plane_le
    plane_card := d.plane_card
    plane_definite := d.plane_definite
    central_fixed := d.central_fixed
    central_card := d.central_card
    other_centralizer := d.other_centralizer
    residual_image := d.residual_image
    residual_core_module := d.residual_core_module
    residual_core_center := d.residual_core_center
    core_movement := d.core_movement
    local_span_abelian := d.local_span_abelian
    line_le := hEV
    line_card := hEcard
    line_singular := hsingular
    selected := S
    selected_map := hS
    escape := hescape }
  exact ⟨E, s, rfl, hfour⟩

/-- Select and conjugate the escaping line from r(G,V)=2, then prove every
clause of 15.3.66–67 for that same line and the original natural action.
The returned earlier data also supplies the literal original-group descent
and offender interfaces to the subsequent Goldschmidt assembly. -/
theorem exists_line_normalizers_of_rank_two (d : BeforeLine T M Mc P)
    (hr : ChapterE.globalR (localModule T M) = 2)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple.{u} G)
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
    (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u}
      KnownSimple.IsKnownSimple.{u}) :
    ∃ (E : Subgroup G) (s : EarlierData T M Mc P E),
      s.natural = d.natural ∧ Nonempty (E ≃* Multiplicative (ZMod 2 × ZMod 2)) ∧
      LineGeometry d.natural Mc P E ∧ LineStructure T M Mc E := by
  obtain ⟨E, s, heq, hfour⟩ := exists_earlierData_of_rank_two d hr
  refine ⟨E, s, heq, hfour, ?_, lemma_15_3_67 s hG hZ classify⟩
  rw [← heq]
  exact lemma_15_3_66 s

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizerSource
