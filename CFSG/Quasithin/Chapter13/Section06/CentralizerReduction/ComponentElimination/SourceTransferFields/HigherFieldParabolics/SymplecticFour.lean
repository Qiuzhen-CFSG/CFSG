module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.ActionKernels
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.HigherFieldResiduals
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic

/-!
# The marked `Sp₄(2^m)` parabolic branch

The source model is an actual equivalence with the symplectic matrix group.
The two maximal parabolics are pulled back along that equivalence and their
solvable residuals are kept as subgroups of the original group.  The marked
action is allowed to be any diagram-preserving automorphism: its action on the
source component is related to ambient conjugation explicitly, while the
diagram-preservation clauses are used separately for the point and plane
classes.  Thus `Tᵥ`-invariance is not inferred from an abstract group
isomorphism and diagram automorphisms are not silently assumed inner.

The B.5 generation and C.1.26 inputs are exposed as source conclusions.  The
leaf supplies the concrete parabolic pullbacks, the literal residual and
quotient data, movement through the parent `moving_residual_of_plus_generation`
lemma, and the transport of a marked nonzero triple commutator without any
splitting assumption.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, 13.6.14,
13.6.16 and 13.6.19, printed pp.929--931; F.1.12(I)(2), pp.262--264.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.LinearTwo.PushingUp

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
namespace SymplecticFour

universe u
variable {G : Type u} [Group G]
variable {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
variable [Field F] [Finite F] [CharP F 2]

/-- A marked action on the actual source component.  The `conjugation` field
is the source B.5 conclusion: it identifies the marked action with literal
ambient conjugation.  The separate `diagram_preserved` field records the
point and plane classes for possible outer or field automorphisms. -/
structure MarkedSp4Model
    (T : Subgroup G) (v : G) (K : Subgroup G) (F : Type)
    [Field F] [Finite F] [CharP F 2] where
  model : K ≃* Sp F
  action : Tv T v →* MulAut K
  modelAction : Tv T v →* MulAut (Sp F)
  action_compatibility : ∀ t : Tv T v, ∀ k : K,
    model (action t k) = modelAction t (model k)
  conjugation : ∀ t : Tv T v, ∀ k : K,
    ((action t k : K) : G) = (t : G) * (k : G) * (t : G)⁻¹
  diagram_preserved : ∀ t : Tv T v,
    DiagramAutomorphisms.PreservesDiagram (modelAction t)

/-- Pull a literal matrix subgroup back through the marked model and then
embed it in the original ambient group. -/
def pullback {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (e : K ≃* Sp F) (P : Subgroup (Sp F)) : Subgroup G :=
  (P.comap e.toMonoidHom).map K.subtype

abbrev pointParabolicPullback (d : MarkedSp4Model T v K F) : Subgroup G :=
  pullback d.model pointParabolic

abbrev planeParabolicPullback (d : MarkedSp4Model T v K F) : Subgroup G :=
  pullback d.model planeParabolic

theorem pullback_le_component (d : MarkedSp4Model T v K F)
    (P : Subgroup (Sp F)) : pullback d.model P ≤ K := by
  exact map_subtype_le _

theorem pointParabolicPullback_le (d : MarkedSp4Model T v K F) :
    pointParabolicPullback d ≤ K :=
  pullback_le_component d pointParabolic

theorem planeParabolicPullback_le (d : MarkedSp4Model T v K F) :
    planeParabolicPullback d ≤ K :=
  pullback_le_component d planeParabolic

/-- The marked action proves the literal `Tᵥ`-invariance of `K`. -/
theorem tv_invariant_of_marked_action
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) :
    Tv T v ≤ normalizer (K : Set G) := by
  intro t ht
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    let t' : Tv T v := ⟨t, ht⟩
    let k : K := ⟨x, hx⟩
    simpa [d.conjugation t' k] using (d.action t' k).property
  · intro hx
    let ti : Tv T v := ⟨t⁻¹, inv_mem ht⟩
    let k : K := ⟨t * x * t⁻¹, hx⟩
    have hi := d.conjugation ti k
    have hk : ((d.action ti k : K) : G) ∈ K := (d.action ti k).property
    rw [hi] at hk
    simpa [ti, k, mul_assoc] using hk

/-- The marked action retains the two actual parabolic classes.  This helper
is intentionally phrased with `PreservesParabolicClass`, so a diagram
automorphism may be outer while still preserving each class. -/
theorem marked_point_parabolic_class
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) (t : Tv T v) :
    DiagramAutomorphisms.PreservesParabolicClass (d.modelAction t)
      pointParabolic :=
  (d.diagram_preserved t).1

theorem marked_plane_parabolic_class
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) (t : Tv T v) :
    DiagramAutomorphisms.PreservesParabolicClass (d.modelAction t)
      planeParabolic :=
  (d.diagram_preserved t).2

/-- The literal plus actor acts on the literal `W_K`; this is the action
interface used by the source generation clause. -/
theorem marked_plusActor_normalizes_WK
    {T : Subgroup G} {v : G} {K : Subgroup G} {L : Subgroup G} {z : G}
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    plusActor K L T v ≤ normalizer (WK K L T z v : Set G) :=
  plusActor_normalizes_WK K L T z v hL hz

/-- Source conclusions attached to the two marked maximal parabolics.  The
membership and C.1.26 hypotheses remain literal `Chapter1.LIn` and SQTK
statements for the actual residuals; no abstract matrix parabolic is used as
a substitute for its source preimage. -/
structure MarkedParabolicData
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) (L : Subgroup G) (z : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) where
  point_local : residualIn (pointParabolicPullback d) ∈
    Chapter1.LIn (Gv v) (Tv T v)
  plane_local : residualIn (planeParabolicPullback d) ∈
    Chapter1.LIn (Gv v) (Tv T v)
  point_normalized : Tv T v ≤
    normalizer (residualIn (pointParabolicPullback d) : Set G)
  plane_normalized : Tv T v ≤
    normalizer (residualIn (planeParabolicPullback d) : Set G)
  residual_generation :
    plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz (residualIn (pointParabolicPullback d)) ⊔
        plusImage K L T z v hL hz (residualIn (planeParabolicPullback d))

/-- The B.5 generation clause selects a residual that moves the marked point. -/
theorem moving_residual_of_marked_parabolics
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) (L : Subgroup G) (z : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hgen : plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz
        (residualIn (pointParabolicPullback d)) ⊔
      plusImage K L T z v hL hz
        (residualIn (planeParabolicPullback d)))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    ∃ R ∈ ({pointParabolicPullback d, planeParabolicPullback d} :
      Set (Subgroup G)),
      R ≤ K ∧ ¬ residualIn R ≤ centralizer ({z} : Set G) := by
  exact moving_residual_of_plus_generation K L T
    (pointParabolicPullback d) (planeParabolicPullback d) z v hL hz
    (pointParabolicPullback_le d) (planeParabolicPullback_le d) hgen hm

/-- The actual `Y_z` membership supplies the nontrivial plus image used by the
source action.  This is kept next to the moving-residual theorem so the
source's selected component, rather than an abstract matrix subgroup, is the
one used in the generation step. -/
theorem moving_residual_of_marked_Yz
    {T : Subgroup G} {v : G} {K : Subgroup G} {F : Type}
    [Field F] [Finite F] [CharP F 2]
    (d : MarkedSp4Model T v K F) (L : Subgroup G) (z : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hgen : plusImage K L T z v hL hz K ≤
      plusImage K L T z v hL hz
        (residualIn (pointParabolicPullback d)) ⊔
      plusImage K L T z v hL hz
        (residualIn (planeParabolicPullback d)))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    (∃ R ∈ ({pointParabolicPullback d, planeParabolicPullback d} :
      Set (Subgroup G)),
      R ≤ K ∧ ¬ residualIn R ≤ centralizer ({z} : Set G)) ∧
      plusImage K L T z v hL hz K ≠ ⊥ := by
  refine ⟨moving_residual_of_marked_parabolics d L z hL hz hgen hm, ?_⟩
  exact plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK

/-- The concrete residuals in the marked matrix model have the exact rank-one
quotient required by 13.6.19. -/
theorem point_model_residual_isL2EvenBlock
    {F : Type}
    [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (pointResidual (F := F)) n :=
  Theory.SpecificGroups.SymplecticFour.pointResidual_isL2EvenBlock hcard hn

theorem plane_model_residual_isL2EvenBlock
    {F : Type}
    [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n) :
    IsL2EvenBlock (planeResidual (F := F)) n :=
  Theory.SpecificGroups.SymplecticFour.planeResidual_isL2EvenBlock hcard hn

/-- The actual quotient model carried by the source `Sp₄` block predicate. -/
theorem quotient_model_of_sp4_block {H : Type*} [Group H]
    (h : IsSp4FourBlock H) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nat.card F = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Sp F) :=
  Theory.SpecificGroups.SymplecticFour.isSp4FourBlock_quotient_model h

/-- Transport the concrete rank-one block to an actual source residual using
the marked residual equivalence. -/
theorem source_point_residual_isL2EvenBlock
    {R : Type*} [Group R] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : pointLocal (F := F) ≃* R) :
  IsL2EvenBlock R n :=
  (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.pointLocal_isL2EvenBlock
    hcard hn).of_mulEquiv e

theorem source_plane_residual_isL2EvenBlock
    {R : Type*} [Group R] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (e : planeLocal (F := F) ≃* R) :
  IsL2EvenBlock R n :=
  (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.planeLocal_isL2EvenBlock
    hcard hn).of_mulEquiv e

/-- The precise source hypotheses that establish membership in the actual
`Chapter1.LIn` family.  Keeping the C-component, Sylow and core clauses
separate makes the final membership proof visible. -/
structure LocalResidualInput (H S R : Subgroup G) where
  contained : R ≤ H
  cComponent : (R.subgroupOf (R ⊔ S)).IsCComponent
  sylow : Chapter1.IsSylowIn 2 S (R ⊔ S)
  nontrivial_two_core : (R ⊔ S).pCoreIn 2 ≠ ⊥

theorem LocalResidualInput.mem_LIn
    {H S R : Subgroup G} (d : LocalResidualInput H S R) :
    R ∈ Chapter1.LIn H S := by
  exact ⟨d.contained, d.cComponent, d.sylow, d.nontrivial_two_core⟩

/-- An actual source core triple.  The two core inclusions are intrinsic to
the selected residual; the nonzero commutator is the output of the marked
module calculation. -/
structure CoreTripleWitness (R : Subgroup G) where
  U : Subgroup G
  Q : Subgroup G
  U_le_core : U ≤ R.pCoreIn 2
  Q_le_core : Q ≤ R.pCoreIn 2
  nonzero : ⁅⁅U, R⁆, Q⁆ ≠ ⊥

theorem residual_not_short_of_core_triple
    (R : Subgroup G) (w : CoreTripleWitness R) :
    ¬ IsShort R :=
  not_short_of_core_triple R w.U w.Q w.U_le_core w.Q_le_core w.nonzero

/-- An injective model map cannot turn a nonzero triple commutator into the
zero subgroup.  This elementary transport is the module-to-source step and
does not use a splitting of the extension. -/
theorem core_triple_ne_bot_of_mulEquiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (U R Q : Subgroup A)
    (hne : ⁅⁅U.map e.toMonoidHom, R.map e.toMonoidHom⁆,
      Q.map e.toMonoidHom⁆ ≠ ⊥) :
    ⁅⁅U, R⁆, Q⁆ ≠ ⊥ := by
  intro h
  apply hne
  have hm := congrArg (Subgroup.map e.toMonoidHom) h
  rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_bot] at hm
  exact hm

/-- Transport the marked module's nonzero triple commutator back to the
source residual.  The model is an arbitrary group isomorphism; no semidirect
product or extension splitting is used. -/
def lift_marked_core_triple
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (U R Q : Subgroup A)
    (hU : U ≤ R.pCoreIn 2) (hQ : Q ≤ R.pCoreIn 2)
    (hmodel : ⁅⁅U.map e.toMonoidHom, R.map e.toMonoidHom⁆,
      Q.map e.toMonoidHom⁆ ≠ ⊥) :
    CoreTripleWitness (R := R) := by
  exact ⟨U, Q, hU, hQ,
    core_triple_ne_bot_of_mulEquiv e U R Q hmodel⟩

/-- The terminal source application for either marked residual.  All SQTK,
generalized-fitting and minimal-parabolic assumptions are the genuine C.1.26
inputs for the actual source residual. -/
structure C126Data {𝒦 : GroupClass.{u}}
    (choices : DistinguishedPairs.{u}) (source : C126Source 𝒦 choices)
    (R T : Subgroup G) (z v : G) where
  local_mem : residualIn R ∈ Chapter1.LIn (Gv v) (Tv T v)
  normalized : Tv T v ≤ normalizer (residualIn R : Set G)
  sqtk : IsSQTK 𝒦 (residualIn R ⊔ Tv T v : Subgroup G)
  fitting : generalizedFitting (residualIn R ⊔ Tv T v : Subgroup G) =
    pCore 2 (residualIn R ⊔ Tv T v : Subgroup G)
  minimal_parabolic : ∀ S : Sylow 2
      (residualIn R ⊔ Tv T v : Subgroup G),
      (S : Subgroup (residualIn R ⊔ Tv T v : Subgroup G)).map
        (residualIn R ⊔ Tv T v).subtype = Tv T v →
      ChapterB.IsMinimalParabolicOver S ⊤

theorem false_of_marked_residual_core_triple [Finite G]
    {𝒦 : GroupClass.{u}} (choices : DistinguishedPairs.{u})
    (source : C126Source 𝒦 choices)
    {T R : Subgroup G} {z v : G}
    (d : C126Data choices source R T z v)
    (hmove : ¬ residualIn R ≤ centralizer ({z} : Set G))
    (h16 : ∀ D ∈ Chapter1.LIn (Gv v) (Tv T v),
      Tv T v ≤ normalizer (D : Set G) → ¬ D ≤ centralizer ({z} : Set G) →
      CharacteristicNormalizerObstruction (Tv T v) D)
    {U Q : Subgroup G}
    [IsQuasisimple (residualIn R ⧸ pCore 2 (residualIn R))]
    (hU : U ≤ (residualIn R).pCoreIn 2)
    (hQ : Q ≤ (residualIn R).pCoreIn 2)
    (hne : ⁅⁅U, residualIn R⁆, Q⁆ ≠ ⊥) : False :=
  false_of_moving_residual_core_triple choices source T R U Q z v
    d.local_mem d.normalized hmove h16 d.sqtk d.fitting
    d.minimal_parabolic hU hQ hne

end SymplecticFour
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics
end
