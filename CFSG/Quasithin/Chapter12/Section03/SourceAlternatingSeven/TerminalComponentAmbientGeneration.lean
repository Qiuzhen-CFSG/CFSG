module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentProperRigidity
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNormalizer
public import Theory.GroupTheory.MaximalCentralizerGeneration
public import Theory.Representation.BinarySevenCode.MaximalStabilizers

/-!
# A generation route for the proper-overcomponent endgame

Choose a Sylow-central weight-six vector `f` in the original module.
Its ambient centralizer lies in `N_G(L)`. If the original `L_e` moves
`f`, and `C_Y(f)` is maximal in `Y`, the containment `L_e ≤ Y` forces
`Y ≤ N_G(L)`, contradicting escape of `K ≤ Y`.

Maximality of nonfixed central-vector stabilizers follows here from the
genuine omega-center decomposition of 12.3.7 and the natural A₇ action.
Movement by the literal two-residual of the weight-four stabilizer is
supplied in `TerminalComponentAmbientUniqueness`. The earlier natural
coordinates and omega-center equality remain explicit source inputs.

This replaces the invalid use of `L_e`'s perfect residual in the printed
proof of Aschbacher--Smith 12.3.12, p.811. It uses 12.3.6 for the original
weight-six point and 12.3.7 for the second maximal component.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V Y W : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}

/-- The exact omega-center equality in 12.3.7(1), for the same chosen W. -/
def Setup.NaturalOmegaDecomposition {Y W : Subgroup G} (_SY : Setup T Y W) : Prop :=
  omegaCenterIn ((Y ⊔ (T : Subgroup G)).pCoreIn 2) =
    W ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (Y : Set G))

/-- The natural permutation stabilizer consequence needed in the endgame.
It does not assert containment in the original normalizer. -/
def Setup.CentralVectorMaximality {Y W : Subgroup G} (_SY : Setup T Y W) : Prop :=
  ∀ z ∈ omegaCenterIn (T : Subgroup G),
    ¬ Y ≤ centralizer ({z} : Set G) →
    IsCoatom ((centralizer ({z} : Set G)).subgroupOf Y)

namespace Setup
variable (SY : Setup T Y W)

include SY in
private theorem omega_sylow_le_core_omega :
    omegaCenterIn (T : Subgroup G) ≤
      omegaCenterIn ((Y ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let H := Y ⊔ (T : Subgroup G)
  have hHe : H ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (SY.hypothesis.simpleQTKE.evenCharacteristic T)
      ⟨SY.hypothesis.maximal_faithful.1.1.2.2,
        (show (T : Subgroup G) ≤ H from le_sup_right)⟩
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [H, Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow H (T.subtype le_sup_right)
  intro z hz
  obtain ⟨hzT, hzC, hz2⟩ := (mem_omegaCenterIn_iff _ _).mp hz
  have hzQ : z ∈ centralizer (H.pCoreIn 2 : Set G) := centralizer_le hQT hzC
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨hHe ⟨(show (T : Subgroup G) ≤ H from le_sup_right) hzT, hzQ⟩, hzQ, hz2⟩

/-- The literal 12.3.7 omega-center decomposition makes nonfixed
Sylow-central point stabilizers maximal in the original second component. -/
theorem centralVectorMaximality_of_coordinates_omega
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition) :
    SY.CentralVectorMaximality := by
  intro z hz hn
  let C := omegaCenterIn (T : Subgroup G) ⊓ centralizer (Y : Set G)
  have hCN : C ≤ normalizer (W : Set G) :=
    (inf_le_right.trans (centralizer_le SY.chosen.le_component)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hzsplit : z ∈ W ⊔ C := hsplit ▸ omega_sylow_le_core_omega SY hz
  change z ∈ (↑(W ⊔ C) : Set G) at hzsplit
  rw [coe_mul_of_right_le_normalizer_left W C hCN] at hzsplit
  obtain ⟨w, hw, c, hc, rfl⟩ := hzsplit
  have hw1 : w ≠ 1 := by
    intro he
    apply hn
    intro y hy
    apply mem_centralizer_singleton_iff.mpr
    simpa only [he, one_mul] using (mem_centralizer_iff.mp hc.2) y hy
  let v : W := ⟨w, hw⟩
  let word := (DY.coordinates v).toAdd
  have hword : word ≠ 0 := by
    intro he
    apply hw1
    have hv : v = 1 := by
      apply DY.coordinates.injective
      apply Multiplicative.toAdd.injective
      exact he.trans (by simp)
    exact congrArg Subtype.val hv
  apply isCoatom_of_mem_iff_fixes_evenWord SY.projection SY.projection_surjective
    word hword
  intro y
  have hcfix : (y : G) * c * (y : G)⁻¹ = c :=
    mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc.2) y y.property)
  have hmul : (y : G) * (w*c) * (y : G)⁻¹ = ((y : G)*w*(y : G)⁻¹)*c := by
    calc
      _ = ((y : G)*w*(y : G)⁻¹)*((y : G)*c*(y : G)⁻¹) := by group
      _ = _ := by rw [hcfix]
  rw [mem_subgroupOf, mem_centralizer_singleton_iff, ← mul_inv_eq_iff_eq_mul,
    hmul, mul_left_inj]
  have hequiv := DY.equivariant y v
  constructor
  · intro he
    have hfix : W.normalizerMonoidHom ⟨y, SY.chosen.normalizes y.property⟩ v = v :=
      Subtype.ext he
    rw [hfix] at hequiv
    exact hequiv.symm
  · intro he
    rw [he] at hequiv
    exact congrArg Subtype.val
      (DY.coordinates.injective (Multiplicative.toAdd.injective hequiv))

/-- The same maximality conclusion using the existing local-analysis interface. -/
theorem centralVectorMaximality_of_natural_omega
    (DY : SY.LocalAnalysis) (hsplit : SY.NaturalOmegaDecomposition) :
    SY.CentralVectorMaximality := by
  let EY : SY.NaturalCoordinates :=
    ⟨DY.model.coordinates, fun y v => by
      simpa only [DY.component_action] using
        DY.model.equivariant ⟨y, SY.chosen.normalizes y.property⟩ v⟩
  exact SY.centralVectorMaximality_of_coordinates_omega EY hsplit

end Setup

namespace TerminalPoint
variable {P : TerminalPoint S D}

/-- A central weight-six point moved by the actual `O²(C_L(e))`.
No ambient containment or A₅ recognition is part of this input. -/
def WeightSixMovement (P : TerminalPoint S D) : Prop :=
  ∃ f : V, f ≠ 1 ∧ weight (D.model.coordinates f).toAdd.val = 6 ∧
    (f : G) ∈ P.Z ∧ ¬ P.Le ≤ centralizer ({(f : G)} : Set G)

/-- Maximality of the second point stabilizer converts the original
`L_e ≤ Y` into the ambient containment needed for residual escape. -/
theorem overcomponent_le_normalizer_of_point_generation
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (hmovement : P.WeightSixMovement) (hmax : SY.CentralVectorMaximality)
    (hLe : P.Le ≤ F.Y) : F.Y ≤ normalizer (L : Set G) := by
  obtain ⟨f, hf, hweight, hcentral, hmove⟩ := hmovement
  have hYmove : ¬ F.Y ≤ centralizer ({(f : G)} : Set G) :=
    fun h => hmove (hLe.trans h)
  exact le_of_maximal_pointCentralizer (hmax f hcentral hYmove)
    hLe ((Le_le_original (P := P)).trans L.le_normalizer)
    (inf_le_right.trans (D.pointCentralizers f hf (Or.inr hweight))) hmove

/-- Conditional construction of the existing ambient uniqueness contract.
The source assembly must supply movement and the natural stabilizer theorem. -/
theorem ambientA5Uniqueness_of_point_generation
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : P.Overcomponents) (hmovement : P.WeightSixMovement)
    (hmax : ∀ {W : Subgroup G} (SY : Setup T F.Y W),
      SY.CentralVectorMaximality) : AmbientA5Uniqueness (P := P) F := by
  intro W SY _ hLe
  have hYM := overcomponent_le_normalizer_of_point_generation F SY
    hmovement (hmax SY) hLe
  exact False.elim (P.residual_escape structural
    (F.residual_le.trans (F.le_maximal.trans hYM)))

/-- The actual proper-rigidity consumer, with the generation route replacing
the printed identification of `K` with a perfect residual of `L_e`. -/
theorem proper_component_eq_residual_of_point_generation
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y)
    (hmovement : P.WeightSixMovement)
    (hmax : ∀ {W' : Subgroup G} (SY' : Setup T F.Y W'),
      SY'.CentralVectorMaximality) : F.E = P.K :=
  proper_component_eq_residual structural R F hKY SY A hLe
    (ambientA5Uniqueness_of_point_generation structural F hmovement hmax)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
