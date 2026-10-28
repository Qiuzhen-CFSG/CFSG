module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentAmbientGeneration
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisFusion
public import Theory.Representation.BinarySevenCode.WeightFourResidualMovement

/-!
# Ambient uniqueness in the proper-overcomponent branch

The literal `O²(C_L(e))` moves every weight-six word: the natural action
maps `C_L(e)` onto the weight-four stabilizer, and a cubic mover lifts to
its two-residual. A Sylow-central weight-six representative therefore gives
a point whose ambient centralizer lies in `N_G(L)` and which `L_e` moves.

For the second component, the natural coordinates and the exact 12.3.7
omega-center decomposition make its nonfixed central-vector stabilizers
maximal. Together with the 12.2.8 containment `L_e ≤ Y`, this generates
`Y` inside `N_G(L)`. Since `K ≤ Y`, residual escape rules out this branch.
This constructs `AmbientA5Uniqueness` and applies it to the existing
proper-component rigidity consumer.

The earlier source coordinates, 12.3.7 equality, 12.2.8 containment and
A.3.14 restriction remain explicit in their respective consumer signatures.
There is no additional movement, maximality, or ambient uniqueness premise.
In particular no A₅ assertion about the solvable weight-four stabilizer
or its residual is used.

Source: Aschbacher--Smith, 12.3.12, printed p.811; 12.3.3, 12.3.6--7,
printed pp.807--809; 12.2.8, printed p.798.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

/-- The original point-centralizer two-residual moves every weight-six word. -/
theorem Le_not_le_weight_six_centralizer (f : V)
    (hf : weight (D.model.coordinates f).toAdd.val = 6) :
    ¬ P.Le ≤ centralizer ({(f : G)} : Set G) := by
  let C := L ⊓ P.pointCentralizer
  let q : C →* alternatingGroup (Fin 7) := S.projection.comp (inclusion inf_le_left)
  have hq : ∀ a, evenRepresentation a.val (D.model.coordinates P.point).toAdd =
      (D.model.coordinates P.point).toAdd → ∃ x, q x = a := by
    intro a ha
    obtain ⟨l, hl⟩ := S.projection_surjective a
    have he := D.model.equivariant ⟨l, S.chosen.normalizes l.property⟩ P.point
    rw [D.component_action, hl, ha] at he
    have hfix : V.normalizerMonoidHom ⟨l, S.chosen.normalizes l.property⟩ P.point =
        P.point := D.model.coordinates.injective (Multiplicative.toAdd.injective he)
    have hlC : (l : G) ∈ P.pointCentralizer :=
      mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hfix))
    exact ⟨⟨l, l.property, hlC⟩, hl⟩
  obtain ⟨x, hx, hmove⟩ := exists_pResidual_weight_six_mover q
    (D.model.coordinates P.point).toAdd (D.model.coordinates f).toAdd P.weight_four hf hq
  intro h
  have hxc : (x : G) ∈ centralizer ({(f : G)} : Set G) :=
    h (mem_map_of_mem C.subtype hx)
  have hfix : V.normalizerMonoidHom ⟨x, S.chosen.normalizes x.property.1⟩ f = f := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hxc)
  have he := D.model.equivariant ⟨x, S.chosen.normalizes x.property.1⟩ f
  rw [D.component_action ⟨x, x.property.1⟩, hfix] at he
  exact hmove he.symm

/-- The movement premise is supplied by the actual natural-module action. -/
theorem weightSixMovement
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u}) : P.WeightSixMovement := by
  let E : S.NaturalCoordinates :=
    ⟨D.model.coordinates, fun l v => by
      simpa only [D.component_action] using
        D.model.equivariant ⟨l, S.chosen.normalizes l.property⟩ v⟩
  obtain ⟨f, hf, hfc⟩ := E.central_representative_weight structural
    (n := 6) (Or.inr (Or.inr rfl))
  have hf1 : f ≠ 1 := by
    intro he
    have hzero : weight (0 : Word) = 0 := by decide
    have hh := hf
    change weight (D.model.coordinates f).toAdd.val = 6 at hh
    simp only [he, map_one] at hh
    exact (by decide : (0 : ℕ) ≠ 6) (hzero.symm.trans hh)
  have hfZ : (f : G) ∈ P.Z := by
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨S.chosen.le_sylow f.property, hfc, ?_⟩
    let := S.chosen.elementary
    exact elemPow_eq_one_of_isElementaryAbelian _ f.property
  exact ⟨f, hf1, hf, hfZ, P.Le_not_le_weight_six_centralizer f hf⟩

/-- The literal 12.3.7 decomposition and the 12.2.8 containment put
all of the second overcomponent in the original normalizer. -/
theorem overcomponent_le_normalizer_of_natural_omega
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (hLe : P.Le ≤ F.Y) : F.Y ≤ normalizer (L : Set G) :=
  overcomponent_le_normalizer_of_point_generation F SY
    (P.weightSixMovement structural)
    (SY.centralVectorMaximality_of_coordinates_omega DY hsplit) hLe

/-- The ambient uniqueness contract from the literal 12.3.7 decomposition.
The 12.2.8 containment is the last argument of that contract. -/
theorem ambientA5Uniqueness_of_natural_omega
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : P.Overcomponents) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition) :
    AmbientA5Uniqueness (P := P) F := by
  intro W' _ _ hLe
  have hYM := P.overcomponent_le_normalizer_of_natural_omega
    structural F SY DY hsplit hLe
  exact False.elim (P.residual_escape structural
    (F.residual_le.trans (F.le_maximal.trans hYM)))

/-- Application to the existing proper-component rigidity theorem. -/
theorem proper_component_eq_residual_of_natural_omega
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (A : A314RestrictionInput (P := P))
    (hLe : F.E = F.Y → P.Le ≤ F.Y) : F.E = P.K :=
  proper_component_eq_residual structural R F hKY SY A hLe
    (P.ambientA5Uniqueness_of_natural_omega structural F SY DY hsplit)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
