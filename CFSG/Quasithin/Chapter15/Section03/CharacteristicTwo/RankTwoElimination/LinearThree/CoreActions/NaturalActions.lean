module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Layers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SourceCase
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions.SylowAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# The two action bounds in the one- and two-natural-layer cases

Starting with the complete compatible C.1.34 case in LR, faithful layer
transport constructs the actual natural coordinates of Q = [O₂(L),L].
The genuine residual Y_C commutes with the SL₃(2) action on these coordinates.
Its pointwise fixation of the order-four subgroup [V,Y_L] supplies a nonzero
fixed vector; two-perfectness then kills the multiplicity action. Thus Y_C
centralizes Q and, by the residual lifting theorem, L.

The marked parabolic image then identifies the Y-action on L/O₂(L) with
its inner A₄ residual. Every actual Sylow three-subgroup P of Y has nontrivial
cubic image. An element of C_S(P) preserves that residual, excluding graph
action, and the cubic-centralizer calculation kills its two-power-order action.

Thus `source_actions` supplies both action inputs to the existing Frattini
core bound, discharging the Sylow-action helper's premise that Y_C centralizes
L. The complete C.1.34 case, fixed order-four subgroup and earlier parabolic
image remain explicit source inputs. Either conjugate parabolic marking is
allowed, independently of the natural-layer coordinates. The projective line
in the source has binary dimension two. Final conjugate-core case assembly
belongs to the parent; no conjugate-core bound is assumed here.

Source: Aschbacher–Smith, proof of 15.3.23, final paragraph on printed p.1129;
complete C.1.34(1),(2), printed pp.136–137 (manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup Matrix.PSL3Two
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source natural cases give actual residual centralization, with only
the earlier fixed-space output on the literal subgroup [V,Y_L] explicit. -/
theorem source_residual_centralizes (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}} (s : SourceData κ c.L d.R)
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUQ : ⁅d.V, YL d c.L⁆ ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      YC d c.L ≤ centralizer (c.L : Set G) := by
  obtain ⟨a, ha, e, ⟨m⟩⟩ := s.ambient_layer
  exact YC_centralizes_of_order_four d c ha m hU hUQ hfix

/-- Both actual action bounds for the complete natural cases of C.1.34.
The fixed-space and parabolic conclusions preceding the last paragraph of
15.3.23 are explicit. S-invariance of Y_L follows from the local geometry,
and residual centralization is proved before applying the Sylow-action theorem.
The conclusions feed `exists_conjugate_core_le_of_actions` for any chosen P. -/
theorem source_actions (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) {κ : GroupClass.{u}} (s : SourceData κ c.L d.R)
    (hU : Nat.card (⁅d.V, YL d c.L⁆ : Subgroup G) = 4)
    (hUQ : ⁅d.V, YL d c.L⁆ ≤ commutatorCore c.L)
    (hfix : YC d c.L ≤ centralizer ((⁅d.V, YL d c.L⁆ : Subgroup G) : Set G))
    (hSL : d.S ≤ normalizer (c.L : Set G))
    (hY : d.Y = YL d c.L ⊔ YC d c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (M : Subgroup SL) (hstd : M = pointParabolicSL ∨ M = lineParabolicSL)
    (g : SL)
    (hM : ((YL d c.L ⊔ (d.S ⊓ c.L)).subgroupOf c.L).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 c.L))) = M.conjBy g) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∧
      ∀ P : Sylow 3 d.Y,
        d.S ⊓ centralizer (sylowThree d P : Set G) ≤ Chapter4.sectionCentralizer c.L := by
  obtain ⟨hQ, hL⟩ := source_residual_centralizes d c s hU hUQ hfix
  have hSYL := S_normalizes_YL d c.L
    (RankTwo.planeStabilizer_normalizes_yplus d.action d.T d.sylow_le 1 d.choice) hSL
  exact ⟨hQ, fun P =>
    SylowAction.sylow_centralizer_of_parabolic d c e hSL hSYL hY hL M hstd g hM P⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.NaturalActions
