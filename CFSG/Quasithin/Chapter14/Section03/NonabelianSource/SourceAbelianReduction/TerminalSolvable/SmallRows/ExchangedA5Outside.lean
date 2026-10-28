module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.ExchangedA5
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelFixedPoint
public import Theory.Representation.SymplecticFixedLine
public import Theory.Representation.OrthogonalFourPlusMatrix.Displacement

/-!
# The original outside actor for the exchanged A₅ tensor

If the actual elementary actor lies in the tensor component span, its action
is linear over F₄. Its fixed space therefore cannot be the source's single
binary line. The other original fixed-point alternative supplies an element
moving at most two binary dimensions, whereas every nonidentity element of
SL₂(4) × SL₂(4) in this tensor action moves at least four. Thus the original
actor lies outside the literal dotted span.

The marked-source consumer discharges the fixed-point alternative using the
existing original flag calculation. Its tensor ActionModel remains the
independent input of the marked-image owner; the full wreath quotient and
final terminal-solvability assembly remain with this terminal source family.
Source: Aschbacher–Smith G.11.1(3), G.11.2(7) and 14.3.15,
printed pp.364 and 994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ClassicalOrthogonal.FourPlusMatrix.Binary
variable {G : Type*} [Group G] [Finite G]

/-- The genuine G.11 fixed-point alternative forces the actor outside the
literal tensor component span. -/
theorem ExchangedA5.ActionModel.actor_not_le_of_fixedPointAlternative
    {T : Sylow 2 G} {M : Subgroup G}
    {F : InvariantFlag T (rankTwoSeed T M) 2}
    [IsElementaryAbelian 2 F.Uhat] {g : G}
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    {K : Subgroup G} (m : ExchangedA5.ActionModel F K)
    {v : Additive F.Uhat} (hv : v ≠ 0)
    (hfixed : MarkedSource.FixedPointAlternative (F := F) (g := g) (v := v)) :
    ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)) := by
  intro hin
  let A := F.terminalDot (F.X g)
  let D := F.terminalDot (conjugateSpanBy K (T : Subgroup G))
  let q : A →* ModelGroup := m.componentEquiv.toMonoidHom.comp (inclusion hin)
  have he (x : A) (w : Additive F.Uhat) :
      m.coordinates (F.terminalRepresentation x w) = action (q x) (m.coordinates w) :=
    m.intertwines (inclusion hin x) w
  rcases hfixed with hline | ⟨x,hx,hr,hm⟩
  · let : Module ClassicalOrthogonal.FourPlusMatrix.Binary.F (Additive F.Uhat) :=
      SymplecticFixedLine.coordinateModule m.coordinates
    have hsmul (a : ClassicalOrthogonal.FourPlusMatrix.Binary.F) (w : Additive F.Uhat) :
        m.coordinates (a • w) = a • m.coordinates w := m.coordinates.apply_symm_apply _
    let : SMulCommClass ClassicalOrthogonal.FourPlusMatrix.Binary.F (ZMod 2) (Additive F.Uhat) :=
      ⟨fun a b w => by
        apply m.coordinates.injective
        simp only [hsmul,m.coordinates.map_smul,smul_comm a b]⟩
    have hlin (x : A) (a : ClassicalOrthogonal.FourPlusMatrix.Binary.F) (w : Additive F.Uhat) :
        F.terminalRepresentation x (a • w) = a • F.terminalRepresentation x w := by
      apply m.coordinates.injective
      rw [he,hsmul,hsmul,he]
      exact (ClassicalOrthogonal.FourPlusMatrix.matrixAction (q x)).map_smul a _
    have hc := SymplecticFixedLine.card_le_two_of_fixed_line
      F.terminalRepresentation A hlin v hv hline
    have hfour : Nat.card ClassicalOrthogonal.FourPlusMatrix.Binary.F = 4 := by
      rw [Nat.card_eq_fintype_card]
      exact Representation.SL2FourNatural.card_field
    omega
  · have hqx : q x ≠ 1 := by
      intro hq
      have hw : F.terminalRepresentation x = 1 := by
        apply LinearMap.ext
        intro w
        apply m.coordinates.injective
        rw [he,hq,map_one]
        rfl
      rw [hw,sub_self,LinearMap.range_zero] at hm
      exact hv hm
    have hmap :
        (LinearMap.range (F.terminalRepresentation x - 1)).map m.coordinates.toLinearMap =
          LinearMap.range (action (q x) - LinearMap.id) := by
      ext w
      constructor
      · rintro ⟨u,⟨z,rfl⟩,rfl⟩
        refine ⟨m.coordinates z,?_⟩
        change action (q x) (m.coordinates z) - m.coordinates z =
          m.coordinates (F.terminalRepresentation x z-z)
        rw [map_sub,he]
      · rintro ⟨u,rfl⟩
        refine ⟨(F.terminalRepresentation x - 1) (m.coordinates.symm u),
          ⟨m.coordinates.symm u,rfl⟩,?_⟩
        change m.coordinates (F.terminalRepresentation x (m.coordinates.symm u) -
          m.coordinates.symm u) = action (q x) u-u
        rw [map_sub,he,m.coordinates.apply_symm_apply]
    have hd := ClassicalOrthogonal.FourPlusMatrix.Displacement.displacement_rank_four (q x) hqx
    rw [←hmap,LinearEquiv.finrank_map_eq] at hd
    omega

namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- Original marked-source application: the outside clause of G.11.2(7)
is proved on the same actor, component span and tensor coordinates. -/
theorem tensor_actor_not_le_span {K : Subgroup G} (m : ExchangedA5.ActionModel F K) :
    ¬ F.terminalDot (F.X g) ≤ F.terminalDot (conjugateSpanBy K (T : Subgroup G)) :=
  m.actor_not_le_of_fixedPointAlternative s.hypothesis.point_ne_zero s.fixedPointAlternative

/-- The original tensor branch now retains only its separately owned action
model and the full wreath quotient from 14.3.6(3). -/
theorem tensor_false_of_wreath {K : Subgroup G} (hK : ComponentLift F g K)
    (m : ExchangedA5.ActionModel F K)
    (eJ : ((conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) : Subgroup G)) ≃*
        Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.Wreath) : False :=
  source_exchanged_a5_false_of_tensor_and_wreath s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
    F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.hypothesis hK m
    (s.tensor_actor_not_le_span m) eJ

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
