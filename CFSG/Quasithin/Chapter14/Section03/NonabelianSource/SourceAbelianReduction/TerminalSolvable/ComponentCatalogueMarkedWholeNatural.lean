module

public import Theory.Representation.SL2NaturalOffenders.MarkedAlternatives
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedProperFaithful

/-!
# The whole natural rank-one row of the marked source

The original fixed-point alternative and the semilinear normalizer of the
actual normal natural component force its field to have order four. The
literal constituent quotient therefore has alternating-five image. Whole-space
coordinates transport the given quotient action before applying this estimate,
and the resulting image case feeds the original ambient local lift.

Source: Aschbacher--Smith, G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative MatrixGroups
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
  {k : Type*} [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
include s

/-- The natural rank-one row of the literal whole action gives A5; the
original fixed-point alternative eliminates every larger defining field. -/
theorem imageCases_of_natural_rank_one
    (hHL : componentOrbit L ⊤ = L)
    (hnat : ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp L.subtype) (SL2.BinarySmall.natural (K := k)))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : s.ImageCases := by
  let := ZMod.algebra k 2
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  obtain ⟨e,c,hc⟩ := hnat
  have halt : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} ∨
    ∃ a : F.terminalDot (F.X g), a ≠ 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2 := by
    rcases s.fixedPointAlternative with hh | ⟨a,ha,hr,_⟩
    · exact Or.inl hh
    · exact Or.inr ⟨a,ha,hr⟩
  have hb := Representation.MarkedSemilinearPlane.card_le_four_of_natural_normal_component
    F.terminalRepresentation s.hypothesis.faithful L e c hc
    (F.terminalDot (F.X g)) v s.hypothesis.point_ne_zero halt n hcard
  have hn2 : n = 2 := by
    rw [hcard] at hb
    have hh : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hb
    omega
  have hk4 : Nat.card k = 4 := by simpa [hn2] using hcard
  let eA := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hk4).some
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  exact Or.inr (Or.inl (Or.inl ⟨eL.symm.trans (e.trans ((Theory.PSL2.sl2QuotientEquiv k).trans eA))⟩))

/-- The source row uses the actual constituent-image action. Whole-space
coordinates identify it with the original action before applying the estimate. -/
theorem imageCases_of_whole_natural_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (hnat : ChapterG.Section09.Quasiequivalent
      ((kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)).comp
          (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
            (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L).subtype)
      (SL2.BinarySmall.natural (K := k)))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : s.ImageCases := by
  subst I
  obtain ⟨e,c,hc⟩ := hnat
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) ⊤ s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  let d := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) ≃ₗ[ZMod 2] _).symm.trans c
  apply s.imageCases_of_natural_rank_one hHL ?_ n hn hcard
  refine ⟨eL.trans e,d,?_⟩
  intro l w
  exact hc (eL l) ⟨w,Submodule.mem_top⟩

/-- The natural whole rank-one row feeds the actual original local lift. -/
theorem local_lift_of_whole_natural_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    (hnat : ChapterG.Section09.Quasiequivalent
      ((kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)).comp
          (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
            (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L).subtype)
      (SL2.BinarySmall.natural (K := k)))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_natural_rank_one hi hHL hnat n hn hcard)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
