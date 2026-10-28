module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeLinearThree
public import Theory.Representation.JankoTwo.NormalSylowBound

/-!
# Excluding the whole marked Hall–Janko component

The original elementary actor is normal in the original ambient Sylow
subgroup. Faithful irreducible conjugation bounds its order by eight, so the
marked dimension identity gives degree at most eight. The actual faithful
irreducible Hall–Janko binary module has degree twelve, a contradiction.
The final adapter concludes the original component lift and component cases.

Source: Aschbacher–Smith G.9.3, G.11.1(4), G.11.7 and 14.3.15.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- The original whole marked Hall–Janko row is impossible. -/
theorem not_whole_janko_two (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  have hI := s.selected.isIrrPlus
  have hfix := s.fixedSpace_eq_bot
  rw [hi,hHL] at hI
  rw [hHL] at hfix
  let : Representation.IsIrreducible (F.terminalRepresentation.comp L.subtype) :=
    component_irreducible_of_top_isIrrPlus F.terminalRepresentation L hI hfix
  obtain ⟨S,_,hXS,hXn⟩ := s.actor_normalSylow
  have hcard := Representation.JankoTwo.normal_elementary_actor_card_le_eight
    F.terminalRepresentation s.hypothesis.faithful L e S (F.terminalDot (F.X g)) hXS hXn
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤ 2 ^ 3 := by
    have heq : Nat.card (F.terminalDot (F.X g)) =
        2 ^ Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by
      rw [← Nat.card_congr (Additive.toMul (α := F.terminalDot (F.X g)))]
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (F.terminalDot (F.X g))))
    rw [← heq]
    exact hcard
  have hr : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤ 3 :=
    (pow_le_pow_iff_right₀ (by decide : 1< (2:ℕ))).mp hpow
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  have hσi : Representation.IsIrreducible σ :=
    (Representation.irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr inferInstance
  have hσf : Function.Injective σ := s.hypothesis.faithful.comp
    (L.subtype_injective.comp e.symm.injective)
  have hd := s.actor_dimension
  have hdeg := Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hσf hσi (by omega)
  omega
/-- The literal original local lift in the impossible Hall–Janko row. -/
theorem local_lift_of_whole_janko_two (hi : I=⊤) (hHL : componentOrbit L ⊤ = L)
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_janko_two hi hHL e).elim
end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
