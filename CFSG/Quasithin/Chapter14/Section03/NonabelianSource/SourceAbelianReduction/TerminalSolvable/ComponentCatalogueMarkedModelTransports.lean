module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRankOne
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedLinearThree
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedSymplectic
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedG2
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedBinaryLinear
public import Theory.SpecificGroups.PSL3.UniversalProjection.Basic
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The actual binary classical carriers in the marked two-copy branch

The model predicates retain their finite fields and projective quotients.
The scalar projection supplies the SL3 central covering; characteristic two
identifies PSp4 with Sp4 and the genuine nonbinary derived group. All resulting
actions use the same constituent image and feed the complete two-copy source
classifier and its intrinsic local-lift consumer.

Source: Aschbacher–Smith G.9.3 and G.11.8, printed pp.353–356,368–369.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
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

open scoped MatrixGroups
open Chapter1.Section02.LocalModels

theorem not_double_dimension_projective_linear_three
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) 3 (2 ^ n)) : False := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.not_double_dimension_linear_three_cover hk hd
    (s.orbit_eq_component_of_double_dimension hk hd)
    (e.symm.toMonoidHom.comp (Matrix.PSL3.projection k))
    (e.symm.surjective.comp (Matrix.PSL3.projection_surjective k))
    (by rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      Matrix.PSL3.projection_ker]) n hn hcard

theorem not_double_dimension_special_linear_three
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 0 < n)
    (hm : IsSL (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) 3 (2 ^ n)) : False := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.not_double_dimension_linear_three_cover hk hd
    (s.orbit_eq_component_of_double_dimension hk hd)
    e.symm.toMonoidHom e.symm.surjective
    (by rw [e.symm.toMonoidHom.ker_eq_bot_iff.mpr e.symm.injective]; exact bot_le)
    n hn hcard

theorem imageCases_of_double_dimension_projective_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) 2 (2 ^ n)) : s.ImageCases := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.imageCases_of_smallComponentImage
    (s.smallComponentImage_of_double_dimension_binary_rank_one hk hd
      (s.orbit_eq_component_of_double_dimension hk hd)
      (e.trans (Theory.PSL2.sl2QuotientEquiv k).symm) n hn hcard)

theorem imageCases_of_double_dimension_projective_symplectic
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) 2 (2 ^ n)) : s.ImageCases := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.imageCases_of_double_dimension_symplectic hk hd
    (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm.trans
      (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hcard hn).symm))
    n (by omega) hcard

theorem imageCases_of_double_dimension_full_g2
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassificationModels.IsG2At (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) (2 ^ n)) : s.ImageCases := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.imageCases_of_double_dimension_g2 hk hd
    (e.trans (Atlas.G2.DerivedEvenOrder.derivedEquivModel (by omega) hcard).symm)
    n (by omega) hcard

theorem imageCases_of_double_dimension_projective_symplectic_derived
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃*
        commutator (ClassicalGroup.PSp 2 (ZMod 2))) : s.ImageCases := by
  let f := (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := ZMod 2)).symm
  let a := (f.subgroupMap (commutator (ClassicalGroup.PSp 2 (ZMod 2)))).trans
    (MulEquiv.subgroupCongr (show (commutator (ClassicalGroup.PSp 2 (ZMod 2))).map
      f.toMonoidHom = commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective]; rfl))
  exact s.imageCases_of_double_dimension_symplectic hk hd (e.trans a) 1 (by decide) (by simp)

theorem imageCases_of_double_dimension_binary_linear_model
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L) n 2) : s.ImageCases := by
  obtain ⟨k, _, _, hcard, ⟨e⟩⟩ := hm
  let : Fintype k := Fintype.ofFinite k
  let a : k ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  rcases hn with rfl | rfl
  · exact s.imageCases_of_double_dimension_binary_four hk hd (e.trans (Atlas.fieldEquivPSL 4 a))
  · exact (s.not_double_dimension_binary_five hk hd (e.trans (Atlas.fieldEquivPSL 5 a))).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
