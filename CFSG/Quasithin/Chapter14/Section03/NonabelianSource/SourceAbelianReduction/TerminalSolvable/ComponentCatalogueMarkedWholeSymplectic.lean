module
public import Theory.Representation.SymplecticNormalActors
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedWholeG2

/-!
# The complete whole marked symplectic row

The original G.9 window recognizes the actual natural Sp₄(2ⁿ) action. Its
degree is 4n, while the original actor has rank 2n−1 and is normal in the
original ambient Sylow. The natural normalizer and the field-fixed Sylow
bound make that actor inner, hence coefficient linear. The original marked
geometry forces its coefficient field to be binary. The binary derived
endpoint is the genuine A₆ carrier, and both carrier conventions feed the
literal local-lift consumer.

Source: Aschbacher–Smith G.9.3(9), G.11.7 and 14.3.15, printed pp.354,367–368,994.
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
include s
open ChapterG.Section09 ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition
open Theory.SpecificGroups.SymplecticFour
attribute [local instance] ZMod.algebra

/-- The original normal Sylow actor on a whole nonbinary natural Sp₄
component is coefficient linear, contradicting the original marked geometry. -/
theorem not_whole_symplectic_natural
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n)
    (hnat : Quasiequivalent (F.terminalRepresentation.comp L.subtype) (binaryNatural k)) : False := by
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  have h9 := s.componentHypothesis_of_whole hi
  rw [hHL] at h9
  let : IsIrreducible (F.terminalRepresentation.comp L.subtype) := h9.irreducible
  have hdim := finrank_of_quasiequivalent hcard hnat
  have hd := s.actor_dimension
  have hq : 2 < Nat.card k := by
    rw [hcard]
    simpa using Nat.pow_lt_pow_right (by decide : 1<2) (show 1<n by omega)
  obtain ⟨e,c,hc⟩ := hnat
  let ef := e.trans (derivedEquivFull_of_card_gt_two hq)
  let τ : Representation (ZMod 2) F.TerminalHdot (Vector k) :=
    c.conjRingEquiv.toMonoidHom.comp F.terminalRepresentation
  have ht (x : F.TerminalHdot) (w : Vector k) :
      τ x w = c (F.terminalRepresentation x (c.symm w)) := rfl
  have hτ (l : L) (w : Vector k) : τ l w = symplecticNatural 2 (ef l) w := by
    rw [ht]
    change c ((F.terminalRepresentation.comp L.subtype) l (c.symm w)) = _
    rw [hc,c.apply_symm_apply]
    simp only [ef,MulEquiv.trans_apply,derivedEquivFull_of_card_gt_two_apply]
    rfl
  obtain ⟨S,_,hXS,hXn⟩ := s.actor_normalSylow
  have hA : Nat.card (F.terminalDot (F.X g)) ≤ 2^(2*n) := by
    rw [h9.card_actor]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hinner := Representation.SymplecticNormalActors.natural_normal_actor_inner
    τ L (F.terminalDot (F.X g)) ef hτ hn hcard S hXS hXn hA
  let : Module k (Additive F.Uhat) := Representation.SymplecticFixedLine.coordinateModule c
  have hsmul (a : k) (w : Additive F.Uhat) : c (a • w) = a • c w := c.apply_symm_apply _
  let : SMulCommClass k (ZMod 2) (Additive F.Uhat) := ⟨fun a b w => by
    apply c.injective
    simp only [hsmul,c.map_smul,smul_comm a b]⟩
  let : IsScalarTower (ZMod 2) k (Additive F.Uhat) :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      apply c.injective
      rw [hsmul,c.map_smul]
      exact IsScalarTower.algebraMap_smul k a (c w))
  have hL : ∀ (l : L) (a : k) (w : Additive F.Uhat),
      F.terminalRepresentation l (a • w) = a • F.terminalRepresentation l w := by
    intro l a w
    apply c.injective
    change c ((F.terminalRepresentation.comp L.subtype) l (a • w)) =
      c (a • (F.terminalRepresentation.comp L.subtype) l w)
    rw [hc,hsmul,hsmul,hc]
    exact (symplecticDerivedNatural 2 (e l)).map_smul a (c w)
  have hlin := Representation.SymplecticFixedLine.coefficient_linear_of_inner
    F.terminalRepresentation L (F.terminalDot (F.X g)) ef hL hinner
  have hb := s.coefficient_card_le_two_of_actor_linear (k := k) (by omega) hlin
  omega

/-- Recognition in the genuine G.9 window excludes the whole nonbinary
derived symplectic carrier, with no extra natural-action premise. -/
theorem not_whole_nonbinary_symplectic
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) k))
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : False := by
  have h9 := s.componentHypothesis_of_whole hi
  rw [hHL] at h9
  let σ := (F.terminalRepresentation.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h9.irreducible
  have hσ : Function.Injective σ := s.hypothesis.faithful.comp
    (L.subtype_injective.comp e.symm.injective)
  have hw := component_degree_window_of_automorphism_rank h9 e
    (EvenTwoRank.derived_automorphism_rank_le hcard hn)
  exact s.not_whole_symplectic_natural hi hHL hn hcard
    (quasiequivalent_of_comp_equiv e (Nonbinary.small_quasiequivalent hn hcard hσ hw.2))

/-- The whole derived symplectic family has only its genuine binary A₆
endpoint under the original marked hypotheses. -/
theorem imageCases_of_whole_symplectic
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2^n) : s.ImageCases := by
  by_cases hn1 : n = 1
  · have hk2 : Nat.card k = 2 := by simpa [hn1] using hcard
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
      (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
    exact Or.inr (Or.inl (Or.inr ⟨eL.symm.trans
      (e.trans (Binary.derivedEquivAlternatingSix hk2))⟩))
  · exact (s.not_whole_nonbinary_symplectic hi hHL e (by omega) hcard).elim

/-- The full projective symplectic model is excluded with its actual finite
field witness and the literal central quotient. -/
theorem not_whole_projective_symplectic
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp L 2 (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := EvenProjective.charTwo_of_card hcard
  let a := (e.trans EvenProjective.equiv.symm).trans (EvenTwoRank.derivedEquiv hcard hn).symm
  exact s.not_whole_nonbinary_symplectic hi hHL a hn hcard

/-- The recognized binary endpoint and the excluded nonbinary family feed
the literal original component lift, including its intrinsic two-core quotient. -/
theorem local_lift_of_whole_symplectic
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* commutator (Matrix.symplecticGroup (Fin 2) k))
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card k = 2^n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_symplectic hi hHL e n hn hcard)

/-- The same local-lift consumer for the source's projective carrier predicate. -/
theorem local_lift_of_whole_projective_symplectic
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSp L 2 (2^n)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  (s.not_whole_projective_symplectic hi hHL hn model).elim

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
