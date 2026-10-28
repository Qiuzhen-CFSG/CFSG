module
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.Elementary
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedCoefficientField
public import Mathlib.Algebra.Module.TransferInstance




/-!
# Whole marked binary rank-one components

An elementary actor normalizing a Hermitian SL₂ component is linear over the
fixed half-field. Transport that scalar structure to the original module;
the marked coefficient bound forces the parameter to one, giving A₅.
Together with the completed natural-row theorem and the exceptional
triple-tensor parameter n = 3, the actual G.9 classifier exhausts the whole
binary rank-one component row. All conclusions retain the literal component
image and feed the original local lift.

Source: Aschbacher--Smith G.11.7 and 14.3.15, printed pp.366--368,994.
-/

@[expose] public noncomputable section
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedRankOneModels
open Representation Representation.OrthogonalFourMinus.FiniteModel
variable {D V k : Type*} [_root_.Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [Field k] [Finite k] [CharP k 2]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2
local instance (r : ℕ) : Algebra (ZMod 2) (fixedField r) := ZMod.algebra _ 2
local instance (r : ℕ) [NeZero r] : Module (ZMod 2) (Space r) :=
  Module.compHom (Space r) (algebraMap (ZMod 2) (fixedField r))

omit [Finite k] [CharP k 2] in
private theorem hermitian_coordinates
    (ρ : Representation (ZMod 2) D V) (e : D ≃* SL(2,k)) (r : ℕ) [NeZero r]
    (h : SL2.BinarySmall.IsHermitian (ρ.comp e.symm.toMonoidHom) r) :
    ChapterG.Section09.Quasiequivalent ρ (SL2.BinarySmall.hermitian r) := by
  obtain ⟨f,⟨d⟩⟩ := h
  refine ⟨e.trans (Atlas.fieldEquivSL 2 f),d.toLinearEquiv,?_⟩
  intro g w
  have hh := Representation.IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (e g) w
  change d (ρ (e.symm (e g)) w) = SL2.BinarySmall.hermitian r
    (Matrix.SpecialLinearGroup.map f.toRingHom (e g)) (d w) at hh
  rw [e.symm_apply_apply] at hh
  exact hh
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedRankOneModels

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
open Representation.OrthogonalFourMinus.FiniteModel
local instance (n : ℕ) : Algebra (ZMod 2) (fixedField n) := ZMod.algebra _ 2
local instance (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- The actual whole Hermitian component has quadratic field of order four. -/
theorem hermitian_parameter_one
    (hHL : componentOrbit L ⊤ = L) (n : ℕ) [NeZero n]
    (hnat : ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp L.subtype) (SL2.BinarySmall.hermitian n)) : n = 1 := by
  classical
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  obtain ⟨e,c,hc⟩ := hnat
  let τ : Representation (ZMod 2) F.TerminalHdot (Space n) :=
    c.conjRingEquiv.toMonoidHom.comp F.terminalRepresentation
  have ht (a : F.TerminalHdot) (w : Space n) :
      τ a w = c (F.terminalRepresentation a (c.symm w)) := rfl
  have hcoord (l : L) (w : Space n) : τ l w = SL2.BinarySmall.hermitian n (e l) w := by
    rw [ht]
    simpa only [MonoidHom.comp_apply,Subgroup.coe_subtype,c.apply_symm_apply] using hc l (c.symm w)
  have hlin := Representation.OrthogonalFourMinus.RankOne.AmbientActions.elementary_normal_component_linear
    n τ L e hcoord (F.terminalDot (F.X g))
  have hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 4*n :=
    c.finrank_eq.trans (Representation.OrthogonalFourMinus.RankOne.space_binary_finrank n)
  by_contra hn
  have hn0 := NeZero.pos n
  have hdim : 6 ≤ Module.finrank (ZMod 2) (Additive F.Uhat) := by omega
  let : SMul (ZMod 2) (fixedField n) := (ZMod.algebra (fixedField n) 2).toSMul
  let : Module (fixedField n) (Additive F.Uhat) := c.toAddEquiv.module (fixedField n)
  let : IsScalarTower (ZMod 2) (fixedField n) (Additive F.Uhat) :=
    IsScalarTower.of_algebraMap_smul (fun a w => by
      fin_cases a
      · change algebraMap (ZMod 2) (fixedField n) (0 : ZMod 2) • w = (0 : ZMod 2) • w
        simp only [map_zero,zero_smul]
      · change algebraMap (ZMod 2) (fixedField n) (1 : ZMod 2) • w = (1 : ZMod 2) • w
        simp only [map_one,one_smul])
  have htower : IsScalarTower (ZMod 2) (fixedField n) (Additive F.Uhat) := inferInstance
  have hb : Nat.card (fixedField n) ≤ 2 := @coefficient_card_le_two_of_actor_linear
    G _ _ T M Mc F _ _ g _ B v L I s (fixedField n) _ _ _ htower hdim (by
    intro x d w
    apply c.injective
    change c (F.terminalRepresentation x (c.symm (d • c w))) =
      c (c.symm (d • c (F.terminalRepresentation x w)))
    rw [c.apply_symm_apply]
    change τ x (d • c w) = _
    rw [hlin,ht,c.symm_apply_apply])
  rw [card_fixedField] at hb
  have hnle : n ≤ 1 := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (by simpa using hb)
  omega

/-- The whole Hermitian row gives the permitted alternating-five image. -/
theorem imageCases_of_hermitian_rank_one
    (hHL : componentOrbit L ⊤ = L) (n : ℕ) [NeZero n]
    (hnat : ChapterG.Section09.Quasiequivalent
      (F.terminalRepresentation.comp L.subtype) (SL2.BinarySmall.hermitian n)) : s.ImageCases := by
  have hn := s.hermitian_parameter_one hHL n hnat
  have hcard : Nat.card (Field n) = 4 := by
    rw [GaloisField.card 2 (2*n) (Nat.mul_ne_zero (by decide) (NeZero.ne n)),hn]
    norm_num
  obtain ⟨e,c,hc⟩ := hnat
  let eA := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard).some
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  exact Or.inr (Or.inl (Or.inl ⟨eL.symm.trans (e.trans
    ((Theory.PSL2.sl2QuotientEquiv (Field n)).trans eA))⟩))

/-- Whole-space coordinates carry the literal constituent-image action to
its original Hermitian normal component. -/
theorem imageCases_of_whole_hermitian_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L) (n : ℕ) [NeZero n]
    (hnat : ChapterG.Section09.Quasiequivalent
      ((kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)).comp
          (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
            (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L).subtype)
      (SL2.BinarySmall.hermitian n)) : s.ImageCases := by
  subst I
  obtain ⟨e,c,hc⟩ := hnat
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) ⊤ s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) ⊤ s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  let d := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) (Additive F.Uhat)) ≃ₗ[ZMod 2] _).symm.trans c
  apply s.imageCases_of_hermitian_rank_one hHL n
  refine ⟨eL.trans e,d,?_⟩
  intro l w
  exact hc (eL l) ⟨w,Submodule.mem_top⟩

/-- The whole Hermitian row supplies the original local component lift. -/
theorem local_lift_of_whole_hermitian_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L) (n : ℕ) [NeZero n]
    (hnat : ChapterG.Section09.Quasiequivalent
      ((kerRepresentation (MarkedAction.action F.terminalRepresentation (componentOrbit L ⊤)
        (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes)).comp
          (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
            (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L).subtype)
      (SL2.BinarySmall.hermitian n)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_hermitian_rank_one hi hHL n hnat)

/-- Every whole binary rank-one row has one of the original allowed images. -/
theorem imageCases_of_whole_binary_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* SL(2,k)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : s.ImageCases := by
  let := ZMod.algebra k 2
  have hf : ActorFaithful (F := F) (g := g) (I := I) := by
    by_contra hnf
    exact s.constituent_ne_top_of_not_actorFaithful hnf hi
  have hc := s.componentHypothesis_of_actorFaithful hf
  have he := congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  dsimp only at hc
  rw [he] at hc
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  let eI := eL.symm.trans e
  rcases (ChapterG.Section09.DefiningCharacteristic.rank_one_module_alternatives hc eI n hn hcard).2
    with ⟨_,_,hnat⟩ | ⟨r,hr,_,_,_,hherm⟩ | ⟨hn3,_,_,_,_,_⟩
  · obtain ⟨d⟩ := hnat
    apply s.imageCases_of_whole_natural_rank_one hi hHL (k := k) ?_ n hn hcard
    refine ⟨eI,d.toLinearEquiv,?_⟩
    intro l w
    have hh := Representation.IntertwiningMap.isIntertwining _ _ d.toIntertwiningMap (eI l) w
    simpa only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,eI.symm_apply_apply,Representation.Equiv.toLinearEquiv_apply,Representation.Equiv.coe_toIntertwiningMap] using hh
  · let : NeZero r := ⟨hr.ne'⟩
    exact s.imageCases_of_whole_hermitian_rank_one hi hHL r
      (MarkedRankOneModels.hermitian_coordinates _ eI r hherm)
  · let : Fintype k := Fintype.ofFinite k
    let : Fintype (GaloisField 2 3) := Fintype.ofFinite _
    let f : k ≃+* GaloisField 2 3 := FiniteField.ringEquivOfCardEq (by
      rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hcard,hn3,GaloisField.card 2 3 (by decide)])
    exact Or.inr (Or.inr ⟨he,⟨eI.trans ((Theory.PSL2.sl2QuotientEquiv k).trans
      (Atlas.fieldEquivPSL 2 f))⟩⟩)

/-- The whole binary rank-one model supplies its literal local lift. -/
theorem local_lift_of_whole_binary_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : L ≃* SL(2,k)) (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_binary_rank_one hi hHL e n hn hcard)

/-- The projective binary rank-one carrier supplies the same original images. -/
theorem imageCases_of_whole_projective_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSL L 2 (2^n)) : s.ImageCases := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hcard
  exact s.imageCases_of_whole_binary_rank_one hi hHL
    (e.trans (Theory.PSL2.sl2QuotientEquiv k).symm) n hn hcard

/-- The original local lift for every whole projective binary rank-one row. -/
theorem local_lift_of_whole_projective_rank_one
    (hi : I = ⊤) (hHL : componentOrbit L ⊤ = L)
    {n : ℕ} (hn : 2 ≤ n) (model : ClassicalGroup.IsPSL L 2 (2^n)) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_whole_projective_rank_one hi hHL hn model)

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
