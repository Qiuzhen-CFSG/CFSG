module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRecognitionReduction
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.RankOneRecognition.Component
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Binary rank-one recognition in the marked two-copy branch

The two-copy kernel calculation gives the literal constituent action image
actor rank `dim I - 2`. When the component orbit is a single component,
its faithful quotient action satisfies G.9.3 with this reduced rank. The
SL₂ module alternatives and the sharp automorphism-rank bound then force
field size four, constituent dimension four and total dimension eight.

The concrete projective-line isomorphism PSL₂(4) = A₅ identifies the actual
component, and the original local-lift theorem supplies its intrinsic
two-core quotient. No counterexample to the full G.11.2 catalogue is used.
Recognition of the other component models remains a separate obligation.

Source: Aschbacher--Smith G.9.3(6),(7),(16), the degree calculation in
G.11.8, and original 14.3.15, printed pp.354,356--357,368--369,994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
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

/-- The actual nonfaithful constituent quotient satisfies G.9 for a single
component orbit, with the actor rank corrected by its order-two kernel. -/
theorem singleOrbit_componentHypothesis_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L) :
    let H := componentOrbit L ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I
      s.selected.invariant s.actor_stabilizes
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes X)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes L)
      (MarkedAction.image F.terminalRepresentation H X I
        s.selected.invariant s.actor_stabilizes H) (Module.finrank (ZMod 2) I - 2) := by
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let P := H ⊔ X
  let σ := MarkedAction.action F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes
  let q := QuotientGroup.mk' σ.ker
  let : H.Normal := componentOrbit_top_normal L
  have hHP : H ≤ P := le_sup_left
  have hLP : L ≤ P := (le_componentOrbit L ⊤).trans hHP
  have hXP : X ≤ P := le_sup_right
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  have hfH := s.constituent_faithful R s.irreducible
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation H X I
    s.selected.invariant s.actor_stabilizes hfH L (le_componentOrbit L ⊤)
  have hL0 : (L.subgroupOf P).map q ≠ ⊥ := by
    intro hz
    have hbot : L = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro l hl
      have he : eL ⟨l, hl⟩ = 1 := Subtype.ext (hz.le (eL ⟨l, hl⟩).property)
      exact congrArg Subtype.val (eL.injective (he.trans eL.map_one.symm))
    exact s.moved (by rw [hbot, commutator_bot_left])
  refine { s.actorImage_setup_of_double_dimension hk hd with
    quotient := ⟨s.constituentSQTKCover⟩
    component := ((s.component.subgroupOf hLP).map_surjective q
      (QuotientGroup.mk'_surjective _)).resolve_left hL0
    noncentral := ?_
    normal_H := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    irreducible := ?_
    components := Or.inl (congrArg (fun J => (J.subgroupOf P).map q) hHL) }
  · intro hz
    apply s.moved
    have hP : ⁅L.subgroupOf P, X.subgroupOf P⁆ = ⊥ := by
      apply _root_.eq_bot_iff.mpr
      intro x hx
      have hxH : x ∈ H.subgroupOf P :=
        ((commutator_mono (subgroupOf_mono P (le_componentOrbit L ⊤)) le_rfl).trans
          (commutator_le_left (H.subgroupOf P) (X.subgroupOf P))) hx
      have hqx : q x = 1 := by
        have hm : q x ∈ (⁅L.subgroupOf P, X.subgroupOf P⁆).map q := mem_map.mpr ⟨x, hx, rfl⟩
        rw [map_commutator, hz] at hm
        exact hm
      have heH : (⟨x, hxH⟩ : H) = 1 :=
        MarkedAction.projection_injective_on_orbit F.terminalRepresentation H X I
          s.selected.invariant s.actor_stabilizes hfH _ _ (hqx.trans q.map_one.symm)
      exact Subtype.ext (congrArg (fun z : H => (z : F.TerminalHdot)) heH)
    have he := congrArg (Subgroup.map P.subtype) hP
    rw [map_commutator, map_subgroupOf_eq_of_le hLP, map_subgroupOf_eq_of_le hXP,
      Subgroup.map_bot] at he
    exact he
  · apply (irreducible_comp_surjective_iff (q.subgroupMap (H.subgroupOf P))
      (q.subgroupMap_surjective _) _).mp
    change IsIrreducible (σ.comp (H.subgroupOf P).subtype)
    let eH := subgroupOfEquivOfLe hHP
    have hh : σ.comp (H.subgroupOf P).subtype =
        R.toRepresentation.comp eH.toMonoidHom := rfl
    rw [hh]
    exact (irreducible_comp_surjective_iff eH.toMonoidHom eH.surjective
      R.toRepresentation).mpr s.irreducible

variable {k : Type*} [Field k] [Finite k] [CharP k 2]

/-- The binary rank-one row in the two-copy branch has precisely the
field and module dimensions of SL₂(4) on two copies of its natural module. -/
theorem binary_rank_one_parameters_of_double_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* SL(2, k))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2 ^ n) :
    n = 2 ∧ Module.finrank (ZMod 2) I = 4 ∧
      Module.finrank (ZMod 2) (Additive F.Uhat) = 8 := by
  have hc := s.singleOrbit_componentHypothesis_of_double_dimension hk hd hHL
  have he : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes (componentOrbit L ⊤) =
    MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L :=
    congrArg (MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes) hHL
  dsimp only at hc
  rw [he] at hc
  obtain ⟨hm, hcases⟩ := ChapterG.Section09.DefiningCharacteristic.rank_one_module_alternatives
    hc e n hn hcard
  have hi := s.dimension_gt_two
  rcases hcases with ⟨hdeg, _, _⟩ | ⟨a, ha, hna, hdeg, _, _⟩ | ⟨he, hdeg, _, _⟩ <;> omega

/-- A genuine SL₂ isomorphism on the literal constituent image recognizes
the original component as A₅, via the projective-line action. -/
theorem smallComponentImage_of_double_dimension_binary_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* SL(2, k))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2 ^ n) : SmallComponentImage L := by
  have hn2 := (s.binary_rank_one_parameters_of_double_dimension hk hd hHL e n hn hcard).1
  have hk4 : Nat.card k = 4 := by simpa [hn2] using hcard
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hk4
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let eL := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  exact Or.inl ⟨eL.trans (e.trans ((Theory.PSL2.sl2QuotientEquiv k).trans eA))⟩

/-- Apply the binary rank-one recognition to the original source local
lift, retaining its intrinsic two-core quotient. -/
theorem local_lift_of_double_dimension_binary_rank_one
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : Module.finrank (ZMod 2) (Additive F.Uhat) = 2 * Module.finrank (ZMod 2) I)
    (hHL : componentOrbit L ⊤ = L)
    (e : MarkedAction.image F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes L ≃* SL(2, k))
    (n : ℕ) (hn : 2 ≤ n) (hcard : Nat.card k = 2 ^ n) :
    ∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K :=
  s.local_lift_of_image_cases (s.imageCases_of_smallComponentImage
    (s.smallComponentImage_of_double_dimension_binary_rank_one hk hd hHL e n hn hcard))

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
