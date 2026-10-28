module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Geometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.NormalizerTransport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Projection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import Theory.Representation.BinaryAlternatingFiveBorel.SplitCoordinates
/-!
# The original rank-two plane inside the residual commutator

The marked local geometry gives [V,Lᵥ]=[z,Lᵥ] and order four. Since z belongs
to W_K, its literal binary image is an invariant plane contained in [W_K,Lᵥ].
The proof uses the original conjugation action and constructs the submodule
inside W_K; containment of the whole original V in W_K is unnecessary.
Source: Aschbacher–Smith, local geometry on p.926 and 13.6.15 on p.930.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection SourceContainment SourceContainment.LinearThree
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
theorem source_plane (s : A5Module.Marking L V) (K T : Subgroup G)
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    [IsElementaryAbelian 2 (WK K L T (A5Module.markedZ s) (A5Module.markedV s))] :
    let ρ := (wkRepresentation K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz).comp
      (residualPlusMap K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz)
    ∃ P : Submodule (ZMod 2) (Additive (WK K L T (A5Module.markedZ s) (A5Module.markedV s))),
      Module.finrank (ZMod 2) P=2 ∧ (∀ l w, w ∈ P → ρ l w ∈ P) ∧
      P ≤ subspaceCommutator ρ ⊤ ⊤ := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let W := WK K L T z v
  let D := Lv L v
  let R := ⁅V,D⁆
  let ρ := (wkRepresentation K L T z v hL hz).comp (residualPlusMap K L T z v hL hz)
  have hnW : D ≤ normalizer (W : Set G) :=
    (show D ≤ plusActor K L T v from le_sup_right.trans le_sup_left).trans
      (plusActor_normalizes_WK K L T z v hL hz)
  have hzW : zpowers z ≤ W := (le_conjugateSpanBy _ _).trans (Vv_le_WK K L T z v)
  have hRW : R ≤ W := by
    rw [show R=⁅zpowers z,D⁆ from SourceSmallModels.AlternatingBranches.ExceptionalActors.moved_eq_seed_commutator s]
    exact (commutator_mono hzW le_rfl).trans (le_normalizer_iff_commutator_le_left.mp hnW)
  let P : Submodule (ZMod 2) (Additive W) :=
    AddSubgroup.toZModSubmodule 2 (R.subgroupOf W).toAddSubgroup
  let ep : P ≃ R := {
    toFun w := ⟨w.val.toMul,w.property⟩
    invFun w := ⟨Additive.ofMul ⟨w,hRW w.property⟩,w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hcard : Nat.card P=4 := (Nat.card_congr ep).trans
    (SourceSmallModels.AlternatingBranches.CoveredSix.source_commutator_card s)
  have hdim : Module.finrank (ZMod 2) P=2 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := P)
    rw [hcard,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (by decide : 1<2)) hh.symm
  refine ⟨P,hdim,?_,?_⟩
  · intro l w hw
    have hnorm : (l : G) ∈ normalizer (R : Set G) := normalizer_commutator_ge_right V D l.property
    exact (hnorm w.toMul).mp hw
  · let M := subspaceCommutator ρ ⊤ ⊤
    have hR : R ≤ M.toAddSubgroup.toSubgroup'.map W.subtype := by
      rw [show R=⁅zpowers z,D⁆ from SourceSmallModels.AlternatingBranches.ExceptionalActors.moved_eq_seed_commutator s,commutator_comm]
      apply commutator_le.mpr
      intro l hl w hw
      let w' : Additive W := Additive.ofMul ⟨w,hzW hw⟩
      refine ⟨(ρ ⟨l,hl⟩ w'-w').toMul,?_,?_⟩
      · change ρ ⟨l,hl⟩ w'-w' ∈ M
        exact Submodule.subset_span ⟨⟨l,hl⟩,mem_top _,w',Submodule.mem_top,rfl⟩
      · change (l*w*l⁻¹)/w=⁅l,w⁆
        rw [div_eq_mul_inv]
        rfl
    intro w hw
    obtain ⟨x,hx,he⟩ := hR hw
    exact (show Additive.ofMul x=w from congrArg Additive.ofMul (Subtype.ext he)) ▸ hx
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
