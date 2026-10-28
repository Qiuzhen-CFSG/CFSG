module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Goldschmidt

/-!
# Exhausting the contrary-center alternatives at G,T

The earlier exhaustive action reduction and the proved nonsolvable
exclusions leave a four-dimensional module. The reducible case has the
literal S3 by S3 quotient and is excluded by the Goldschmidt argument.
The remaining nonsolvable four-space rows are excluded on the same
marked action, leaving only a solvable irreducible four-space.
Source: Aschbacher--Smith 14.3.23--25,30--31, pp.999--1003.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/SolvableFour.lean. -/
section
set_option backward.isDefEq.respectTransparency false
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private noncomputable def solvableFour_permWreathEquiv_at : BinaryFourPlus.Wreath ≃*
    WreathTwoResidual.Actor :=
  RegularWreathProduct.congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
    (MulEquiv.refl _)
private theorem solvableFour_card_sixteen_of_degree_four_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat]
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : Nat.card F.Uhat = 16 := by
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  change Nat.card F.Uhat = _ at hh
  simpa only [Nat.card_zmod, hd, show (2 : ℕ)^4=16 by decide] using hh
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_no_wreath_embedding_of_four_at
    (hc : Nat.card F.Uhat = 16)
    (f : F.TerminalHdot →* WreathTwoResidual.Actor) (hf : Function.Injective f) : False := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes_at structural)
      ((F.invariant 1).trans (F.Gi 1).le_normalizer)).trans inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (L ⊓ F.Gi 1) (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)))
  have hLH : F.Li L 1 ≤ F.H := fun x hx => (F.Li_le L 1 hx).2
  have hp : IsPPerfect 2 N := by
    have hh : IsPPerfect 2 (F.Li L 1) := by
      rw [hres]
      exact isPPerfect_embedded_pResidual 2 (L ⊓ F.Gi 1)
    exact hh.of_surjective (subgroupOfEquivOfLe hLH).symm.toMonoidHom
      (subgroupOfEquivOfLe hLH).symm.surjective
  let S := (T.subtype (F.invariant 1)).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hSN : (S : Subgroup F.TerminalHdot) ≤ normalizer (N.map q : Set F.TerminalHdot) := by
    apply le_trans (map_mono (f := q) ?_) (N.le_normalizer_map q)
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    exact (mem_normalizer_iff.mp (hTn ht)) (x : G)
  have hn : (F.terminalDot (F.Li L 1)).Normal :=
    WreathTwoResidual.normal_of_injective_of_twoPerfect f hf S (N.map q)
      (hp.of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N)) hSN
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  exact source_normal_dot_Li_one_exclusion_of_four_two_at d earlier hq chosen structural alternatives
    F hne hZ hI hc (WreathTwoResidual.rank_le_two_of_injective f hf) g hgP hgH hn
theorem source_terminal_irreducible_of_centerless_at : IsIrreducible F.terminalRepresentation := by
  by_contra hred
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  obtain ⟨f, hf⟩ := hyp.reducible_symmetricThree_pair hred
  let j := solvableFour_permWreathEquiv_at.toMonoidHom.comp
    ((MonoidHom.ker (RegularWreathProduct.rightHom : BinaryFourPlus.Wreath →* BinaryFourPlus.C2)).subtype.comp
      (BinaryFourPlus.baseEquiv.symm.toMonoidHom.comp f))
  have hj : Function.Injective j := solvableFour_permWreathEquiv_at.injective.comp
    (Subtype.val_injective.comp (BinaryFourPlus.baseEquiv.symm.injective.comp hf))
  exact source_no_wreath_embedding_of_four_at d earlier hq chosen structural alternatives F hne hZ hI
    (solvableFour_card_sixteen_of_degree_four_at F (hyp.reducible_degree_and_solvable hred).1) j hj
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_terminal_not_solvable_of_centerless_at : ¬ Group.IsSolvable F.TerminalHdot := by
  intro hs
  let := chosen.elementary
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU, heX, B, v, hyp, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hb := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  obtain ⟨htwo, hphi, hvc⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  have hd := (quotient_dimension F htwo hphi hvc).1
  have hr : 2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) := by omega
  have hX : F.terminalDot (F.X g) ≠ ⊥ := by
    intro he
    let : Subsingleton (F.terminalDot (F.X g)) := he ▸ inferInstance
    have hz : finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega
  obtain ⟨_, hfour, H, _, e, c, he⟩ := hyp.orthogonal_case_of_rank_bound
    (CaseOneLarge.source_terminal_cover F d chosen) hs
    (source_terminal_irreducible_of_centerless_at d earlier hq chosen structural alternatives F hne hZ hI)
    hX hr hb
  let k := ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
    (BinaryFourPlus.isometryEquivWreath.trans solvableFour_permWreathEquiv_at)
  let j := k.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  have hj : Function.Injective j := k.injective.comp (Subtype.val_injective.comp e.injective)
  exact source_no_wreath_embedding_of_four_at d earlier hq chosen structural alternatives F hne hZ hI
    (solvableFour_card_sixteen_of_degree_four_at F hfour) j hj
open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_nonsolvable_four_or_whole_recognition_of_centerless_at
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      IsIrreducible F.terminalRepresentation ∧ ¬ Group.IsSolvable F.TerminalHdot ∧
      ((CaseTwo F.terminalRepresentation B ∧ 5 ∣ Nat.card F.TerminalHdot ∧
          ¬ 360 ∣ Nat.card F.TerminalHdot) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ¬ Group.IsSolvable F.TerminalHdot ∧
          ∃ J : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot J ∧
            ⁅J,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧
            ChapterG.Section10.ComponentOrthogonalData F.terminalRepresentation B J ∧
            ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple
              F.terminalRepresentation (F.terminalDot (F.X g)) J (componentOrbit J ⊤)
              (finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∧
            WholeComponentCandidates.Alternatives F.terminalRepresentation J
              (componentOrbit J ⊤))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hn,hcases⟩ :=
    source_four_or_whole_recognition_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
  let := heU
  let := heX
  have hi := source_terminal_irreducible_of_centerless_at d earlier hq chosen structural alternatives
    F hne hZ hI
  have hs := source_terminal_not_solvable_of_centerless_at d earlier hq chosen structural alternatives
    F hne hZ hI
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,hi,hs,?_⟩
  rcases hcases with ⟨hfour,h360⟩ | hwhole
  · exact .inl ⟨hfour,five_dvd_card_of_nonsolvable_degree_four hyp hs hfour.1,h360⟩
  · exact .inr hwhole
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/AlternatingFive.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI
theorem source_four_residual_alternatingFive_at (hc : Nat.card F.Uhat = 16) :
    Nonempty (solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless_at
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact Theory.SpecificGroups.SymmetricSix.residual_equiv_alternatingFive j hj
    (source_terminal_not_solvable_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI) ha
theorem source_four_card_sixty_or_oneTwenty_at (hc : Nat.card F.Uhat = 16) :
    Nat.card F.TerminalHdot = 60 ∨ Nat.card F.TerminalHdot = 120 := by
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless_at
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact Theory.SpecificGroups.SymmetricSix.card_eq_sixty_or_oneTwenty j hj
    (source_terminal_not_solvable_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI) ha
theorem source_four_residual_action_alternatives_at (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) :
    (∃ e : solvableResidual F.TerminalHdot ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (SL2.BinarySmall.natural.comp e.toMonoidHom))) ∨
    (∃ e : solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp e.toMonoidHom))) := by
  have hc : Nat.card F.Uhat = 16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  obtain ⟨_,_,j,hj,_,ha⟩ := source_four_symplectic_embedding_of_centerless_at
    d earlier hq chosen structural alternatives F hne hZ hI hc
  exact ChapterG.Section11.FourResidual.action_alternatives F.terminalRepresentation
    F.terminalRepresentation_injective hd j hj
    (source_terminal_not_solvable_of_centerless_at d earlier hq chosen structural alternatives
      F hne hZ hI) ha
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/NaturalResidual.lean. -/
section
set_option backward.isDefEq.respectTransparency false
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) :=
  ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem naturalResidual_seed_stable_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (a : F.H) (ha : (a:G) ∈ normalizer (V : Set G)) (w : Additive F.Uhat)
    (hw : w ∈ hatSpace F V) :
    F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w ∈ hatSpace F V := by
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction a b, (mem_normalizer_iff.mp ha (b:G)).mp hb, ?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.terminalHatAction a w.toMul
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.uhatAction a w.toMul
  rw [← F.uhatAction_apply_mk,he]
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_no_deleted_five_coordinates_at
    (f : F.TerminalHdot →* Equiv.Perm (Fin 5))
    (hA : alternatingGroup (Fin 5) ≤ f.range)
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ a w, c (F.terminalRepresentation a w) =
      BinaryPermutation.coreRepresentation (Fin 5) (f a) (c w)) : False := by
  let := chosen.elementary
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : ∀ a∈P, ∀ w∈hatSpace F V, F.terminalRepresentation a w∈hatSpace F V := by
    rintro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a∈F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply naturalResidual_seed_stable_at F b _ w hw
    have hTV : (T : Subgroup G)≤normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  have hseed : hatSpace F (F.Vi 2) ≤ hatSpace F V := fun _ hw =>
    (show hatImage F (F.Vi 2)≤hatImage F V from map_mono (comap_mono (F.le_seed 2))) hw
  have hv : v∈hatSpace F V := hseed (hline ▸ Submodule.mem_span_singleton_self v)
  obtain ⟨k,hk,hm⟩ := source_seed_point_moved_at d earlier hq chosen F hne v hline
  apply hm
  apply BinaryPermutation.AlternatingFiveFlag.PlaneFixer.point_fixed_of_coordinates
    F.terminalRepresentation f hA c he P (hatSpace F V)
    (seed_hat_dimension F (source_closure_at d earlier hq chosen structural alternatives F hne).2.2)
    hs v hv (fun a ha => hfix a (hP ▸ ha)) k
  intro w hw
  obtain ⟨b,hb,rfl⟩ := hk
  exact naturalResidual_seed_stable_at F b (chosen.normalizes (F.Li_le L 1 hb).1) w hw
theorem source_four_residual_not_deleted_at
    (e : solvableResidual F.TerminalHdot ≃* alternatingGroup (Fin 5))
    (E : Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
      (OrthogonalFourMinus.AlternatingFive.alternatingRepresentation.comp e.toMonoidHom)) :
    False := by
  obtain ⟨f,_,hf,hm⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation
    F.terminalRepresentation (solvableResidual F.TerminalHdot) e E.toLinearEquiv
    (fun a w => IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w) F.terminalRepresentation_injective
  have hA : alternatingGroup (Fin 5)≤f.range := by
    intro a ha
    obtain ⟨k,hk⟩ := e.surjective ⟨a,ha⟩
    exact ⟨k.val,(hm k).trans (congrArg Subtype.val hk)⟩
  let C := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let c := E.toLinearEquiv.trans C.symm
  apply source_no_deleted_five_coordinates_at d earlier hq chosen structural alternatives F hne f hA c
  intro a w
  apply C.injective
  change C (C.symm (E (F.terminalRepresentation a w))) =
    C (BinaryPermutation.coreRepresentation (Fin 5) (f a) (C.symm (E w)))
  rw [C.apply_symm_apply]
  change E.toLinearEquiv (F.terminalRepresentation a w) =
    C (BinaryPermutation.coreRepresentation (Fin 5) (f a) (C.symm (E.toLinearEquiv w)))
  rw [hf,BinaryPermutation.coreEquivNatural_equivariant,C.apply_symm_apply]
theorem source_four_residual_natural_at
    (hZ : F.ZU ≠ F.Vi 1) (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (hd : finrank (ZMod 2) (Additive F.Uhat)=4) :
    ∃ e : solvableResidual F.TerminalHdot ≃* SL(2,OrthogonalFourMinus.FiniteModel.Field 1),
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype)
        (SL2.BinarySmall.natural.comp e.toMonoidHom)) := by
  rcases source_four_residual_action_alternatives_at d earlier hq chosen structural alternatives
    F hne hZ hI hd with hn | ⟨e,⟨E⟩⟩
  · exact hn
  · exact (source_four_residual_not_deleted_at d earlier hq chosen structural alternatives F hne e E).elim
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/FourNonsolvable.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
local instance hsCenterlessFourNaturalAlgebra_at :
    Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private def fourNonsolvable_concreteCoordinates_at : SL2FourNatural.V ≃ₗ[ZMod 2]
    (Fin 2 → OrthogonalFourMinus.FiniteModel.Field 1) where
  toFun v i := SL2FourNatural.fieldEquiv (v i)
  invFun v i := SL2FourNatural.fieldEquiv.symm (v i)
  left_inv v := by funext i; exact SL2FourNatural.fieldEquiv.symm_apply_apply _
  right_inv v := by funext i; exact SL2FourNatural.fieldEquiv.apply_symm_apply _
  map_add' v w := by funext i; exact map_add SL2FourNatural.fieldEquiv _ _
  map_smul' c v := by funext i; exact ZMod.map_smul SL2FourNatural.fieldEquiv c (v i)
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives hne hZ
omit hZ in
private theorem fourNonsolvable_original_five_coordinates_at
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) (ha : ¬ alternatingGroup (Fin 6) ≤ j.range) :
    ∃ (e : solvableResidual F.TerminalHdot ≃* SL2FourNatural.SL)
      (c : Additive F.Uhat ≃ₗ[ZMod 2] SL2FourNatural.V),
      ∀ a w, c (F.terminalRepresentation a.val w)=SL2FourNatural.action (e a) (c w) := by
  rcases FourResidual.action_alternatives F.terminalRepresentation F.terminalRepresentation_injective
    hd j hj hs ha with ⟨e,⟨E⟩⟩ | ⟨e,⟨E⟩⟩
  · let e' := e.trans SL2FourNatural.standardGroupEquiv.symm
    let c := E.toLinearEquiv.trans fourNonsolvable_concreteCoordinates_at.symm
    refine ⟨e',c,?_⟩
    intro a w
    have hi := IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap a w
    change E (F.terminalRepresentation a.val w) = specialLinearNatural 2 (e a) (E w) at hi
    apply fourNonsolvable_concreteCoordinates_at.injective
    change fourNonsolvable_concreteCoordinates_at (fourNonsolvable_concreteCoordinates_at.symm (E (F.terminalRepresentation a.val w))) =
      fourNonsolvable_concreteCoordinates_at (SL2FourNatural.action (e' a) (c w))
    rw [fourNonsolvable_concreteCoordinates_at.apply_symm_apply]
    change _ = SL2FourNatural.standardVectorEquiv (SL2FourNatural.action (e' a) (c w))
    rw [SL2FourNatural.standard_equivariant]
    change _ = specialLinearNatural 2 (SL2FourNatural.standardGroupEquiv
      (SL2FourNatural.standardGroupEquiv.symm (e a)))
      (fourNonsolvable_concreteCoordinates_at (fourNonsolvable_concreteCoordinates_at.symm (E w)))
    rw [SL2FourNatural.standardGroupEquiv.apply_symm_apply,fourNonsolvable_concreteCoordinates_at.apply_symm_apply]
    exact hi
  · exact (source_four_residual_not_deleted_at d earlier hq chosen structural alternatives F hne e E).elim
private theorem fourNonsolvable_original_symmetricFive_model_at
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) (ha : ¬ alternatingGroup (Fin 6) ≤ j.range) :
    Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨e,c,he⟩ := fourNonsolvable_original_five_coordinates_at d earlier hq chosen structural alternatives F hne hd j hj hs ha
  have hc : Nat.card F.TerminalHdot = 120 := by
    rcases Theory.SpecificGroups.SymmetricSix.card_eq_sixty_or_oneTwenty j hj hs ha with h60 | h120
    · obtain ⟨eA⟩ := Theory.SpecificGroups.SymmetricSix.residual_equiv_alternatingFive j hj hs ha
      have hR : solvableResidual F.TerminalHdot = ⊤ := by
        apply eq_of_le_of_card_ge le_top
        rw [card_top,h60,Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
        norm_num [Nat.factorial]
      let R := solvableResidual F.TerminalHdot
      let eR : R ≃* F.TerminalHdot := MulEquiv.ofBijective R.subtype
        ⟨Subtype.val_injective, fun a => ⟨⟨a,by change a ∈ solvableResidual F.TerminalHdot; rw [hR]; exact mem_top a⟩,rfl⟩⟩
      have heR (a : F.TerminalHdot) : (eR.symm a).val=a := eR.apply_symm_apply a
      let e' := eR.symm.trans e
      have he' (a : F.TerminalHdot) (w : Additive F.Uhat) :
          c (F.terminalRepresentation a w)=SL2FourNatural.action (e' a) (c w) := by
        simpa only [e',MulEquiv.trans_apply,heR] using he (eR.symm a) w
      obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
      obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
        d earlier hq chosen structural alternatives hne g hgP hgH
      let := heX
      have hb := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
        F g hne hZ hgP hgH
      have hX : 4 ≤ Nat.card (F.terminalDot (F.X g)) := by
        have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := Additive (F.terminalDot (F.X g)))
        change Nat.card (F.terminalDot (F.X g)) = _ at hh
        rw [hh,Nat.card_zmod]
        exact Nat.pow_le_pow_right (by decide : 0<2)
          (by omega : 2≤finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
      obtain ⟨_,_,hW,_⟩ := source_four_marked_geometry_at d earlier hq chosen structural alternatives
        F hne hd g hgP hgH
      exact (FourNatural.not_special_linear hyp hW hX e' c he').elim
    · exact h120
  obtain ⟨E,C,hE⟩ := SL2FourNatural.SemilinearNormalizer.coordinates_of_order_oneTwenty
    F.terminalRepresentation F.terminalRepresentation_injective hc
    (solvableResidual F.TerminalHdot) e c he
  exact ⟨E.trans SL2FourNatural.SemilinearNormalizer.symmetricFiveEquiv⟩
omit [Finite G] d earlier hq chosen structural alternatives [IsElementaryAbelian 2 F.Uhat] hne hZ in
private theorem fourNonsolvable_model_of_alternatingSix_le_at {D : Type*} [Group D] [Finite D]
    (j : D →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (ha : alternatingGroup (Fin 6) ≤ j.range) :
    Nonempty (D ≃* alternatingGroup (Fin 6)) ∨ Nonempty (D ≃* Equiv.Perm (Fin 6)) := by
  have hD : j.range.index ∣ 2 := by
    simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le ha
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hD with hi | hi
  · right
    exact ⟨(MonoidHom.ofInjective hj).trans
      ((MulEquiv.subgroupCongr (index_eq_one.mp hi)).trans Subgroup.topEquiv)⟩
  · left
    have he : alternatingGroup (Fin 6) = j.range := by
      apply eq_of_le_of_card_ge ha
      have hh := j.range.card_mul_index
      rw [hi,Nat.card_perm,Nat.card_fin] at hh
      norm_num [Nat.factorial] at hh
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
      omega
    exact ⟨(MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr he.symm)⟩
include classification in
theorem source_centerless_of_nonsolvable_four_at
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (hs : ¬ Group.IsSolvable F.TerminalHdot) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  obtain ⟨c,j,hj,he⟩ := exists_binarySymplecticFour_embedding F.terminalRepresentation
    hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  let j' := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  have hj' : Function.Injective j' :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj
  have hc : Nat.card F.Uhat = 16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    simpa only [Nat.card_zmod,hd,show (2 : ℕ)^4=16 by decide] using hh
  apply source_centerless_of_four_nonsolvable_model_at d earlier hq chosen structural alternatives
    F hne classification hZ hc
  by_cases ha : alternatingGroup (Fin 6) ≤ j'.range
  · exact .inr (fourNonsolvable_model_of_alternatingSix_le_at j' hj' ha)
  · exact .inl (fourNonsolvable_original_symmetricFive_model_at d earlier hq chosen structural alternatives F hne hZ hd j' hj' hs ha)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Exhaustion.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives classification hne hZ
theorem source_centerless_or_four_at :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ ∨ Nat.card F.Uhat = 16 := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hS,hcases⟩ :=
    source_earlier_remaining_action_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := heU
  let := heX
  rcases hcases with hcases | ⟨_,hd,_,J,_,_,_,h9,_⟩
  · rcases hcases with h2 | h4 | h5 | h6
    · right
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
      change Nat.card F.Uhat = _ at hh
      simpa only [Nat.card_zmod,h2.1,show (2 : ℕ)^4=16 by decide] using hh
    · exact (source_no_caseFour_at d earlier hq chosen structural alternatives F hne hZ h4).elim
    · obtain ⟨q,c,J,hJn,hJc,e,he⟩ := SplitSix.caseFive_selfcentralizing_marking h5
      let := hJn
      exact (source_no_alternatingEight_natural_at d earlier hq chosen structural alternatives
        F hne classification hZ g hgP hgH v hline J e c.toLinearEquiv he).elim
    · exact .inl (source_centerless_of_g2_natural_at d earlier hq chosen structural alternatives
        F hne classification h6)
  · have hlarge := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
      F g hne hZ hgP hgH
    by_cases he : componentOrbit J ⊤ = J
    · rw [he] at h9
      obtain ⟨_,hc⟩ := LargeWhole.single_small_carrier hyp h9 hw hS hd hlarge
      cases hc with
      | seven e =>
        exact (LargeWhole.not_seven_of_smaller_ne_bot hyp h9 hd
          (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
          (source_earlier_conjugate_center_ne_bot_at d earlier hq chosen structural alternatives
            F hne hZ g hgP hgH) e.some).elim
      | eight e =>
        let := h9.normal_H
        obtain ⟨e,c,hc⟩ :=
          ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
            h9 (LargeWhole.selfDual hyp)
            (e.some.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
        exact (source_no_alternatingEight_natural_at d earlier hq chosen structural alternatives
          F hne classification hZ g hgP hgH v hline J e c hc).elim
      | binary_g2 e =>
        exact .inl (source_centerless_of_g2_natural_at d earlier hq chosen structural alternatives
          F hne classification (LargeWhole.caseSix_of_binary_g2 hyp h9 hd hlarge e.some))
    · exact (LargeWhole.not_component_pair hyp hw hlarge h9 he).elim
theorem source_centerless_of_reducible_at [IsElementaryAbelian 2 F.Uhat]
    (hred : ¬ IsIrreducible F.terminalRepresentation) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  obtain ⟨f,hf⟩ := hyp.reducible_symmetricThree_pair hred
  obtain ⟨hd,h18⟩ := reducible_order hyp
    (source_earlier_lowRank_at d earlier hq chosen structural alternatives F hne hZ g hgP hgH v hline) hred
  have hb := source_earlier_dimension_le_twice_actor_at d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  have hx : 4 ∣ Nat.card (F.terminalDot (F.X g)) := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := Additive (F.terminalDot (F.X g)))
    change Nat.card (F.terminalDot (F.X g)) = _ at hh
    rw [hh,Nat.card_zmod]
    exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g))))
  have h4 := hx.trans (F.terminalDot (F.X g)).card_subgroup_dvd_card
  have hp : Nat.card (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) = 36 := by
    simp only [Nat.card_prod,Nat.card_perm,Nat.card_fin]
    decide
  have hdiv : Nat.card F.TerminalHdot ∣ 36 := hp ▸ card_dvd_of_injective f hf
  have h36 : 36 ∣ Nat.card F.TerminalHdot := by omega
  have hc : Nat.card F.TerminalHdot = 36 := Nat.dvd_antisymm hdiv h36
  let e := MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by rw [hc,hp]))
  exact source_centerless_of_solvable_model_at d earlier hq chosen structural alternatives F hne
    classification hZ ⟨e⟩
theorem source_contrary_irreducible_solvable_four_at [IsElementaryAbelian 2 F.Uhat]
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      IsIrreducible F.terminalRepresentation ∧ Group.IsSolvable F.TerminalHdot := by
  have hc := (source_centerless_or_four_at d earlier hq chosen structural alternatives classification
    F hne hZ).resolve_left hI
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  refine ⟨hd,?_,?_⟩
  · by_contra hred
    exact hI (source_centerless_of_reducible_at d earlier hq chosen structural alternatives classification
      F hne hZ hred)
  · by_contra hs
    exact hI (source_centerless_of_nonsolvable_four_at d earlier hq chosen structural alternatives classification
      F hne hZ hd hs)
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
