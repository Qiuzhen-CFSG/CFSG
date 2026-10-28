module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FourDimensional
public import Theory.GroupTheory.WreathTwoSubgroups
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.OrthogonalWreath

/-!
# Excluding every solvable original HS action

Both reducible actions and the irreducible solvable action embed in the
binary-plane wreath group. Its abelian two-residual centralizes the actual
dotted L₁, which is two-perfect and normalized by the original Sylow image.
The residual and that Sylow image generate the whole dotted group, proving
normality of dotted L₁. The wreath two-rank bound supplies the order-four
actor bound, so the checked small-center argument lifts this normality to
L₁ in H and gives the contradiction on the original tilded module.

The irreducible solvable branch uses the genuine G.9 orthogonal realization:
the original half-degree bound forces actor rank at least two. The final
consumer retains all original marked action and whole-component data, and
removes the solvable four-dimensional alternative. Its nonsolvable four-space
also has order divisible by five, while the previous A₆/S₆ exclusion remains.

Natural identification of the remaining nonsolvable four-space and the
whole-component recognition are still required for ActionStructure.
Centerlessness remains the explicit preceding premise owned by
qt-d-hs-local-structure. No natural coordinates are assumed here.
Source: Aschbacher--Smith 14.3.23--24 and 14.3.32, pp.1000,1003--1004.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private noncomputable def permWreathEquiv : BinaryFourPlus.Wreath ≃*
    WreathTwoResidual.Actor :=
  RegularWreathProduct.congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm
    (MulEquiv.refl _)

private theorem card_sixteen_of_degree_four (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat]
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4) : Nat.card F.Uhat = 16 := by
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
  change Nat.card F.Uhat = _ at hh
  simpa only [Nat.card_zmod, hd, show (2 : ℕ)^4=16 by decide] using hh

variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
include d earlier hq chosen structural alternatives hne hZ hI

omit [IsElementaryAbelian 2 F.Uhat] in
/-- No faithful four-dimensional source actor embeds in the binary-plane wreath group. -/
theorem source_no_wreath_embedding_of_four
    (hc : Nat.card F.Uhat = 16)
    (f : F.TerminalHdot →* WreathTwoResidual.Actor) (hf : Function.Injective f) : False := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let N := (F.Li L 1).subgroupOf F.H
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hres : F.Li L 1 = (pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype := by
    simp only [Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) from by omega, if_false]
  have hTn : (T : Subgroup G) ≤ normalizer (F.Li L 1 : Set G) := by
    rw [hres]
    exact ((le_inf (h.sylow_normalizes structural)
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
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  exact source_normal_dot_Li_one_exclusion_of_four_two d earlier hq chosen structural alternatives
    F hne hZ hI hc (WreathTwoResidual.rank_le_two_of_injective f hf) g hgP hgH hn

/-- The original nonextraspecial HS action is irreducible under centerlessness. -/
theorem source_terminal_irreducible_of_centerless : IsIrreducible F.terminalRepresentation := by
  by_contra hred
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_, heX, B, v, hyp, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  obtain ⟨f, hf⟩ := hyp.reducible_symmetricThree_pair hred
  let j := permWreathEquiv.toMonoidHom.comp
    ((MonoidHom.ker (RegularWreathProduct.rightHom : BinaryFourPlus.Wreath →* BinaryFourPlus.C2)).subtype.comp
      (BinaryFourPlus.baseEquiv.symm.toMonoidHom.comp f))
  have hj : Function.Injective j := permWreathEquiv.injective.comp
    (Subtype.val_injective.comp (BinaryFourPlus.baseEquiv.symm.injective.comp hf))
  exact source_no_wreath_embedding_of_four d earlier hq chosen structural alternatives F hne hZ hI
    (card_sixteen_of_degree_four F (hyp.reducible_degree_and_solvable hred).1) j hj

omit [IsElementaryAbelian 2 F.Uhat] in
/-- The original nonextraspecial HS dotted group is nonsolvable under centerlessness. -/
theorem source_terminal_not_solvable_of_centerless : ¬ Group.IsSolvable F.TerminalHdot := by
  intro hs
  let := chosen.elementary
  obtain ⟨g, _, hgP, hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU, heX, B, v, hyp, _⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
    F g hne hZ hgP hgH
  obtain ⟨htwo, hphi, hvc⟩ := source_closure d earlier hq chosen structural alternatives F hne
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
    (source_terminal_irreducible_of_centerless d earlier hq chosen structural alternatives F hne hZ hI)
    hX hr hb
  let k := ChapterG.Section09.FittingRecognition.Four.splitOrthogonalEquiv.trans
    (BinaryFourPlus.isometryEquivWreath.trans permWreathEquiv)
  let j := k.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  have hj : Function.Injective j := k.injective.comp (Subtype.val_injective.comp e.injective)
  exact source_no_wreath_embedding_of_four d earlier hq chosen structural alternatives F hne hZ hI
    (card_sixteen_of_degree_four F hfour) j hj

open ChapterG.Section11 ChapterG.Section11.ExchangedRecognition

omit [IsElementaryAbelian 2 F.Uhat] in
/-- Apply the solvable exclusion to the original alternatives, preserving the
whole-component recognition obligation and all literal source markings. -/
theorem source_nonsolvable_four_or_whole_recognition_of_centerless
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
    source_four_or_whole_recognition_of_centerless d earlier hq chosen structural alternatives
      F hne hZ hI g hgP hgH
  let := heU
  let := heX
  have hi := source_terminal_irreducible_of_centerless d earlier hq chosen structural alternatives
    F hne hZ hI
  have hs := source_terminal_not_solvable_of_centerless d earlier hq chosen structural alternatives
    F hne hZ hI
  refine ⟨heU,heX,B,v,hyp,hline,hw,hn,hi,hs,?_⟩
  rcases hcases with ⟨hfour,h360⟩ | hwhole
  · exact .inl ⟨hfour,five_dvd_card_of_nonsolvable_degree_four hyp hs hfour.1,h360⟩
  · exact .inr hwhole

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
