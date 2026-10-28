module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.AlternatingEight
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableOrbitBound
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FourNonsolvable

/-!
# Exhausting the large and nonsolvable centerlessness branches

Apply the genuine earlier marked action reduction to the original flag.
The nontrivial conjugate center excludes A₇, the large-actor recognition
excludes a component pair, and Centerless.AlternatingEight excludes both
A₈ occurrences without a centerlessness premise. The natural G₂ branch
already proves centerlessness. Thus a nontrivial I₂ center forces a
four-dimensional hatted module.

In the reducible case, G.10 embeds the literal actor in S₃ × S₃. Its order
is divisible by eighteen, and the original half-degree bound supplies an
elementary four-group. Hence its order is 36 and the embedding is an
isomorphism. The completed solvable-model Goldschmidt contradiction applies.
Centerless.FourNonsolvable settles every nonsolvable four-space, leaving
only a solvable irreducible four-space in a putative counterexample.

The final two LocalStructure adapters use the literal preceding assembly.
Centerless.Source recognizes the remaining solvable irreducible actor as
S₃ × S₃ and applies the proved solvable branch to assemble source_centerless.
No additional local exclusion callback is introduced as a source input.
Source: Aschbacher--Smith 14.3.23--25,28--31, printed pp.999--1003,
with the corrected G.11 whole-component reduction.
-/

public noncomputable section
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
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives classification hne hZ

/-- The original exhaustive catalogue forces order sixteen unless centerlessness already holds. -/
theorem source_centerless_or_four :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ ∨ Nat.card F.Uhat = 16 := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,hw,hS,hcases⟩ :=
    source_earlier_remaining_action d earlier hq chosen structural alternatives F hne hZ g hgP hgH
  let := heU
  let := heX
  rcases hcases with hcases | ⟨_,hd,_,J,_,_,_,h9,_⟩
  · rcases hcases with h2 | h4 | h5 | h6
    · right
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
      change Nat.card F.Uhat = _ at hh
      simpa only [Nat.card_zmod,h2.1,show (2 : ℕ)^4=16 by decide] using hh
    · exact (source_no_caseFour d earlier hq chosen structural alternatives F hne hZ h4).elim
    · obtain ⟨q,c,J,hJn,hJc,e,he⟩ := SplitSix.caseFive_selfcentralizing_marking h5
      let := hJn
      exact (source_no_alternatingEight_natural d earlier hq chosen structural alternatives
        F hne classification hZ g hgP hgH v hline J e c.toLinearEquiv he).elim
    · exact .inl (source_centerless_of_g2_natural d earlier hq chosen structural alternatives
        F hne classification h6)
  · have hlarge := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
      F g hne hZ hgP hgH
    by_cases he : componentOrbit J ⊤ = J
    · rw [he] at h9
      obtain ⟨_,hc⟩ := LargeWhole.single_small_carrier hyp h9 hw hS hd hlarge
      cases hc with
      | seven e =>
        exact (LargeWhole.not_seven_of_smaller_ne_bot hyp h9 hd
          (map_mono (comap_mono (F.conjugate_ZU_le_X g)))
          (source_earlier_conjugate_center_ne_bot d earlier hq chosen structural alternatives
            F hne hZ g hgP hgH) e.some).elim
      | eight e =>
        let := h9.normal_H
        obtain ⟨e,c,hc⟩ :=
          ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
            h9 (LargeWhole.selfDual hyp)
            (e.some.trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
        exact (source_no_alternatingEight_natural d earlier hq chosen structural alternatives
          F hne classification hZ g hgP hgH v hline J e c hc).elim
      | binary_g2 e =>
        exact .inl (source_centerless_of_g2_natural d earlier hq chosen structural alternatives
          F hne classification (LargeWhole.caseSix_of_binary_g2 hyp h9 hd hlarge e.some))
    · exact (LargeWhole.not_component_pair hyp hw hlarge h9 he).elim

/-- The literal reducible action is S₃ × S₃, so the proved Goldschmidt contradiction applies. -/
theorem source_centerless_of_reducible [IsElementaryAbelian 2 F.Uhat]
    (hred : ¬ IsIrreducible F.terminalRepresentation) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heX
  obtain ⟨f,hf⟩ := hyp.reducible_symmetricThree_pair hred
  obtain ⟨hd,h18⟩ := reducible_order hyp
    (source_earlier_lowRank d earlier hq chosen structural alternatives F hne hZ g hgP hgH v hline) hred
  have hb := source_earlier_dimension_le_twice_actor d earlier hq chosen structural alternatives
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
  exact source_centerless_of_solvable_model d earlier hq chosen structural alternatives F hne
    classification hZ ⟨e⟩

/-- Apply the exhausted large-dimensional branches to the original LocalStructure consumer. -/
theorem localStructure_of_not_four_action (hfour : Nat.card F.Uhat ≠ 16)
    (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    ((source_centerless_or_four d earlier hq chosen structural alternatives classification F hne hZ).resolve_right hfour)
    action

/-- Every remaining counterexample has the original solvable irreducible four-space action. -/
theorem source_contrary_irreducible_solvable_four [IsElementaryAbelian 2 F.Uhat]
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
      IsIrreducible F.terminalRepresentation ∧ Group.IsSolvable F.TerminalHdot := by
  have hc := (source_centerless_or_four d earlier hq chosen structural alternatives classification
    F hne hZ).resolve_left hI
  have hd : finrank (ZMod 2) (Additive F.Uhat) = 4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  refine ⟨hd,?_,?_⟩
  · by_contra hred
    exact hI (source_centerless_of_reducible d earlier hq chosen structural alternatives classification
      F hne hZ hred)
  · by_contra hs
    exact hI (source_centerless_of_nonsolvable_four d earlier hq chosen structural alternatives classification
      F hne hZ hd hs)

/-- Every nonsolvable original hatted action has trivial I₂ center, without a model premise. -/
theorem source_centerless_of_nonsolvable
    (hs : ¬ Group.IsSolvable F.TerminalHdot) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  let := chosen.elementary
  obtain ⟨htwo,hphi,_⟩ := source_closure d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  exact hs (source_contrary_irreducible_solvable_four d earlier hq chosen structural alternatives
    classification F hne hZ hI).2.2

/-- The original LocalStructure application of unrestricted nonsolvable centerlessness. -/
theorem localStructure_of_nonsolvable_action
    (hs : ¬ Group.IsSolvable F.TerminalHdot) (action : ActionStructure F) : LocalStructure L F :=
  localStructure_of_centerless_action d earlier hq chosen structural alternatives F hne
    (source_centerless_of_nonsolvable d earlier hq chosen structural alternatives classification F hne hZ hs)
    action

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
