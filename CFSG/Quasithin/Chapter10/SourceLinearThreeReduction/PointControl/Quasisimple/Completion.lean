module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Moving
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.Other.FullyMoved

/-!
# Quasisimple exclusion from the original quotient order

The actual moved elementary subgroup is fully moved and has order at least
eight. The small-core-center comparison supplies odd centralizers in J₄,
M₂₄ and the binary-linear carriers without component irreducibility. Along
with the original moved-normalizer restriction in M₂₃ and the native Held,
HS and Rudvalis comparisons, this excludes every containing carrier when
168 divides the original two-core quotient order.

Consequently every binary-three module row is covered, including quiet
Thompson action, fixed kernels and nonsplit extensions. The actual J₁ and
PSL₂(7) quotients are excluded too. The original nonnormal-component
catalogue now leaves only Suzuki and the other odd-prime PSL₂ quotients.
Those comparisons and final source discharge remain with
`qt-d-10-nona5-point-control`.

The last theorem applies this exclusion to all nonidentity moved vectors
in the original point-control consumer. It retains the selection,
half-Sylow and constrained premises of their existing source owners;
it does not assert unconditional point control.
Source: Aschbacher--Smith A.3.12 and 10.2.9, pp.47--48,750--753.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {t v : G} {I : Subgroup G} [IsQuasisimple I] (c : EscapingComponent D t v I)
include D c

/-- The intrinsic divisor suffices on the literal escaping configuration. -/
theorem quasisimple_impossible_of_168
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L)) : False := by
  have h7 : 7 ∣ Nat.card (L ⧸ pCore 2 L) := (by decide : 7 ∣ 168).trans h168
  have h3 : 3 ∣ Nat.card (L ⧸ pCore 2 L) := (by decide : 3 ∣ 168).trans h168
  rcases Other.remaining_binary_or_sporadic D c
      (RankTwo.not_rank_two_of_three D c h3) with ⟨n,hn,hm⟩ | ⟨name,hname,⟨e⟩⟩
  · rcases hn with rfl | rfl
    · exact Other.not_binary_four_of_seven D c h7 hm
    · exact Other.not_binary_five_model_of_fully_moved D c h7 hm
  · rcases hname with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Other.not_mathieuTwentyTwo_of_seven D c h7 e
    · exact Other.not_mathieuTwentyThree_of_fully_moved D c h168 e
    · exact Other.not_mathieuTwentyFour_of_fully_moved D c e
    · exact Other.not_jankoFour_of_fully_moved D c e
    · exact Other.not_higmanSims_of_fully_moved D c h168 e
    · exact Other.not_held_of_fully_moved D c h168 e
    · exact Other.not_rudvalis_of_twentyOne D c ((by decide : 21 ∣ 168).trans h168) e

/-- All original binary-three rows, without any marking of their action. -/
theorem quasisimple_impossible_of_binary_three
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)) : False := by
  apply quasisimple_impossible_of_168 D c
  rw [Nat.card_congr dL.toEquiv,Matrix.PSL3Two.card_SL]

theorem quasisimple_impossible_of_janko_one_quotient
    (dL : (L ⧸ pCore 2 L) ≃* Janko1.Model) : False := by
  apply quasisimple_impossible_of_168 D c
  rw [Nat.card_congr dL.toEquiv,Janko1.card_model]
  decide

theorem quasisimple_impossible_of_prime_seven_quotient
    (hL : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 7) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hL
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact quasisimple_impossible_of_binary_three D c
    ((e.trans (Atlas.fieldEquivPSL 2
      (Atlas.Comparisons.Exceptional.cardSevenFieldEquiv hF))).trans
        Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two)

/-- The remaining original quotients retain actual source model isomorphisms. -/
theorem original_quotient_suzuki_or_prime
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))) :
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty ((L ⧸ pCore 2 L) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ p ≠ 7 ∧
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) := by
  cases Selection.ModuleChoice.component_quotient_model D
      (fun hn => c.t_not_normalizes (hn c.t_mem)) with
  | linear_even n hn he =>
    exact (quasisimple_impossible_of_binary_quotient D c (by omega) he hna).elim
  | suzuki m hm he => exact Or.inl ⟨m,hm,he⟩
  | linear_prime p hp ho he =>
    exact Or.inr ⟨p,hp,ho,fun h =>
      quasisimple_impossible_of_prime_seven_quotient D c (h ▸ he),he⟩
  | janko he => exact (quasisimple_impossible_of_janko_one_quotient D c he.some).elim

end CFSG.Quasithin.Chapter10.PointControl.Quasisimple

namespace CFSG.Quasithin.Chapter10.PointControl
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The divisor branch of the original point-control consumer, with its
quasisimple premise discharged. The three original source producers remain
with their existing owners; this task retains their final discharge. -/
theorem source_nonnormalPointControl_of_168
    (hhalf : HalfSylowUniqueAt T) (hselect : SelectionAt T)
    (hconstrained : ConstrainedExclusionAt T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hL : L ∈ Chapter1.LStar G (T : Subgroup G))
    (hf : ChapterA.Section04.IsFaithfulSignalizerType L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (h168 : 168 ∣ Nat.card (L ⧸ pCore 2 L)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      D.IsMinimalFullModule ∧
      ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal := by
  obtain ⟨D,hD,t,ht,htn,hcross,hpoint⟩ := hselect hmany L hL hf hq hn hna
  have hU := hhalf hmany L D hn hna
  refine ⟨D,hD,?_⟩
  apply source_a5_moved_point_control_of_partner_saturated D hn ht htn
  intro v hv hvne hsM
  by_contra hout
  obtain ⟨I,C⟩ := escapingComponent_of_local_sylow D ht htn hcross hU (hpoint hU)
    hv hvne hsM hout
  by_cases hI : IsQuasisimple I
  · let := hI
    exact Quasisimple.quasisimple_impossible_of_168 D C h168
  · have hvV := partner_le_fullModule D ht hv
    have hCW := (Subgroup.centralizer_le_normalizer _).trans C.moved_normalizer
    exact hconstrained hmany L D hD hna t v I C hI
      (source_a5_point_component_characteristicTwo D hvV hvne (hcross hv) hCW I
        C.le_centralizer C.component hI)
      (source_a5_point_component_reduced_module D hvV hvne (hcross hv) hCW I C.strict.le
        C.le_centralizer C.component C.normalizes hI C.sylow)

end CFSG.Quasithin.Chapter10.PointControl
