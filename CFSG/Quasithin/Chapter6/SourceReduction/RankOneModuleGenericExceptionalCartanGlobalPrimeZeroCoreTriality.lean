module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowSevenFixed
public import Theory.SpecificGroups.Triality.ArmsParabolicPerfectAtTwo
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
public import Theory.GroupTheory.Amalgam.RankTwo

/-!
# The marked zero-core binary-triality row of original 5.2.2

The original pair is oriented with its solvable endpoint first. In the
binary-triality model this endpoint must be the central parabolic. Its
Borel index is three, so the literal prime actor is cubic. The arms
parabolic is perfect even at the binary field; the selected right factor
therefore equals its whole parabolic and has the actual PSL₂(8) quotient.
Its original right Hall intersection has order seven.

The final application combines this with the existing fixed-lift argument
on the original left quotient. It preserves the distinct field degrees and
proves only S ≤ R; neither S = T nor R = O²(H) is assumed or concluded.
The marking is an explicit parabolic equivalence to the concrete carrier,
not a consequence asserted merely from F.1.1. Its recognition and ultimate
exclusion remain with qt-d-1222-rankone-cartan-local-to-global.

Source: Aschbacher–Smith, 5.2.2, printed pp.647–648, and F.1.12(I)(4),
printed pp.263–264 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]
open Triality.Standard Triality.Standard.Parabolics

/-- The original whole-overlap inclusion amalgam, without any recognition premise. -/
def zeroCoreAmalgam (L H B D R : Subgroup G) :
    RankTwoAmalgam ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) : Subgroup G)
      (Global.sourceS L H ⊔ (B ⊓ R) : Subgroup G)
      (R ⊔ Global.sourceS L H : Subgroup G) :=
  .ofSubgroups _ _ _ (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    (sup_le le_sup_right (inf_le_right.trans le_sup_left))

/-- The concrete binary-triality amalgam with the solvable endpoint first. -/
def binaryTrialityPrimeAmalgam :
    RankTwoAmalgam (parabolic (binaryParameters 1 Nat.zero_lt_one) .central)
      (borel (binaryParameters 1 Nat.zero_lt_one))
      (parabolic (binaryParameters 1 Nat.zero_lt_one) .arms) :=
  .ofSubgroups _ _ _ (borel_le_parabolic _ _) (borel_le_parabolic _ _)

omit [Finite G] in
/-- Solvability excludes the opposite orientation of the actual binary model. -/
theorem LocalData.zeroCore_not_binaryTriality_central_right
    {T : Sylow 2 G} {L H B D R : Subgroup G}
    (d : LocalData T L H B D R) (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ¬ Nonempty ((R ⊔ Global.sourceS L H : Subgroup G) ≃*
      parabolic (binaryParameters 1 Nat.zero_lt_one) .central) := by
  rintro ⟨e⟩
  let := Triality.Standard.BinaryLocalSections.central_parabolic_solvable
  have hs : Group.IsSolvable (R ⊔ Global.sourceS L H : Subgroup G) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact d.right_parabolic_not_solvable hz (d.parabolic_one hz ▸ hs)

/-- A parabolic marking gives the actual cubic actor, selected PSL₂(8) quotient and seven-torus. -/
theorem LocalData.zeroCore_binaryTriality_configuration
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    p = 3 ∧ Global.sourceS L H ≤ R ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧ Nat.card (B ⊓ R : Subgroup G) = 7 := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let S := Global.sourceS L H
  let C := S ⊔ (B ⊓ R)
  let J := (D ⊔ S) ⊔ (B ⊓ R)
  have hs := relIndex_mul_relIndex (⊥ : Subgroup G) C J bot_le
    (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  simp only [relIndex_bot_left] at hs
  change Nat.card C * C.relIndex J = Nat.card J at hs
  rw [d.zeroCore_left_index h hH c hd hz] at hs
  rw [Nat.card_congr e.middle.toEquiv,Nat.card_congr e.left.toEquiv] at hs
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (Carrier P)) (borel P)
    (parabolic P .central) bot_le (borel_le_parabolic P .central)
  simp only [relIndex_bot_left] at hm
  rw [Triality.Standard.OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at hm
  change Nat.card (borel P) * 3 = Nat.card (parabolic P .central) at hm
  have hp : p = 3 := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := borel P)) (hs.trans hm.symm)
  let := parabolic_arms_isPerfect_at_two P rfl rfl
  let : Group.IsPerfect (R ⊔ S : Subgroup G) := Group.IsPerfect.ofSurjective
    (f := e.right.symm.toMonoidHom) e.right.symm.surjective
  have hR := d.zeroCore_right_eq_of_perfect_parabolic h hH c hd hz
  let a : R ≃* localFactor P .arms := (MulEquiv.subgroupCongr hR).trans
    (e.right.trans (MulEquiv.subgroupCongr (parabolic_arms_eq_localFactor_at_two P rfl rfl)))
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  have hr : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 :=
    ⟨ExtensionField P,inferInstance,inferInstance,by rw [card_extensionField]; rfl,
      ⟨aq.trans (localFactorArmsQuotientEquivPSL2 P rfl)⟩⟩
  refine ⟨hp,hR ▸ le_sup_right,hr,?_⟩
  simpa using d.right_cartan_card (m := 3) c hr

/-- The marked zero-core row feeds the original-degree fixed-module calculation. -/
theorem LocalData.zeroCore_binaryTriality_seven_fixed
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    p = 3 ∧ Global.sourceS L H ≤ R ∧
      ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 8 ∧
      Nat.card (B ⊓ R : Subgroup G) = 7 ∧
      ((B ⊓ R : Subgroup G) ≤ centralizer
        (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ↔
        (B ⊓ R : Subgroup G) ≤ omegaCentralizer T) := by
  obtain ⟨hp,hS,hr,hcard⟩ := d.zeroCore_binaryTriality_configuration h hH c hd hz e
  exact ⟨hp,hS,hr,hcard,c.seven_centralizes_omega_span_iff h hn inf_le_left hcard⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
