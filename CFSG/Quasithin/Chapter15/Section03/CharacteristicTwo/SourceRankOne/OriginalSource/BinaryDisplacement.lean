module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource.Small
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.DistanceEightDisplacement
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The remaining binary MS obstruction at the original rank-one source

At the literal component and Sylow subgroup of 15.3.31, the checked weaker
MS conclusion gives the complete source alternatives or an original-core
displacement line. The complete alternatives already contradict the actual
marked small-module consumer. Thus only the displacement line remains: it
is central in the original join, has order two, lies properly in the original
first omega center, and is not characteristic in the original Sylow subgroup.

The full original hypotheses are supplied by the second theorem. Both results
retain the exact whole-fixed-factor equality owned by
`qt-ms93-distance-eight-fixed-factor`. They do not exclude the displacement
line or assert C.1.34. The remaining ambient exclusion stays with
`qt-rank-two-ms93` and the original E assembly. In particular, centrality in
the characteristic replacement is not transported to the original two-core.

Source: Aschbacher–Smith C.1.34 and 15.3.25–31, printed pp.136–137,
1130–1132; Meierfrankenfeld–Stellmacher (1993), Main Theorem (13),
(4.4)–(4.5), and Section 7.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
open ChapterA.Section05To06 RankOneConfiguration SmallExtension SmallExtension.MarkedMS
open ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The actual rank-one small branch forces the nontrivial original displacement
line. Its centrality gives containment in the original first omega center;
its order makes that containment proper. No original-core centrality is assumed. -/
theorem source_binary_displacement_line
    {d : LocalData G} {I : Subgroup G} {c : ComponentWitness d I}
    (s : SourceData KnownSimple.IsKnownSimple d c)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfixed : ∀ t : BinaryMS.MS93.InputSetup ((source_smallMSPair s hm).binaryInput e),
      4 < t.geometry.b t.reduction.radical →
      BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
        centralizer (BinaryMS.MS93.Ltilde t.reduction.radical
          (BinaryMS.MS93.alpha t.reduction.radical) : Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical)) :
    let D := ⁅msQ c.L d.S ⊓ centralizer (c.L : Set G), (c.L ⊔ d.S).pCoreIn 2⁆
    D ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn (c.L ⊔ d.S) ∧ D < d.ZS ∧ Nat.card D = 2 ∧
      ¬ (D.subgroupOf d.S).Characteristic := by
  have hS : Chapter1.IsSylowIn 2 d.S (c.L ⊔ d.S) :=
    s.generated ▸ ⟨s.sylow,s.sylow_eq⟩
  have hcard : Nat.card (omegaCenterIn d.S) = 4 := by
    change Nat.card (centralOmegaIn d.S) = 4
    rw [←s.omega.1]
    exact s.omega.2
  have hms := source_smallMSPair s hm
  rcases hms.binary_source_or_central_displacement e hfixed d.S hS le_rfl with
    ⟨e',hcases⟩ | ⟨hc,hD,hchar⟩
  · have hsurv := linearThree_survivors hS hms.characteristic hcard e' hcases
    let : IsSimpleGroup Matrix.PSL3Two.PSL :=
      Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
    let : IsSimpleGroup Matrix.PSL3Two.SL := Matrix.PSL3Two.equiv.isSimpleGroup
    exact (source_small_false_of_MS_cases s hm (Or.inr (Or.inr ⟨e',hsurv⟩))
      e.isSimpleGroup).elim
  · let D := ⁅msQ c.L d.S ⊓ centralizer (c.L : Set G), (c.L ⊔ d.S).pCoreIn 2⁆
    have hd : Nat.card D = 2 := hD
    let : IsMulCommutative D := (isCyclic_of_prime_card hd).isMulCommutative
    let : IsElementaryAbelian 2 D := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
        rw [←hd]
        exact pow_card_eq_one') }
    have hle : D ≤ d.ZS := by
      rw [s.omega.1]
      exact central_elementary_le_omegaCenter hS hc
    refine ⟨hc,lt_of_le_of_ne hle ?_,hd,hchar⟩
    intro he
    have hh : Nat.card D = 4 := by
      change D = d.ZS at he
      rw [he]
      exact s.omega.2
    omega

/-- Original selection hypotheses instantiate the preceding obstruction at the
same component, quotient marking, join and Sylow subgroup. The only additional
earlier-source premise is the separately owned whole-fixed-factor equality. -/
theorem source_binary_displacement_line_of_original
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    (hshadow : SymmetricThreeShadow d.Yplus d.S)
    {I : Subgroup G} (hI : I ∈ d.HplusMinimal) (hf : HasCharacteristicTwo I)
    (c : ComponentWitness d I)
    (hm : Parabolics.SmallParabolicMarking d I c.L)
    (e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfixed : ∀ hms : SmallMSPair KnownSimple.IsKnownSimple c.L d.S,
      ∀ t : BinaryMS.MS93.InputSetup (hms.binaryInput e),
      4 < t.geometry.b t.reduction.radical →
      BinaryMS.MS93.core t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical) ⊓
        centralizer (BinaryMS.MS93.Ltilde t.reduction.radical
          (BinaryMS.MS93.alpha t.reduction.radical) : Set (FreeAmalgam t.reduction.radical)) =
        BinaryMS.MS93.H t.reduction.radical (BinaryMS.MS93.alpha t.reduction.radical)) :
    let D := ⁅msQ c.L d.S ⊓ centralizer (c.L : Set G), (c.L ⊔ d.S).pCoreIn 2⁆
    D ≤ CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
      (c.L ⊔ d.S) ∧ D < d.ZS ∧ Nat.card D = 2 ∧
      ¬ (D.subgroupOf d.S).Characteristic := by
  obtain ⟨s⟩ := source_smallData hG d hempty hM hu hmany hshadow hI hf c
  exact source_binary_displacement_line s hm e (hfixed (source_smallMSPair s hm))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.SourceRankOne.OriginalSource
