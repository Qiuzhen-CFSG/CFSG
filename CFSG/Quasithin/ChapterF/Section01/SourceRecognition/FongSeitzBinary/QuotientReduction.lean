module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.SplitCore
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple

/-!
# Reduction and local lifting for the original F.1.1 pair

Work in the actual generated subgroup, preserving both original parabolics
and their full intersection. The existing F.1.9 faithful-triple theorem
supplies Borel faithfulness in any marked finite quotient. Splitness of that
same quotient then gives its actual Sylow two-subgroup, its Borel two-core,
and trivial ambient two-core and center.

Restriction to the generated subgroup followed by the marked quotient maps
constructs an isomorphism on the original inclusion amalgam, with both
commuting squares. A comparison established on the quotient can therefore
be lifted without recognizing the original ambient completion.

Source: DGS, Groups and Graphs, Part II, Theorem D, printed p.224;
Aschbacher–Smith F.1.9 and F.1.11, printed pp.261–262. The actual regular
apartment/quotient and splitness are explicit earlier inputs, owned by
qt-dgs85-apartment-exchange. This module proves reduction and transport;
Fong–Seitz minimality, irreducibility reduction and exhaustive seven-row
recognition remain to be proved by this family. The unconditional DGS and
quasithin assemblies retain discharge of all earlier source premises.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The marked finite quotient of the literal generated source carrier. -/
abbrev SourceQuotient (L : Fin 2 → Subgroup G) (S : Subgroup G) :=
  MarkedQuotient (fun i => (parabolic L S i).subgroupOf (generated L S))

/-- The containment used by each literal endpoint marking in the generated carrier. -/
theorem parabolic_le_generated (i : Fin 2) : parabolic L S i ≤ generated L S := by
  rw [← parabolics_generate L S]
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private def generatedAmalgamIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    (RankTwoAmalgam.ofSubgroups ((parabolic L S 0).subgroupOf (generated L S))
      ((parabolic L S 0).subgroupOf (generated L S) ⊓
        (parabolic L S 1).subgroupOf (generated L S))
      ((parabolic L S 1).subgroupOf (generated L S)) inf_le_left inf_le_right) where
  left := (subgroupOfEquivOfLe (parabolic_le_generated (L := L) (S := S) 0)).symm
  middle := (subgroupOfEquivOfLe
    (inf_le_left.trans (parabolic_le_generated (L := L) (S := S) 0))).symm
  right := (subgroupOfEquivOfLe (parabolic_le_generated (L := L) (S := S) 1)).symm
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- Both original endpoint inclusions lift through the same quotient map. -/
def originalMarkedIso (d : SourceQuotient L S) : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    d.standardAmalgam :=
  generatedAmalgamIso.trans d.markedIso

/-- The original left endpoint uses the quotient of its literal inclusion
in the generated source carrier. -/
@[simp] theorem originalMarkedIso_left_apply (d : SourceQuotient L S)
    (x : parabolic L S 0) :
    ((originalMarkedIso d).left x : (generated L S) ⧸ d.D) =
      d.q ⟨x, parabolic_le_generated 0 x.property⟩ := by
  exact d.markedIso_left_apply _

/-- The entire original intersection uses the same quotient map. -/
@[simp] theorem originalMarkedIso_middle_apply (d : SourceQuotient L S)
    (x : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G)) :
    ((originalMarkedIso d).middle x : (generated L S) ⧸ d.D) =
      d.q ⟨x, parabolic_le_generated 0 x.property.1⟩ := by
  exact d.markedIso_middle_apply _

/-- The original right endpoint uses the same quotient of the generated
source carrier, preserving the second marking. -/
@[simp] theorem originalMarkedIso_right_apply (d : SourceQuotient L S)
    (x : parabolic L S 1) :
    ((originalMarkedIso d).right x : (generated L S) ⧸ d.D) =
      d.q ⟨x, parabolic_le_generated 1 x.property⟩ := by
  exact d.markedIso_right_apply _

/-- F.1.9 discharges Borel faithfulness for the marked source quotient. -/
theorem quotient_borel_core_eq_bot (h : HypothesisF11 L S) (d : SourceQuotient L S) :
    d.tits.B.normalCore = ⊥ := by
  have hs := h.generatedLocallyRankOneTriple
  apply d.borel_core_eq_bot hs.generate
  rw [hs.intersection]
  exact hs.faithful _ inferInstance (normalCore_le _)

/-- The elementary faithful, center-free, two-core-free reduction with
the actual unipotent Sylow retained. This is not the full minimality reduction. -/
theorem quotient_reduction (h : HypothesisF11 L S) (d : SourceQuotient L S)
    (split : SplitData d.tits) :
    d.tits.B.normalCore = ⊥ ∧ pCore 2 ((generated L S) ⧸ d.D) = ⊥ ∧
      center ((generated L S) ⧸ d.D) = ⊥ ∧
      ∃ U : Sylow 2 ((generated L S) ⧸ d.D),
        (U : Subgroup ((generated L S) ⧸ d.D)) = split.U ∧
        normalizer (U : Set ((generated L S) ⧸ d.D)) = d.tits.B ∧
        pCore 2 d.tits.B = split.U.subgroupOf d.tits.B := by
  have hc := quotient_borel_core_eq_bot h d
  exact ⟨hc, split.twoCore_eq_bot, split.center_eq_bot_of_borel_core hc,
    split.sylow, rfl, split.normalizer_eq, split.borel_twoCore⟩

/-- Lift a proved marked quotient comparison to the original source
amalgam, retaining both squares and the given orientation. -/
def originalComparison (d : SourceQuotient L S)
    {A C E : Type*} [Group A] [Group C] [Group E]
    {β : RankTwoAmalgam A C E} (e : RankTwoAmalgam.Iso d.standardAmalgam β) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) β :=
  (originalMarkedIso d).trans e

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
