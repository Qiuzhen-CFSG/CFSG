module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient

/-!
# A simple residual in the literal universal apartment quotient

The original F.1.1 parabolics are finite, but their universal completion
need not be. Apply the local transport theorem to the geometric quotient
and its proved marked amalgam isomorphism. Both original endpoint maps
are the universal embeddings followed by the same geometric quotient map.
No descent from the universal quotient to the actual generated subgroup
is required or asserted. The overlap-core theorem derives universal
faithfulness from F.1.1. In the geometric application the source marking
may be reflexivity on the literal original inclusion amalgam; keeping its
presentation abstract avoids expensive kernel reductions through the
concrete universal-completion type.

Apartment uniqueness/exchange and root/Cartan data remain earlier inputs
from qt-dgs85-apartment-exchange. Splitness refers to this same Tits system;
ApartmentExchange.sourceSplitData supplies it from the earlier Cartan
saturation data. The result removes the simple-power multiplicity in the
both-perfect branch, not the remaining minimal-configuration, root-field
reconstruction or seven marked Lie comparisons.

Source: DGS, Groups and Graphs, Part II, (3.6)–(3.7), pp.77–80,
and Theorem D, p.224; Aschbacher–Smith F.1.1, p.259.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

section Original
variable {G : Type*} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "α" => RankTwoAmalgam.ofSubgroups (parabolic L S 0)
  (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right
private def inclusionCompletion (J A B : Subgroup G) (hAJ : A ≤ J) (hBJ : B ≤ J)
    (hAB : A ⊔ B = J) :
    FaithfulCompletion (RankTwoAmalgam.ofSubgroups A (A ⊓ B) B inf_le_left inf_le_right)
      (G := J) where
  left := inclusion hAJ
  right := inclusion hBJ
  compatible := by ext b; rfl
  left_injective := inclusion_injective hAJ
  right_injective := inclusion_injective hBJ
  middle_injective := (inclusion_injective hAJ).comp (inclusion_injective inf_le_left)
  generated := by
    rw [inclusion_range, inclusion_range, ← subgroupOf_sup hAJ hBJ, hAB, subgroupOf_self]

private def originalGeneratedCompletion : FaithfulCompletion α (G := generated L S) :=
  inclusionCompletion (generated L S) (parabolic L S 0) (parabolic L S 1)
    (parabolic_le_generated 0) (parabolic_le_generated 1) (parabolics_generate L S)

/-- Faithfulness of the whole universal overlap follows from the original
F.1.1 source hypothesis, independently of the apartment or quotient. -/
theorem originalUniversal_overlap_core_eq_bot (h : HypothesisF11 L S) :
    ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥ := by
  let c : FaithfulCompletion α (G := generated L S) := originalGeneratedCompletion
  have hc : c.middle.range.normalCore = ⊥ := by
    change (inclusion (show parabolic L S 0 ⊓ parabolic L S 1 ≤ generated L S from
      inf_le_left.trans (parabolic_le_generated 0))).range.normalCore = ⊥
    rw [inclusion_range]
    have hs := h.generatedLocallyRankOneTriple
    change (((parabolic L S 0).subgroupOf (generated L S) ⊓
      (parabolic L S 1).subgroupOf (generated L S))).normalCore = ⊥
    rw [hs.intersection]
    exact hs.faithful _ inferInstance (normalCore_le _)
  rw [Universal.overlap_eq α (inclusion_injective inf_le_left) (inclusion_injective inf_le_right)]
  exact (Universal.completion α c).middle_normalCore_eq_bot_of_model c hc



end Original

universe u v
variable {G : Type v} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {A C E : Type u} [Group A] [Group C] [Group E] [Finite A] [Finite E]
  (α : RankTwoAmalgam A C E)
  (hL : Function.Injective α.left) (hR : Function.Injective α.right)
  (h : HypothesisF11 L S) (hp : ∀ i, Group.IsPerfect (L i))
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) α)
  (T : Set (SourceVertex α)) (n : ℕ)
  (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
  (hdeg : TwoNeighborsIn (sourceGraph α) T)
  (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
  (hline : NoBranchingIn (sourceGraph α) T)
  (hunique : ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1))
  (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)
  (hn : 1 < n)
  (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
  (roots : RootQuotientData (quotientMap α T n))
  (hB : roots.B = originalMiddle α)
  (hP : ∀ i, roots.endpoint i = Universal.cosetFamily α i)
  (hBN : roots.B.map (quotientMap α T n) ⊓ roots.N.map (quotientMap α T n) =
    (roots.B ⊓ roots.N).map (quotientMap α T n))

include h hp e in
/-- The geometric universal quotient has a simple two-residual. The
source marking can be reflexivity on the original inclusion amalgam. -/
theorem geometric_quotient_twoResidual_isSimple
    (split : SplitData (recognitionQuotient α T n hL hR hbase hdeg htrans hline
      hunique hexchange hn hcore roots hB hP hBN).tits) :
    IsSimpleGroup (pResidual 2 (QuotientGroup α T n)) :=
  MarkedLocal.twoResidual_isSimple
    (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h hp split

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
