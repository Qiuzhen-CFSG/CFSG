module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootLocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GeometricSylowGeneratedReduction

/-!
# The smaller root-generated cover on the actual apartment quotient

The original endpoint marking is composed with the literal geometric
marking. Fong--Seitz (5C)(a) then puts each smaller root group's full panel
kernel in the actual Cartan. With the earlier (2B) containment, this same
group gives the central odd stem cover, with the original kernel formula.
The independent apartment/exchange hypotheses remain explicit; no descent
to the original ambient completion is assumed.

Source: Fong--Seitz I, pp.25--26; DGS (3.6)--(3.7), pp.77--80.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

universe u v
variable {G : Type v} [Group G]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  {A C E : Type u} [Group A] [Group C] [Group E] [Finite A] [Finite E]
  (α : RankTwoAmalgam A C E)
  (hL : Function.Injective α.left) (hR : Function.Injective α.right)
  (h : HypothesisF11 L S)
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

local notation "Q" => recognitionQuotient α T n hL hR hbase hdeg htrans hline
  hunique hexchange hn hcore roots hB hP hBN

local notation "marking" => e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline
  hunique hexchange hn hcore roots hB hP hBN)

include h

/-- The kernel bound is independent of perfectness and of the (2B) containment. -/
theorem geometric_original_root_kernel (split : SplitData (Q).tits) (i : Fin 2) :
    MarkedLocal.originalRankOne Q marking split i ⊓
        MarkedLocal.originalPanelKernel (L := L) (S := S) i ≤
      ((Q).tits.B ⊓ (Q).tits.N).comap (MarkedLocal.endpointMap Q marking i) :=
  MarkedLocal.originalRankOne_inf_kernel_le_cartan Q marking h split i

/-- The smaller cover retains the original panel kernel on this exact geometric carrier. -/
theorem geometric_original_root_cover (split : SplitData (Q).tits) (i : Fin 2)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    (MarkedLocal.originalRootProjection Q marking split i).ker =
      (MarkedLocal.originalPanelKernel (L := L) (S := S) i).subgroupOf
        (MarkedLocal.originalRankOne Q marking split i) ∧
      Function.Surjective (MarkedLocal.originalRootProjection Q marking split i) ∧
      (MarkedLocal.originalRootProjection Q marking split i).ker ≤
        center (MarkedLocal.originalRankOne Q marking split i) ∧
      Nat.Coprime 2 (Nat.card (MarkedLocal.originalRootProjection Q marking split i).ker) ∧
      (MarkedLocal.originalRootProjection Q marking split i).ker ≤
        _root_.commutator (MarkedLocal.originalRankOne Q marking split i) :=
  ⟨MarkedLocal.originalRootProjection_ker Q marking h split i,
    MarkedLocal.original_root_central_odd_cover Q marking split i hV⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
