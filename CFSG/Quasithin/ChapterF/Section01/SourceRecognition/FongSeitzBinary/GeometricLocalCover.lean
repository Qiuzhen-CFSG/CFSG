module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.GeometricSylowGeneratedReduction

/-!
# Fong--Seitz (5B) on the actual finite apartment quotient

Compose the original amalgam marking with the apartment quotient's
geometricMarkedIso. The local cover then uses the original S, the full
original panel kernel and the lifted reflection at either endpoint.
Its central odd kernel lies in the derived subgroup, including when
the local groups are nonperfect. The quotient, apartment, exchange and
splitness inputs remain those of the independent apartment/exchange
producer. No map from this universal quotient to the original ambient
completion or Lie-model comparison is assumed.

Source: Fong--Seitz I (5B), printed p.25; DGS (3.6)--(3.7), pp.77--80,
and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
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

/-- The original-endpoint cover is carried by this very geometric quotient. -/
theorem geometric_original_local_cover (split : SplitData (Q).tits) (i : Fin 2) :
    letI := MarkedLocal.originalRadicalInClosure_normal Q marking h split i
    let E := MarkedLocal.originalLocalClosure Q marking split i ⧸
      MarkedLocal.originalRadicalInClosure Q marking split i
    Function.Surjective (MarkedLocal.originalProjection Q marking h split i) ∧
      (MarkedLocal.originalProjection Q marking h split i).ker ≤ center E ∧
      Nat.Coprime 2 (Nat.card (MarkedLocal.originalProjection Q marking h split i).ker) ∧
      (MarkedLocal.originalProjection Q marking h split i).ker ≤ _root_.commutator E :=
  MarkedLocal.original_central_odd_cover Q marking h split i

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
