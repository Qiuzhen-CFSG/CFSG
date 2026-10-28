module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootGeneratedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniversalSimpleSocle

/-!
# The whole universal geometric quotient on the perfect branch

The same finite quotient of the universal completion is now perfect and
simple, using the proved ordered-root theorem to discharge generation of U.
Transport both original factors through the supplied amalgam marking and
geometricMarkedIso, retaining the full overlap and both endpoint squares.
The possibly infinite numerator need not descend to the actual source group.

Apartment uniqueness, exchange, the root quotient datum, actual Cartan
intersection, splitness and perfectness of both original factors remain
explicit earlier inputs. No Lie-model classification is concluded.
Source: DGS, Groups and Graphs, Part II, (3.6)–(3.7), pp.77–81 and
Theorem D, p.224; Aschbacher–Smith F.1.1, p.259.
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

local notation "Q" => recognitionQuotient α T n hL hR hbase hdeg htrans hline
  hunique hexchange hn hcore roots hB hP hBN

include h hp e in
/-- The whole geometric quotient is perfect, with root generation discharged. -/
theorem geometric_quotient_isPerfect (split : SplitData (Q).tits) :
    Group.IsPerfect (QuotientGroup α T n) :=
  MarkedLocal.quotient_isPerfect Q
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h hp split

include h hp e in
/-- The whole geometric quotient is simple, with root generation discharged. -/
theorem geometric_quotient_isSimple (split : SplitData (Q).tits) :
    IsSimpleGroup (QuotientGroup α T n) :=
  MarkedLocal.quotient_isSimple Q
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h hp split

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
