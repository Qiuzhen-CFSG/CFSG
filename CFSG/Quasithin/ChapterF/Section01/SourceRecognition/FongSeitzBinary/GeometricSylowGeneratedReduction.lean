module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SylowGeneratedReduction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniversalSimpleSocle

/-!
# Sylow generation in the literal finite apartment quotient

Compose the original marking with geometricMarkedIso. Local Sylow normal
generation identifies the entire finite universal quotient with U^Y,
without asserting descent to the original generated carrier or requiring
perfect local factors. The same quotient has perfect two-residual; one
perfect original endpoint makes that residual simple.

All apartment, exchange and root quotient hypotheses remain explicit
inputs of the earlier apartment/exchange producer. Both squares and the
full Borel are those of the original marking. Source: DGS (3.6)–(3.7),
pp.77–80, and Theorem D, p.224; Fong–Seitz I (1A), p.3. No Lie-model
comparison or whole-quotient perfectness is claimed.
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

include h e in
/-- No perfectness premise is needed for the geometric quotient's normal generation. -/
theorem geometric_quotient_normal_generation_of_source
    (split : SplitData (Q).tits) :
    split.unipotentClosure = ⊤ ∧ Group.IsPerfect (pResidual 2 (QuotientGroup α T n)) := by
  let marking := e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline
    hunique hexchange hn hcore roots hB hP hBN)
  exact ⟨MarkedLocal.unipotentClosure_eq_top_of_source Q marking h split,
    MarkedLocal.twoResidual_isPerfect_of_source Q marking h split⟩

include h e in
/-- One perfect original factor gives a simple residual in this very geometric quotient. -/
theorem geometric_quotient_simple_residual_of_perfect_factor
    (split : SplitData (Q).tits) (i : Fin 2) (hp : Group.IsPerfect (L i)) :
    IsSimpleGroup (pResidual 2 (QuotientGroup α T n)) :=
  MarkedLocal.twoResidual_isSimple_of_perfect_factor Q
    (e.trans (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      roots hB hP hBN)) h split i hp

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
