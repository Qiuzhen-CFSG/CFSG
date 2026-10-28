module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SuzukiEnlargement
public import Theory.SpecificGroups.Suzuki.LinearSeparation

/-!
# Commuting critical centers from an original Suzuki endpoint

Transport the original positive-parameter Suzuki quotient through the actual
starred endpoint inclusion and graph conjugation. A noncommuting critical pair
would make every graph actor a projective linear group in characteristic two.
The transported Suzuki actor has order prime to three, whereas every such
linear actor contains an element of order three.

Consequently every critical pair commutes. The original F.1.1 Sylow subgroup
and both endpoint subgroups are retained; no Borel normalization, local
catalogue, center-action data, or recognized parabolic is an additional input.
The commuting source branches are not excluded by this result.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

/-- Every vertex in the marked endpoint orbit retains the actual original
Suzuki quotient, with its original parameter. -/
theorem original_suzuki_graph_quotient (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    (v : Vertex F) (hv : v.type = i) :
    Nonempty ((graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃*
      SuzukiMatrixGroup m) := by
  obtain ⟨g,hg⟩ := (same_orbit_iff F (base F i) v).mpr hv.symm
  let A := graphLocalGroup F (base F i)
  have he : A.map (MulAut.conj g).toMonoidHom = graphLocalGroup F v :=
    (graphLocalGroup_conjugate (reduced_triple h) g (base F i)).symm.trans
      (congrArg (graphLocalGroup F) hg)
  let f : A ≃* graphLocalGroup F v :=
    (A.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr he)
  exact ⟨(QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm.trans
    (reduced_graphSuzukiQuotient h i hm e)⟩

/-- An original positive-parameter Suzuki endpoint rules out all noncommuting
critical pairs, independently of the other original endpoint marking. -/
theorem original_suzuki_critical_centers_commute (h : HypothesisF11 L S) (i : Bool)
    {m : ℕ} (hm : 0 < m)
    (e : (family L i ⧸ pCore 2 (family L i)) ≃* SuzukiMatrixGroup m)
    {v w : Vertex F} (hc : IsCriticalPair F v w) :
    ⁅Z F v,Z F w⁆ = ⊥ := by
  by_contra hne
  obtain ⟨n,hn,K,hK,hfin,hcard,⟨f⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne (base F i)
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  exact not_nonempty_psl2_char_two_equiv_suzuki K hm
    ⟨f.symm.trans (reduced_graphSuzukiQuotient h i hm e)⟩

end CFSG.Quasithin.ChapterF.Source
