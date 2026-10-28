module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.SmallSuzukiEnlargement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.IntrinsicNoncommutingCatalogue
public import Theory.SpecificGroups.Suzuki.LinearSeparation

/-!
# Commuting critical pairs at a small solvable endpoint

A noncommuting critical pair forces every enlarged actor quotient to be
PSL₂ over a finite field of characteristic two. Such a quotient has order
divisible by three. An original D₁₀ marking enlarges only to D₁₀ or Sz(2),
and an original Sz(2) marking preserves that quotient; their orders are ten
and twenty. The resulting contradiction eliminates the noncommuting branch
without choosing the orientation or either critical endpoint.

The literal marked-five S₃ and wreath mixed pairs in Chapter 15 consume this
reduction. Commuting recognition remains a separate source argument.
Source: DGS, *Groups and Graphs* (1985), Chapters 7 and 10--11;
Aschbacher--Smith F.1.9--12 and 15.2.4--8, printed pp.261--264,1106--1110.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S

set_option backward.isDefEq.respectTransparency false in
/-- An original D₁₀ or Sz(2) endpoint excludes every noncommuting critical pair. -/
theorem reduced_critical_commuting_of_small_solvable (h : HypothesisF11 L S) (j : Bool)
    (hm : Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* DihedralGroup 5) ∨
      Nonempty ((family L j ⧸ pCore 2 (family L j)) ≃* SuzukiMatrixGroup 0))
    {v w : Vertex F} (hc : IsCriticalPair F v w) : ⁅Z F v,Z F w⁆ = ⊥ := by
  by_contra hne
  obtain ⟨n,hn,K,hK,hfin,hcard,⟨eK⟩⟩ :=
    reduced_noncommuting_actor_quotients_linear h hc hne (base F j)
  let := hK
  let := hfin
  let := Fintype.ofFinite K
  let := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  have hd : 3 ∣ Nat.card
      (graphLocalGroup F (base F j) ⧸ pCore 2 (graphLocalGroup F (base F j))) := by
    have hce : Nat.card
        (graphLocalGroup F (base F j) ⧸ pCore 2 (graphLocalGroup F (base F j))) =
        Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := Nat.card_congr eK.toEquiv
    rw [hce]
    exact three_dvd_card_psl2_char_two K
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    rcases reduced_graph_dihedral_alternatives h j e with hm | hm
    · obtain ⟨_,⟨f⟩⟩ := hm
      rw [Nat.card_congr f.toEquiv,DihedralGroup.nat_card] at hd
      norm_num at hd
    · obtain ⟨f⟩ := hm
      rw [Nat.card_congr f.toEquiv,suzukiZero_card] at hd
      norm_num at hd
  · obtain ⟨e⟩ := hm
    rw [Nat.card_congr (reduced_graphSuzukiQuotient_all h j 0 e).toEquiv,
      suzukiZero_card] at hd
    norm_num at hd

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
