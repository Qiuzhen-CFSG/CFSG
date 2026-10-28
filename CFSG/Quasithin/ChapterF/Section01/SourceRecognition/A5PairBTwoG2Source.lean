module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictA5CartanKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorExchangeSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictG2Quotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictRootSigns

/-!
# The actual G₂(4) reduced comparison from the original A5 pair

The original noncommuting distance-two source supplies its Cartan, reflections,
and whole local permutation kernels. The two A5 markings make the Cartan-kernel
part nontrivial on every supported twelve-path, so the strict source proves
apartment exchange. Its raw hexagon geometry then supplies the whole-Borel
root signs. Both original quotient markings over the same field F4 feed the
marked G₂ presentation and produce an isomorphism of the actual reduced amalgam.

No apartment, exchange, signs, model, or classification premise is added.
The full reduced Borel and both original endpoint inclusions are retained.
Source: DGS, Groups and Graphs (1985), (10.10), p.164, (14.1)--(14.9),
pp.210--216, and Theorem D, p.224; Fong--Seitz I (6E), II (9.1)--(9.21).
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open _root_.CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original A5/A5 noncommuting distance-two configuration constructs
the actual reduced G₂(4) amalgam comparison, in its source-selected orientation. -/
theorem HypothesisF11.a5_bTwo_reduced_g2_comparison
    (h : HypothesisF11 L S)
    (a : ∀ i, Nonempty ((L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)))
    {u : Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
    (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) u⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 2)
    (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u) :
    ∃ short : Bool,
      Nonempty (Iso (reducedAmalgam L S) (G2Native.amalgam (GaloisField 2 2) short)) := by
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨e₄⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour
  let μ (i : Fin 2) := (a i).some.trans e₄.symm
  have hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^2) :=
    ⟨GaloisField 2 2,inferInstance,inferInstance,(by simpa using hfour),⟨μ 0⟩⟩
  have hns := h.a5_parabolic_not_solvable 0 (a 0).some
  have hexchange : StrictSourceExchange h hc hne hb hβu hns hlinear :=
    strict_source_exchange_of_cartan_kernels h hc hne hb hβu hns hlinear
    (fun {_ _} p hp hl hT => strict_a5_source_cartan_kernel_ne_bot h a hc hne hb hβu hns hlinear
      p hp hl hT)
  let d := strictSourceReflections h hc hne hb hβu hns hlinear
  have hs := strict_source_root_signs_of_exchange h hc hne hb hβu hns hlinear hexchange
  exact strict_linear_hexagon_comparison h hc hne hb hβu hns hlinear (chosenCartans h)
    d.t d.fixes d.moves d.square d.normalizes hexchange hs (GaloisField 2 2) μ

end CFSG.Quasithin.ChapterF.Source
