module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictMarkedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.G2ConstructedReflections

/-!
# Applying the strict apartment quotient to the linear hexagon source

The strict source supplies the finite quotient, marking, split data and
rotation order six. Common-field endpoint markings feed the existing G₂
presentation, whose finite root reflections are constructed from split data. The full reduced Borel and both
endpoint inclusion maps are retained in the resulting marked comparison.

The geometric reflection/exchange/sign premises and the common-field
markings remain with their source producers. The common field selects the
G₂ row; the separate triality possibility is not excluded here. This is their
conditional downstream consumer, not an unconditional classification.
Source: DGS, *Groups and Graphs* (1985), Theorem D, p.224;
Fong--Seitz I (6E)(a), II (9.1)--(9.21).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Atlas.G2.RootPresentationRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2) (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
  (c : CompatibleCartans L (reducedSylow L S))
  (t : Bool → (reducedAmalgam L S).Universal)
  (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i = base (Universal.cosetFamily (reducedAmalgam L S)) i)
  (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
  (htsq : ∀ i, t i * t i = 1)
  (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))

-- Keep dependencies explicit in section-variable types. In particular,
-- notation capturing `L`, `S`, or the roots hides their binder dependencies.
variable
  (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
    (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 6)
  (hsign : ∀ (i : Bool) (x : (reducedAmalgam L S).Universal), x ∈ reflectionGroup c t →
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 (x⁻¹*r*x) ∈ (originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
            (reflectionGroup c t)) 6)) ∨
    (∀ r ∈ (strictPathRoots h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm i).root,
      quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
        (reflectionGroup c t)) 6 ((t i*x)⁻¹*r*(t i*x)) ∈
          (originalMiddle (reducedAmalgam L S)).map
            (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S)
              (reflectionGroup c t)) 6)))

local notation "Q" => strictFiniteQuotient h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign
local notation "split" => strictFiniteSplitData h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign
local notation "mark" => strictFiniteMarkedIso h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign
local notation "hrot" => strictFiniteQuotient_rotation h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign

variable (K : Type*) [Field K] [Finite K] [CharP K 2]
  (μ : ∀ i, (L i ⧸ pCore 2 (L i)) ≃* PSL(2,K))

include h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign μ in
/-- The strict source quotient feeds the actual linear hexagon presentation,
with the same full reduced overlap and both marked endpoint maps. -/
theorem strict_linear_hexagon_comparison :
    ∃ short : Bool, Nonempty (Iso (reducedAmalgam L S) (G2Native.amalgam K short)) := by
  let j : Iso
      (ofSubgroups (parabolic L (reducedSylow L S) 0)
        (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
        (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right) (reducedAmalgam L S) :=
    NativeRestoration.subgroupCongrIso _ _ _ _ rfl
      (lemma_F_1_3_6 (reduced_hypothesis h)) rfl
  obtain ⟨short, e, _⟩ := G2Source.reduced_linear_recognition_of_split
    h Q (j.trans mark) split hrot μ
  exact ⟨short, ⟨e⟩⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
