module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictMarkedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.NativeRestoration
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearHexagonRecognition

/-!
# The full strict source linear hexagon catalogue

The strict distance-two source constructs the right linear quotient, while
its original left quotient supplies the other field. The seven-path theorem
and source thickness supply the marked finite split quotient of rotation
order six. Its two original field markings then give the complete G₂ or
triality comparison, with both endpoint squares and the whole reduced Borel.

Only the earlier same-Cartan reflections, chosen-apartment exchange and
quotient root signs remain explicit. No equality of endpoint fields, finite
root reflection, source presentation or finite-model comparison is assumed.
Source: DGS, *Groups and Graphs* (1985), (10.10), p.164; (14.1)--(14.2),
pp.210--211; Theorem D, p.224; Fong--Seitz I (6E), pp.43--45.
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

include h hc hne hb hβu hns hlinear c t htfix htmove htsq htnorm hexchange hsign in
/-- The original strict linear-left branch gives the full reduced catalogue,
including equal-field G₂ and unequal-field triality alternatives. -/
theorem strict_linear_hexagon_catalogue :
    Chapter6.Source.RankOneGeneric.Global.ConcreteAmalgamComparison
      (Chapter6.Source.RankOneGeneric.Global.sourceParabolicAmalgam
        L (reducedSylow L S)) := by
  have hval : 3 ≤ Nat.card ((graph (reducedFamily L S)).neighborSet (base (reducedFamily L S) false)) := by
    rw [card_neighbors_of_indices (reducedFamily L S)
      (fun i => (((reducedFamily L S) (!i)).subgroupOf ((reducedFamily L S) i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨v,hv,hvne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph (reducedFamily L S)).neighborSet (base (reducedFamily L S) false))
    (by rw [←Nat.card_coe_set_eq]; omega) (base (reducedFamily L S) true)
  obtain ⟨k,f,fin,ch,alg,c₀,hactor,hk,m,hm,hright,_⟩ :=
    original_core_layers h hc hne hb hβu hv hvne hns
  have hleft := hlinear
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hleft
  obtain ⟨k₁,f₁,fin₁,h₁,⟨e₁⟩⟩ := hright
  let _ := f₀
  let _ := fin₀
  let _ := f₁
  let _ := fin₁
  let _ := Fintype.ofFinite k₀
  let _ := Fintype.ofFinite k₁
  let _ : CharP k₀ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₀)
  let _ : CharP k₁ 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using h₁)
  let j : Iso
      (ofSubgroups (parabolic L (reducedSylow L S) 0)
        (parabolic L (reducedSylow L S) 0 ⊓ parabolic L (reducedSylow L S) 1)
        (parabolic L (reducedSylow L S) 1) inf_le_left inf_le_right) (reducedAmalgam L S) :=
    NativeRestoration.subgroupCongrIso _ _ _ _ rfl
      (lemma_F_1_3_6 (reduced_hypothesis h)) rfl
  exact LinearHexagon.marked_linear_hexagon_catalogue Q (j.trans mark)
    (reduced_hypothesis h) split hrot e₀ e₁

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
