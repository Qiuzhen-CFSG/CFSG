module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BTwoStrictPathSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourcePathRoots
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.LinearPathInteriorStars

/-!
# Interior-star fixation for the original strict six-path roots

The original left PSL₂ quotient and the right quotient supplied by the
strict distance-two core calculation provide the two linear endpoint
markings. Characteristic two identifies PSL₂ with SL₂. Hence each actual
path radical fixes every star centered at an interior path vertex.

The final theorem applies this directly to the literal `pathRoots` used
by the strict marked quotient, with no extra core, kernel or local-action
premise. Reflection choices, transitivity and thickness remain the inputs
of that existing root constructor. The whole-Borel quotient sign is a
separate geometric obligation; interior-star fixation alone does not
identify the quotient action with a Borel representative.

Source: DGS, *Groups and Graphs* (1985), (10.10), p.164;
(14.1)--(14.2), pp.210--211.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile OriginalExtension
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "α" => base F false
local notation "β" => base F true

/-- The original strict source hypotheses force every path radical to fix its interior stars. -/
theorem original_bTwo_strict_pathRoot_fixes_interior_stars
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    {a d : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a d) (hp : p.IsPath)
    (x : (reducedAmalgam L S).Universal)
    (hx : x ∈ pathRoot (X := (reducedAmalgam L S).Universal) p) :
    ∀ j, 0 < j → j < p.length →
      ∀ z, (sourceGraph (reducedAmalgam L S)).Adj (p.getVert j) z → x • z = z := by
  have hval : 3 ≤ Nat.card ((graph F).neighborSet α) := by
    rw [card_neighbors_of_indices F
      (fun i => ((F (!i)).subgroupOf (F i)).index) (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) false
  obtain ⟨v,hv,hvne⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet α) (by rw [←Nat.card_coe_set_eq]; omega) β
  obtain ⟨k,f,fin,ch,alg,c,hactor,hk,m,hm,hright,_⟩ :=
    original_core_layers h hc hne hb hβu hv hvne hns
  obtain ⟨k₀,f₀,fin₀,h₀,⟨e₀⟩⟩ := hlinear
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
  let K : Bool → Type := fun i => if i then k₁ else k₀
  let _ : ∀ i, Field (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, Finite (K i) := fun i => by cases i <;> assumption
  let _ : ∀ i, CharP (K i) 2 := fun i => by cases i <;> assumption
  let ePSL : ∀ i : Bool, (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* PSL(2,K i) := by
    intro i
    cases i
    · exact e₀
    · exact e₁
  let eSL (i : Bool) : SL(2,K i) ≃* PSL(2,K i) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (K i))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact linear_pathRoot_fixes_interior_stars h (k := K) (fun i => (ePSL i).trans (eSL i).symm)
    p hp x hx

/-- The literal roots used by the strict marked quotient fix all five interior stars. -/
theorem original_bTwo_strict_roots_fixes_interior_stars
    (h : HypothesisF11 L S) {u : Vertex F}
    (hc : IsCriticalPair F α u) (hne : ⁅Z F α,Z F u⁆ ≠ ⊥)
    (hb : b F = 2) (hβu : (graph F).Adj β u)
    (hns : ¬ Group.IsSolvable (parabolic L S 0))
    {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
    (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i * t i = 1)
    (htnorm : ∀ i, t i ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal))
    (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 7)
    (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
      z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (i : Bool) (x : (reducedAmalgam L S).Universal)
    (hx : x ∈ (pathRoots h c 6 (by decide) t htfix htmove htsq htnorm
      htrans hthick i).root) :
    ∀ j, 0 < j → j < 6 → ∀ z,
      (sourceGraph (reducedAmalgam L S)).Adj
        ((reflectionPath c t htfix htmove htnorm 6 (by decide) i).walk.getVert j) z →
      x • z = z := by
  let p := reflectionPath c t htfix htmove htnorm 6 (by decide) i
  have hx' : x ∈ pathRoot (X := (reducedAmalgam L S).Universal) p.walk := hx
  intro j hj hjl z hz
  exact original_bTwo_strict_pathRoot_fixes_interior_stars h hc hne hb hβu hns hlinear
    p.walk p.isPath x hx' j hj (by rw [p.length_eq]; exact hjl) z hz

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
