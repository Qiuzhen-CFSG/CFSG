module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.A2Source.MarkedRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneOrderSource

/-!
# A₂ recognition of the actual geometric source quotient

The genuine reduced natural actors are transported through the full marked
amalgam into the finite apartment quotient. The source equality m=n and n=3
supply its triangle geometry. The one-field recognition then gives PSL₃,
both full endpoint maps, the entire Borel map and the actual unipotent image.
The reduced Sylow is retained throughout; no descent to an ambient completion
or identification with the original Sylow is assumed. Orders two and four
are included. Earlier natural-action and apartment inputs remain with their
source producers.

Source: DGS, Groups and Graphs, 10.5 and Theorem D, printed pp.156,224;
AS F.1.1--3 and its reduced local configuration.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan.A2SourceRecognition
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))
variable (roots : Bool → LocalRootAction (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)))

variable (hnormalizes : ∀ i, (roots i).reflection ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))

variable (ha : ∀ i, (roots i).a = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (hb : ∀ i, (roots i).b = Subgroup.CosetGeometry.base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)
variable (n : ℕ) (hn : 1 < n)
variable (hodd : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
  p.IsPath → p.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hexchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)
variable (hsign : ∀ i x, x ∈ apartmentGroup c roots →
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
      (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap (reducedAmalgam L S)
    (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S)
        (cartanApartment (reducedAmalgam L S) (apartmentGroup c roots)) n)))

open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Subgroup.CosetGeometry.RankTwo

open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Reduction Matrix.PSL3.RootPresentationRecognition
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
local instance geometricA2FieldAlgebra {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2
variable
  (c₀ : BOneActionData (reducedFamily L S) (CosetGeometry.base (reducedFamily L S) false)
    (CosetGeometry.base (reducedFamily L S) true) k₀ W₀)
  (c₁ : BOneActionData (reducedFamily L S) (CosetGeometry.base (reducedFamily L S) true)
    (CosetGeometry.base (reducedFamily L S) false) k₁ W₁)
  (hactor₀ : c₀.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 0).subgroupOf (G₀ L S))
  (hactor₁ : c₁.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S 1).subgroupOf (G₀ L S))
  (E₀ : W₀ ≃ₗ[ZMod 2] (Fin 2 → k₀)) (E₁ : W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))
  (hc : centerIn c₁.actor = ⊥) (hn3 : n = 3)

local notation "d" => finiteQuotient h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
local notation "mark" => finiteMarkedIso h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
local notation "split" => finiteSplitData h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign

include c₀ c₁ hactor₀ hactor₁ E₀ E₁ hc hn3 in
/-- The genuine reduced actors and n=3 source apartment recognize the SAME
finite quotient, with both full reduced endpoints and its whole Borel marking.
No identification of the reduced Sylow with the original S is made. -/
theorem geometric_recognition :
    ∃ (i : Fin 2) (e : ((reducedAmalgam L S).Universal ⧸ (d).D) ≃* PSL(3,k₁))
      (cmp : RankTwoAmalgam.Iso (reducedAmalgam L S) (flagAmalgam k₁ i)),
      (∀ a, (cmp.left a : PSL(3,k₁)) = e ((mark).left a : (reducedAmalgam L S).Universal ⧸ (d).D)) ∧
      (∀ b, (cmp.middle b : PSL(3,k₁)) = e ((mark).middle b : (reducedAmalgam L S).Universal ⧸ (d).D)) ∧
      (∀ a, (cmp.right a : PSL(3,k₁)) = e ((mark).right a : (reducedAmalgam L S).Universal ⧸ (d).D)) ∧
      (split).U.map e.toMonoidHom = Matrix.PSL3.LinearThree.unipotent k₁ := by
  have hn₀ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₀.actor : Set _) := by
    rw [hactor₀]
    exact reduced_borel_normalizes_source_actor h 0
  have hn₁ : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (c₁.actor : Set _) := by
    rw [hactor₁]
    exact reduced_borel_normalizes_source_actor h 1
  have hd₀ : ∃ (a₀ : BOneActionData (reducedFamily L S) (CosetGeometry.base (reducedFamily L S) false)
      (CosetGeometry.base (reducedFamily L S) true) k₀ W₀)
      (a₁ : BOneActionData (reducedFamily L S) (CosetGeometry.base (reducedFamily L S) true)
        (CosetGeometry.base (reducedFamily L S) false) k₁ W₁),
      (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (a₀.actor : Set _) ∧
      (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer (a₁.actor : Set _) ∧ centerIn a₁.actor = ⊥ :=
    ⟨c₀,c₁,hn₀,hn₁,hc⟩
  have hd : ∃ (a₀ : BOneActionData (fullFamily L (reducedSylow L S))
      (CosetGeometry.base (fullFamily L (reducedSylow L S)) false) (CosetGeometry.base (fullFamily L (reducedSylow L S)) true) k₀ W₀)
      (a₁ : BOneActionData (fullFamily L (reducedSylow L S))
        (CosetGeometry.base (fullFamily L (reducedSylow L S)) true) (CosetGeometry.base (fullFamily L (reducedSylow L S)) false) k₁ W₁),
      (commonBorel L (reducedSylow L S)).subgroupOf (generated L (reducedSylow L S)) ≤ normalizer (a₀.actor : Set _) ∧
      (commonBorel L (reducedSylow L S)).subgroupOf (generated L (reducedSylow L S)) ≤ normalizer (a₁.actor : Set _) ∧
        centerIn a₁.actor = ⊥ := by
    unfold fullFamily
    rw [←G₀_eq_source h]
    have hF : (fun i => (P₀ L S i).subgroupOf (G₀ L S)) =
        (fun i => (parabolic L (reducedSylow L S) i).subgroupOf (G₀ L S)) := by
      funext i
      rw [P₀_eq_source h i]
    rw [←hF]
    simpa only [reducedFamily,B₀_eq_source h] using hd₀
  obtain ⟨a₀,a₁,ha₀,ha₁,hac⟩ := hd
  let hf := reduced_hypothesis h
  let j := FongSeitzBinary.A2Source.intersectionAmalgamIso hf
  let m := j.trans mark
  have hm : RootCoordinates.rotationOrder d = 3 :=
    (finiteQuotient_simple_product_order h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign).trans hn3
  let i := FongSeitzBinary.A2Source.MarkedRecognition.pointIndex d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split
  let e := FongSeitzBinary.A2Source.MarkedRecognition.quotientEquiv d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split
  let cmp := FongSeitzBinary.A2Source.MarkedRecognition.comparison d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split
  refine ⟨i,e,j.symm.trans cmp,?_,?_,?_,?_⟩
  · intro a
    exact FongSeitzBinary.A2Source.MarkedRecognition.comparison_left_apply d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split a
  · intro b
    exact FongSeitzBinary.A2Source.MarkedRecognition.comparison_middle_apply d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split (j.middle.symm b)
  · intro a
    exact FongSeitzBinary.A2Source.MarkedRecognition.comparison_right_apply d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split a
  · exact (FongSeitzBinary.A2Source.MarkedRecognition.subgroup_images d m hf a₀ a₁ ha₀ ha₁ E₀ E₁ hm hac split).1

end ReducedCartan.A2SourceRecognition
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
