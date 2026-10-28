module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter

/-!
# The b=1 alternatives on the actual apartment quotient

The earlier apartment, path-transitivity, odd-stabilizer and root-sign
hypotheses construct the finite marked quotient and its split data. Apply
the natural-profile comparison to that same quotient. Its proved Weyl
parameter equality identifies the actual apartment parameter as three or
four and gives the corresponding full reduced PSL₃ or Sp₄ amalgam.

No quotient, split structure, rotation choice, actor-center hypothesis or
model comparison is an extra input to this geometric specialization. Both
endpoint squares and the whole reduced Borel remain part of each Iso.
The actual natural actions and genuine apartment hypotheses still require
the earlier source producers; this does not assert full DGS exhaustiveness.

Source: DGS, Groups and Graphs (1985), (3.6)--(3.7), (10.5) and Theorem D,
printed pp.77--80,156--157,224.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan.BOneSourceRecognition
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

open CFSG.Quasithin.ChapterF.Source.DGS85.Assembly
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
variable {k₀ k₁ W₀ W₁ : Type*} [Field k₀] [Finite k₀] [CharP k₀ 2]
  [Field k₁] [Finite k₁] [CharP k₁ 2]
  [AddCommGroup W₀] [Module (ZMod 2) W₀] [AddCommGroup W₁] [Module (ZMod 2) W₁]
variable (p : C2Source.Profile L S k₀ k₁ W₀ W₁)
  (E₁ : letI : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
    W₁ ≃ₗ[ZMod 2] (Fin 2 → k₁))

include h c roots hnormalizes ha hb hinv hn hodd htrans hexchange hsign p E₁ in
/-- Construct the quotient and select the complete b=1 model from the source apartment. -/
theorem geometric_reduced_comparison :
    (n = 3 ∧ ∃ point : Bool,
      Nonempty (Iso (reducedAmalgam L S) (LinearNative.amalgam k₁ point))) ∨
    (n = 4 ∧ ∃ point : Bool,
      Nonempty (Iso (reducedAmalgam L S) (SymplecticNative.amalgam k₀ point))) := by
  have hm := finiteQuotient_simple_product_order h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign
  have he := BOneSource.reduced_comparison h p E₁
    (finiteQuotient h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign)
    (finiteMarkedIso h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign)
    (finiteSplitData h c roots hnormalizes ha hb hinv n hn hodd htrans hexchange hsign)
  rcases he with ⟨hrot,hiso⟩ | ⟨hrot,hiso⟩
  · exact Or.inl ⟨hm.symm.trans hrot,hiso⟩
  · exact Or.inr ⟨hm.symm.trans hrot,hiso⟩

end ReducedCartan.BOneSourceRecognition
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
