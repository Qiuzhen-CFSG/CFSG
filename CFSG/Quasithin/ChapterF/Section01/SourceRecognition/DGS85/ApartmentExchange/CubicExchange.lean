module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.GroupTheory.WeakBNPair.RegularTree.PathBraidExchange

/-!
# The cubic exchange branch on the original universal apartment

For the actual reduced amalgam and its chosen Cartan, odd stabilizer orders
separate each half-path root from the midpoint two-core. The Cartan
factorization reduces an arbitrary actor in the exchange condition to a
nonidentity half-root element. When the source supplies its opposite
involution, order-three relation and apartment-reflection correction in that
two-core times the Cartan, absorb the Cartan factor in the reflection.
The braid calculation then proves exchange or exhibits a nontrivial
common centralizer in the same two-core. A separate source centralizer bound
then gives the full chosen-apartment exchange condition.

This is the rank-one SL₂(2) case of the local calculation in DGS (14.12),
under its explicit path-root and reflection-coset premises. It does not
construct the cubic pairs or prove the needed centralizer bound; those remain
source obligations. The finite quotient, both marked endpoint inclusions and
the whole original middle map are the existing literal constructions, while
the quotient root-sign premise remains explicit.

Source: DGS, *Groups and Graphs* (1985), Part II, (14.12), printed
pp.217--218; (3.6)--(3.7), pp.77--80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

variable (n : ℕ) (hn : 1 < n)
variable (t : Bool → (reducedAmalgam L S).Universal)
variable (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
  base (Universal.cosetFamily (reducedAmalgam L S)) i)
variable (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
  base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
variable (htsq : ∀ i, t i * t i = 1)
variable (htnorm : ∀ i, t i ∈
  Subgroup.normalizer (cartan c : Set (reducedAmalgam L S).Universal))
variable (htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
  (sourceGraph (reducedAmalgam L S)) (n+1))
variable (hthick : ∀ i, ∃ z, (sourceGraph (reducedAmalgam L S)).Adj
  (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
  z ≠ base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
  z ≠ t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i))

variable (hodd : ∀ {a b} (q : (sourceGraph (reducedAmalgam L S)).Walk a b),
  q.IsPath → q.length = n+1 →
    Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) q)))

local notation "ρ" => pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick



variable (hpairs : ∀ {a b : SourceVertex (reducedAmalgam L S)} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=2*n →
  (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) → ∀ x∈pathRoot (X := (reducedAmalgam L S).Universal) (p.drop n), x≠1 →
  ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (p.take n), ∃ u : (reducedAmalgam L S).Universal,
    x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
    (∀ k≤2*n, u • p.getVert k=p.getVert (2*n-k)) ∧
    (x*y*x)*u⁻¹∈(MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert n)).pCoreIn 2 ⊔ cartan c)

include h hn htfix htmove htsq htnorm htrans hthick hodd hpairs in
/-- The local SL₂(2) case of source (14.12), on actual half-path roots and retaining its centralizer alternative. -/
theorem source_cubic_exchange_or_centralizer
    {a b : SourceVertex (reducedAmalgam L S)} (p : (sourceGraph (reducedAmalgam L S)).Walk a b) (hp : p.IsPath) (hl : p.length=2*n)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) (g : (reducedAmalgam L S).Universal)
    (hg : ∀ k, n≤k → k≤2*n → g • p.getVert k=p.getVert k)
    (hmove : g • a≠a) :
    (∃ y : (reducedAmalgam L S).Universal, (∀ k≤n, y • p.getVert k=p.getVert k) ∧ y • (g • a)=b) ∨
      ∃ x∈pathRoot (X := (reducedAmalgam L S).Universal) (p.drop n), ∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (p.take n),
        x*x=1 ∧ y*y=1 ∧ orderOf (x*y)=3 ∧
        ∃ q∈(MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert n)).pCoreIn 2,
          q≠1 ∧ Commute x q ∧ Commute y q := by
  have hfix : cartan c ≤ pathFixer (X := (reducedAmalgam L S).Universal) p := by
    intro k hk j _
    exact reflectionApartment_fixed c t htnorm k hk _ (hT _ (p.getVert_mem_support j))
  have hf := apartment_path_factorization h c n hn t htfix htmove htsq htnorm htrans hthick
    (p.drop n) (by rw [SimpleGraph.Walk.drop_length, hl]; omega)
    (by
      intro z hz
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
      exact hT z (List.mem_of_mem_drop hz))
  have hS := pathRoot_take_inf_vertexCore p hp n (by omega) hodd
    (universal_vertex_core_fixes_neighbors h _ _ (p.adj_getVert_succ (by omega)))
  exact halfFixer_exchange_or_centralizer p n hl (cartan c)
    ((MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert n)).pCoreIn 2) hfix hf hS
    (vertexCore_normalized _) (hpairs p hp hl hT) g hg hmove

variable (hcentral : ∀ {a b : SourceVertex (reducedAmalgam L S)} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=2*n →
  (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) → ∀ x∈pathRoot (X := (reducedAmalgam L S).Universal) (p.drop n),
  ∀ y∈pathRoot (X := (reducedAmalgam L S).Universal) (p.take n), x*x=1 → y*y=1 → orderOf (x*y)=3 →
  ∀ q∈(MulAction.stabilizer (reducedAmalgam L S).Universal (p.getVert n)).pCoreIn 2,
    Commute x q → Commute y q → q=1)

include h hn htfix htmove htsq htnorm htrans hthick hodd hpairs hcentral in
/-- The actual source apartment satisfies exchange once the stated pair centralizers are trivial. -/
theorem source_cubic_exchange : ChosenApartmentExchange (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n := by
  intro a b p hp hl hT g hg hmove
  rcases source_cubic_exchange_or_centralizer h c n hn t htfix htmove htsq htnorm
      htrans hthick hodd hpairs p hp hl hT g hg hmove with he |
      ⟨x,hx,y,hy,hxx,hyy,hxy,q,hq,hqne,hxq,hyq⟩
  · exact he
  · exact (hqne (hcentral p hp hl hT x hx y hy hxx hyy hxy q hq hxq hyq)).elim

variable (hsign : ∀ i x, x∈reflectionGroup c t →
  (∀ r∈((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n)) ∨
  (∀ r∈((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n ((t i*x)⁻¹*r*(t i*x)) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n)))

/-- Literal marked finite quotient in the cubic branch; its geometric exchange premise is proved above. -/
def cubicFiniteQuotient : Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) :=
  pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_cubic_exchange h c n hn t htfix htmove htsq htnorm htrans hthick hodd hpairs hcentral)
    hsign

/-- Both original endpoint inclusion squares and the whole original middle map are retained. -/
def cubicFiniteMarkedIso : RankTwoAmalgam.Iso (reducedAmalgam L S)
    (cubicFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
      hpairs hcentral hsign).standardAmalgam :=
  pathFiniteMarkedIso h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_cubic_exchange h c n hn t htfix htmove htsq htnorm htrans hthick hodd hpairs hcentral)
    hsign

/-- The same constructed quotient has the source two-group/odd abelian splitting and saturation. -/
def cubicFiniteSplitData : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (cubicFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
      hpairs hcentral hsign).tits :=
  pathFiniteSplitData h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_cubic_exchange h c n hn t htfix htmove htsq htnorm htrans hthick hodd hpairs hcentral)
    hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
