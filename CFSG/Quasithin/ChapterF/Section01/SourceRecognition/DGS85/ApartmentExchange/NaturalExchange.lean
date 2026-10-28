module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PathFactorization
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalPathExchange

/-!
# Natural-module exchange on the original universal apartment

Use natural SL₂ coordinates on the actual midpoint local subgroup and its
original two-core. Opposite root matrices construct cubic pairs upstairs:
their cube lies in the two-core and is fixed by their fixed-point-free cubic
image, so it is trivial. The same calculation kills their common centralizer.
The matrix braid differs from the marked reflection by a Cartan element
modulo that same core. The path calculation then proves exchange for every
half-path fixer, using the original Cartan factorization. Two constructed
paths suffice: apartment alignment transports their exchange actors to all
other paths, with both original vertex orbits retained.

This supplies the characteristic-two natural-module step of DGS (14.13),
conditional on the preceding local profiles and their
root/Cartan coordinate markings and chosen local reflections. Those markings, reflection
selection, the other Chapter 14 alternatives and quotient root signs remain
source obligations. No full (14.19) or finite recognition result is asserted.
Both original endpoint maps and the whole middle map are retained in the
literal finite quotient application.

Source: DGS, *Groups and Graphs* (1985), (14.12)--(14.13), pp.217--218,
and (3.6)--(3.7), pp.77--80.
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
universe uF
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


/-- A constructed length-2n apartment path starting at each of the two
original marked endpoints. -/
def exchangePath (i : Bool) :=
  (reflectionPath c t htfix htmove htnorm (2*n)
    (Nat.mul_pos (by decide) (lt_trans Nat.zero_lt_one hn)) i).walk.reverse

variable (htwo : ∀ i : Bool, Nonempty (NaturalPathCoordinates.{uF}
  (exchangePath c n hn t htfix htmove htnorm i) n (cartan c)))

include h hn htfix htmove htsq htnorm htrans hthick hodd htwo in
/-- Two actual local coordinate profiles suffice: the apartment normalizer
aligns all other paths, and conjugation transports their exchange actors. -/
theorem source_natural_exchange : ChosenApartmentExchange
    (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S))
    (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n := by
  intro a b p hp hl hT g hg hmove
  let A := reducedAmalgam L S
  let N := reflectionGroup c t
  let r := reflectionPath c t htfix htmove htnorm (2*n)
    (Nat.mul_pos (by decide) (lt_trans Nat.zero_lt_one hn)) a.type
  let q := exchangePath c n hn t htfix htmove htnorm a.type
  have hqp : q.IsPath := r.isPath.reverse
  have hql : q.length=2*n := by
    change r.walk.reverse.length=2*n
    rw [SimpleGraph.Walk.length_reverse,r.length_eq]
  have hqT : ∀ z∈q.support, z∈cartanApartment A N := by
    intro z hz
    change z∈r.walk.reverse.support at hz
    exact r.supported z (by simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hz)
  have hfix : cartan c ≤ pathFixer (X := A.Universal) q := by
    intro k hk j _
    exact reflectionApartment_fixed c t htnorm k hk _ (hqT _ (q.getVert_mem_support j))
  have hf := apartment_path_factorization h c n hn t htfix htmove htsq htnorm htrans hthick
    (q.drop n) (by rw [SimpleGraph.Walk.drop_length,hql]; omega)
    (by
      intro z hz
      rw [SimpleGraph.Walk.drop_support_eq_support_drop_min] at hz
      exact hqT z (List.mem_of_mem_drop hz))
  have hS := pathRoot_take_inf_vertexCore q hqp n (by omega) hodd
    (universal_vertex_core_fixes_neighbors h _ _ (q.adj_getVert_succ (by omega)))
  have hex := halfFixer_exchange_of_natural_coordinates q n hql (cartan c) hfix hf hS
    (Classical.choice (htwo a.type))
  have ha := pathRoots_a h c n hn t htfix htmove htsq htnorm htrans hthick
  have hb := pathRoots_b h c n hn t htfix htmove htsq htnorm htrans hthick
  have hlift := reflection_mem_apartmentGroup c ρ
  have hline := cartanApartment_noBranching A N (cartan c) ρ ha hb hlift
    (cartan_le c) (reflectionGroup_normalizes c t htnorm) le_rfl htsq
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
  have hsym := cartanApartment_symmetries A N ρ ha hb hlift hline
  obtain ⟨f,_,hfq⟩ := hsym.align_paths (source_action A) hline q p hqp hp
    (hql.trans hl.symm) hqT hT (exists_smul_base (Universal.cosetFamily A) a)
  exact exchange_along_path_map q p n hql f (fun k hk => hfq k (by omega)) hl hex g hg hmove

variable (hsign : ∀ i x, x∈reflectionGroup c t →
  (∀ r∈((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n (x⁻¹*r*x) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n)) ∨
  (∀ r∈((pathRoots h c n hn t htfix htmove htsq htnorm htrans hthick) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n ((t i*x)⁻¹*r*(t i*x)) ∈
    (originalMiddle (reducedAmalgam L S)).map (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) n)))

/-- The actual marked finite quotient in the natural-module branch, with
exchange proved from the local coordinate profiles. -/
def naturalFiniteQuotient : Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient
    (recognitionEndpoints (reducedAmalgam L S)) :=
  pathFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_natural_exchange h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd htwo) hsign

/-- Both literal endpoint inclusion squares and the whole original Borel map. -/
def naturalFiniteMarkedIso : RankTwoAmalgam.Iso (reducedAmalgam L S)
    (naturalFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
      htwo hsign).standardAmalgam :=
  pathFiniteMarkedIso h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_natural_exchange h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd htwo) hsign

/-- The same source quotient has its original normal two-group, abelian odd
Cartan complement and saturation. -/
def naturalFiniteSplitData : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (naturalFiniteQuotient h c n hn t htfix htmove htsq htnorm htrans hthick hodd
      htwo hsign).tits :=
  pathFiniteSplitData h c n hn t htfix htmove htsq htnorm htrans hthick hodd
    (source_natural_exchange h c n hn t htfix htmove htsq htnorm htrans hthick
      hodd htwo) hsign

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
