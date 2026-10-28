module
public import Theory.GroupTheory.WeakBNPair.RegularTree.ReflectionApartment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.CartanApartment

/-!
# The chosen involutions give the actual nonbranching Cartan apartment

Apply the embedded integer-line construction to the two characteristic-two
involutions of DGS (14.2) on the actual universal coset tree. The Cartan fixes
its marked edge and is normalized by the generated normalizer. Thus its two
normalizer orbits are exactly that line, which proves nonbranching.

The finite quotient, both marked inclusion squares, and split-data consumers
below use this proved fact. The source choice of the involutions and roots,
the exchange alternatives, quotient root signs and quotient Cartan
intersection remain explicit; this does not assert (14.19) or Theorem D.
Source: DGS, *Groups and Graphs* (1985), Part II, (14.2), pp.210--211,
(14.10), pp.216--217, and (3.6)--(3.7), pp.77--80.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (N K : Subgroup α.Universal)
variable (roots : Bool → LocalRootAction (X := α.Universal) (sourceGraph α))
variable (ha : ∀ i, (roots i).a = base (Universal.cosetFamily α) i)
variable (hb : ∀ i, (roots i).b = base (Universal.cosetFamily α) (!i))
variable (hlift : ∀ i, (roots i).reflection ∈ N)
variable (hK : K ≤ originalMiddle α)
variable (hnorm : N ≤ Subgroup.normalizer (K : Set α.Universal))
variable (hgen : N ≤ Subgroup.closure
  ((K : Set α.Universal) ∪ Set.range fun i => (roots i).reflection))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)

include ha hb hlift hK hnorm hgen hinv hL hR in
/-- The characteristic-two choices in DGS (14.2) make the literal Cartan
orbit apartment nonbranching. No apartment valence bound is assumed. -/
theorem cartanApartment_noBranching :
    NoBranchingIn (sourceGraph α) (cartanApartment α N) := by
  have hfix (k : α.Universal) (hk : k∈K) :
      k • base (Universal.cosetFamily α) false = base (Universal.cosetFamily α) false ∧
      k • base (Universal.cosetFamily α) true = base (Universal.cosetFamily α) true :=
    ⟨cartanApartment_fixed α N K hK hnorm hL hR k hk _ (cartanApartment_base α N false),
      cartanApartment_fixed α N K hK hnorm hL hR k hk _ (cartanApartment_base α N true)⟩
  have hgen' : N ≤ Subgroup.closure ((K : Set α.Universal) ∪
      {(roots false).reflection, (roots true).reflection}) := by
    apply hgen.trans
    apply Subgroup.closure_mono
    rintro g (hg | ⟨i, rfl⟩)
    · exact Or.inl hg
    · right
      cases i <;> simp
  have he : cartanApartment α N = {v | ∃ g∈N,
      g • base (Universal.cosetFamily α) false = v ∨
      g • base (Universal.cosetFamily α) true = v} := by
    ext v
    constructor
    · rintro ⟨g, hg, i, he⟩
      exact ⟨g, hg, by cases i; exact Or.inl he; exact Or.inr he⟩
    · rintro ⟨g, hg, he | he⟩
      · exact ⟨g, hg, false, he⟩
      · exact ⟨g, hg, true, he⟩
  rw [he]
  apply reflectionOrbit_noBranching (Universal.cosetGraph_isTree α hL hR).isAcyclic
    ⟨source_action α⟩
    (show (sourceGraph α).Adj (base (Universal.cosetFamily α) false)
      (base (Universal.cosetFamily α) true) from
      ⟨Bool.false_ne_true, incident_base _ _ _⟩)
    (x := (roots false).reflection) (y := (roots true).reflection)
    (by simpa only [ha] using (roots false).fixes_a)
    (by simpa only [ha] using (roots true).fixes_a)
    (by
      simpa only [hb, Bool.not_false] using
        (show (roots false).reflection • (roots false).b ≠ (roots false).b by
          rw [(roots false).sends_b]
          exact (roots false).distinct.symm))
    (by
      simpa only [hb, Bool.not_true] using
        (show (roots true).reflection • (roots true).b ≠ (roots true).b by
          rw [(roots true).sends_b]
          exact (roots true).distinct.symm))
    (hinv false) (hinv true) K N (hlift false) (hlift true) hnorm hfix hgen'

variable (hKN : K ≤ N) (n : ℕ)
variable (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))
variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal)
  (sourceGraph α) (cartanApartment α N) n)
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (hsign : ∀ i x, x ∈ N →
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n (x⁻¹*r*x) ∈
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle α).map (quotientMap α (cartanApartment α N) n)))
variable (hBN : (originalMiddle α).map (quotientMap α (cartanApartment α N) n) ⊓
    N.map (quotientMap α (cartanApartment α N) n) =
  (originalMiddle α ⊓ N).map (quotientMap α (cartanApartment α N) n))

/-- Literal source application: the two chosen involutions remove the
nonbranching premise from the finite marked quotient constructor. -/
noncomputable abbrev reflectionFiniteQuotient [Finite L] [Finite R] :=
  cartanFiniteQuotient α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore hBN

/-- Both original inclusion squares survive the constructed finite quotient;
nonbranching is proved from the involutions on the same universal tree. -/
noncomputable abbrev reflectionFiniteMarkedIso [Finite L] [Finite R] :=
  cartanFiniteMarkedIso α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore hBN

/-- The same actual quotient is split and saturated under the original
normal-two-group/abelian-Cartan factorization. -/
noncomputable abbrev reflectionFiniteSplitData [Finite L] [Finite R]
    (U : Subgroup α.Universal)
    (hUnorm : originalMiddle α ≤ Subgroup.normalizer (U : Set α.Universal))
    (hTwo : IsPGroup 2 U) (hKabelian : IsMulCommutative K)
    (hfactor : U ⊔ K = originalMiddle α) :=
  cartanFiniteSplitData α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore hBN
    U hUnorm hTwo hKabelian hfactor
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
