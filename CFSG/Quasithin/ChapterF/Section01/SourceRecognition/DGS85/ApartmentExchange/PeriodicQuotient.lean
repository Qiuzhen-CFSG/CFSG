module
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicApartment
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionApartment

/-!
# The actual periodic Cartan apartment and its quotient intersection

Construct the integer line through the original marked edge of the universal
amalgam tree from the chosen involutions. Its range is the literal union of
the two normalizer orbits. On this line the apartment equivalence is congruence
modulo 2(s-1), so a normalizer element fixing the quotient edge fixes every
quotient line vertex. A Borel representative then fixes an original long path,
and its odd stabilizer places that representative in the Cartan.

This proves the quotient Borel--normalizer intersection needed by the genuine
Tits-system construction. The final constructors preserve both original
endpoint inclusions and the full middle map and derive split saturation.
Neither apartment nonbranching nor the quotient intersection is an input.

The source choice of Cartan and root groups, the Chapter 14 exchange
alternatives, quotient root signs, and original normal-two-group/abelian-Cartan
factorization remain explicit. This is an intermediate source construction,
not the full (14.19) or Theorem D. Source: DGS, *Groups and Graphs* (1985),
Part II, (3.6)--(3.7), pp.77--80, and (14.2),(14.10), pp.210--211,216--217.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.GroupAction.CubicTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R)
variable (roots : Bool → LocalRootAction (X := α.Universal) (sourceGraph α))
variable (ha : ∀ i, (roots i).a = base (Universal.cosetFamily α) i)
variable (hb : ∀ i, (roots i).b = base (Universal.cosetFamily α) (!i))
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)

include ha in
private theorem reflection_fixes (i : Bool) :
    (roots i).reflection • base (Universal.cosetFamily α) i =
      base (Universal.cosetFamily α) i := by simpa only [ha] using (roots i).fixes_a

include hb in
private theorem reflection_moves (i : Bool) :
    (roots i).reflection • base (Universal.cosetFamily α) (!i) ≠
      base (Universal.cosetFamily α) (!i) := by
  rw [← hb i, (roots i).sends_b]
  exact (roots i).distinct.symm

/-- The explicit integer line through the original marked edge, with
translation the right chosen reflection times the left one. -/
def cartanLine : Line (sourceGraph α) :=
  (localMoversTrack (Universal.cosetGraph_isTree α hL hR).isAcyclic
    ⟨source_action α⟩
    (show (sourceGraph α).Adj (base (Universal.cosetFamily α) false)
      (base (Universal.cosetFamily α) true) from
      ⟨Bool.false_ne_true, incident_base _ _ _⟩)
    (x := (roots false).reflection) (y := (roots true).reflection)
    (by exact reflection_fixes α roots ha false) (by exact reflection_fixes α roots ha true)
    (by exact reflection_moves α roots hb false) (by exact reflection_moves α roots hb true)).toLine

@[simp] theorem cartanLine_zero :
    (cartanLine α roots ha hb hL hR).vertex 0 = base (Universal.cosetFamily α) false := by
  change alternatingVertex _ _ _ 0 = _
  simp [alternatingVertex]

@[simp] theorem cartanLine_one :
    (cartanLine α roots ha hb hL hR).vertex 1 = base (Universal.cosetFamily α) true := by
  change alternatingVertex _ _ _ 1 = _
  simp [alternatingVertex]

variable (N K : Subgroup α.Universal)
variable (hlift : ∀ i, (roots i).reflection ∈ N)
variable (hK : K ≤ originalMiddle α)
variable (hnorm : N ≤ Subgroup.normalizer (K : Set α.Universal))
variable (hgen : N ≤ Subgroup.closure
  ((K : Set α.Universal) ∪ Set.range fun i => (roots i).reflection))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)

include hgen in
private theorem normalizer_generated_pair : N ≤ Subgroup.closure ((K : Set α.Universal) ∪
    {(roots false).reflection, (roots true).reflection}) := by
  apply hgen.trans
  apply Subgroup.closure_mono
  rintro g (hg | ⟨i, rfl⟩)
  · exact Or.inl hg
  · right
    cases i <;> simp

include ha hb hL hR hlift hK hnorm hgen hinv in
/-- The original two normalizer orbits equal the range of the explicit line. -/
theorem cartanApartment_eq_line : cartanApartment α N =
    Set.range (cartanLine α roots ha hb hL hR).vertex := by
  have hfix (k : α.Universal) (hk : k∈K) :
      k • base (Universal.cosetFamily α) false = base (Universal.cosetFamily α) false ∧
      k • base (Universal.cosetFamily α) true = base (Universal.cosetFamily α) true :=
    ⟨cartanApartment_fixed α N K hK hnorm hL hR k hk _ (cartanApartment_base α N false),
      cartanApartment_fixed α N K hK hnorm hL hR k hk _ (cartanApartment_base α N true)⟩
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
  exact reflectionOrbit_eq_range (reflection_fixes α roots ha false)
    (reflection_fixes α roots ha true) (hinv false) (hinv true) K N
    (hlift false) (hlift true) hnorm hfix (normalizer_generated_pair α roots N K hgen)

variable (n : ℕ) (hKN : K ≤ N) (hn : 1 < n)
variable (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))
variable (hsep : Separated (sourceRelation α (cartanApartment α N) n) (sourceGraph α) (2*n))

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd hsep in
/-- The Borel--normalizer intersection in the actual quotient is the image
of their original intersection. This is derived from the periodic line,
separation and the odd path stabilizer, not from endpoint injectivity. -/
theorem reflection_quotient_intersection [Finite L] [Finite R] :
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n) ⊓
      N.map (quotientMap α (cartanApartment α N) n) =
    (originalMiddle α ⊓ N).map (quotientMap α (cartanApartment α N) n) := by
  let l := cartanLine α roots ha hb hL hR
  have he := cartanApartment_eq_line α roots ha hb hL hR N K hlift hK hnorm hgen hinv
  have hline := cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR
  have hdeg := cartanApartment_twoNeighbors α N roots ha hb hlift
  have hfixall := cartanApartment_fixed α N K hK hnorm hL hR
  have hhallEdges := cartanApartment_hall_edges α N roots ha hb hlift hline K hK hnorm hL hR hhall
  have hperiod (i : ℤ) : sourceRelation α (cartanApartment α N) n
      (l.vertex (i+(2*n:ℕ))) (l.vertex i) := by
    change apartmentSetoid (X := α.Universal) (sourceGraph α) (cartanApartment α N) n _ _
    rw [he]
    exact apartment_line_period (Universal.cosetGraph_isTree α hL hR).isAcyclic l n i
  have hform : ∀ g∈N, ∃ c : ℤ,
      (∀ i, g • l.vertex i = l.vertex (c+i)) ∨
      (∀ i, g • l.vertex i = l.vertex (c-i)) := by
    apply line_action_of_generators l.vertex K N (roots false).reflection (roots true).reflection
    · intro k hk i
      exact hfixall k hk _ (by rw [he]; exact ⟨i, rfl⟩)
    · exact alternatingVertex_left_reflection (reflection_fixes α roots ha false)
        (reflection_fixes α roots ha true) (hinv false) (hinv true)
    · exact alternatingVertex_right_reflection (reflection_fixes α roots ha false)
        (reflection_fixes α roots ha true) (hinv false) (hinv true)
    · exact normalizer_generated_pair α roots N K hgen
  have hBa : originalMiddle α ≤ MulAction.stabilizer α.Universal (l.vertex 0) := by
    rw [show l.vertex 0 = base (Universal.cosetFamily α) false from cartanLine_zero α roots ha hb hL hR,
      stabilizer_base, originalMiddle, ← Universal.overlap_eq α hL hR]
    exact inf_le_left
  have hBb : originalMiddle α ≤ MulAction.stabilizer α.Universal (l.vertex 1) := by
    rw [show l.vertex 1 = base (Universal.cosetFamily α) true from cartanLine_one α roots ha hb hL hR,
      stabilizer_base, originalMiddle, ← Universal.overlap_eq α hL hR]
    exact inf_le_right
  obtain ⟨b, p, hp, hlen, hpT, _⟩ := path_extension_in_set
    (Universal.cosetGraph_isTree α hL hR).isAcyclic hdeg
    (SimpleGraph.Walk.nil : (sourceGraph α).Walk (l.vertex 0) (l.vertex 0))
    SimpleGraph.Walk.IsPath.nil (by
      intro z hz
      have hz' : z = l.vertex 0 := List.mem_singleton.mp hz
      rw [hz', he]
      exact ⟨0, rfl⟩) (show 0 ≤ n+1 from Nat.zero_le _)
  have hfix : pathFixer (X := α.Universal) p = K :=
    pathFixer_eq_cartan K hfixall hhallEdges (source_vertexStabilizer_finite α)
      p (by omega) hpT (source_pathFixer_pi α n hodd p hp hlen)
  apply image_intersection_of_line (quotientMap α (cartanApartment α N) n)
    (sourceRelation α (cartanApartment α N) n)
    (fun he v => related_of_quotient_eq (apartmentSetoid_invariant (source_action α)) he v)
    (Universal.cosetGraph_isTree α hL hR) (source_action α) l (2*n) (by omega) hsep hperiod
    (originalMiddle α) K N hBa hBb hK hKN hform p
    (by simpa only [he] using hpT) hfix.le

variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal)
  (sourceGraph α) (cartanApartment α N) n)

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd htrans hexchange in
/-- The literal Chapter 14 apartment hypotheses imply the quotient Cartan
intersection, with short-distance separation itself derived by exchange. -/
theorem reflection_quotient_intersection_of_exchange [Finite L] [Finite R] :
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n) ⊓
      N.map (quotientMap α (cartanApartment α N) n) =
    (originalMiddle α ⊓ N).map (quotientMap α (cartanApartment α N) n) := by
  have hline := cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR
  apply reflection_quotient_intersection α roots ha hb hL hR N K hlift hK hnorm hgen hinv
    n hKN hn hhall hodd
  exact source_apartment_separated α (cartanApartment α N) n hL hR htrans hline
    (cartanApartment_unique α N roots ha hb hlift hline K hKN hK hnorm hL hR n hhall hodd)
    hexchange (by omega)

variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (hsign : ∀ i x, x ∈ N →
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n (x⁻¹*r*x) ∈
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle α).map (quotientMap α (cartanApartment α N) n)))

/-- The finite marked quotient with both apartment nonbranching and the
quotient Borel--normalizer intersection proved from the actual geometry. -/
noncomputable abbrev periodicFiniteQuotient [Finite L] [Finite R] :=
  cartanFiniteQuotient α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore
    (reflection_quotient_intersection_of_exchange α roots ha hb hL hR N K hlift hK hnorm hgen
      hinv n hKN hn hhall hodd htrans hexchange)

/-- The same quotient construction preserves the two original endpoint
maps and the whole original middle map, through a single marked isomorphism. -/
noncomputable abbrev periodicFiniteMarkedIso [Finite L] [Finite R] :=
  cartanFiniteMarkedIso α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore
    (reflection_quotient_intersection_of_exchange α roots ha hb hL hR N K hlift hK hnorm hgen
      hinv n hKN hn hhall hodd htrans hexchange)

/-- Splitness and saturation on that same quotient, with no assumed
quotient-intersection or saturation equation. The original source
normal-two-group/abelian-Cartan factorization remains explicit. -/
noncomputable abbrev periodicFiniteSplitData [Finite L] [Finite R]
    (U : Subgroup α.Universal)
    (hUnorm : originalMiddle α ≤ Subgroup.normalizer (U : Set α.Universal))
    (hTwo : IsPGroup 2 U) (hKabelian : IsMulCommutative K)
    (hfactor : U ⊔ K = originalMiddle α) :=
  cartanFiniteSplitData α N roots ha hb hlift
    (cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR)
    K hKN hK hnorm hL hR n hgen hsign hhall hodd htrans hexchange hn hcore
    (reflection_quotient_intersection_of_exchange α roots ha hb hL hR N K hlift hK hnorm hgen
      hinv n hKN hn hhall hodd htrans hexchange) U hUnorm hTwo hKabelian hfactor

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
