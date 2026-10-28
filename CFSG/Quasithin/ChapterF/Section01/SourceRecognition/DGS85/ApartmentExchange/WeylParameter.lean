module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.PeriodicQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.PeriodicWeyl
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility

/-!
# The marked Weyl parameter of the actual apartment quotient

For the same periodic apartment, quotient map and reflection lifts used by
`periodicFiniteQuotient`, prove that the product of the two marked simple
reflections has order exactly n. No abstract polygon parameter is substituted
for the source n = r = s-1.

Each endpoint image is a maximal proper parabolic. Its containment in the
corresponding vertex-class stabilizer is therefore equality: the opposite
reflection moves that class, by short-distance separation. Thus the Borel is
the fixer of the two marked classes. The kernel of the map from the original
apartment group to the Weyl quotient fixes precisely those two classes.
Finally the two original reflection formulas give translation by minus two
on the integer line, whose exact period is 2n.

This argument takes place after the genuine BN construction. In particular,
it retains the preceding exchange and quotient root-sign hypotheses; using
parabolic maximality here does not discharge those earlier premises. No
equality between vertex classes and kernel orbits is assumed.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)--(3.7), pp.77--80,
integer apartment coordinates following (14.2), p.211, and Theorem D, p.224.
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

variable (N K : Subgroup α.Universal)
variable (hlift : ∀ i, (roots i).reflection ∈ N)
variable (hK : K ≤ originalMiddle α)
variable (hnorm : N ≤ Subgroup.normalizer (K : Set α.Universal))
variable (hgen : N ≤ Subgroup.closure
  ((K : Set α.Universal) ∪ Set.range fun i => (roots i).reflection))
variable (hinv : ∀ i, (roots i).reflection * (roots i).reflection = 1)

variable (n : ℕ) (hKN : K ≤ N) (hn : 1 < n)
variable (hhall : IsHallSubgroup Subgroup.OddHall.oddPrimes (K.subgroupOf (originalMiddle α)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))


variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal)
  (sourceGraph α) (cartanApartment α N) n)

variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (hsign : ∀ i x, x ∈ N →
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n (x⁻¹*r*x) ∈
    (originalMiddle α).map (quotientMap α (cartanApartment α N) n)) ∨
  (∀ r ∈ (roots i).root, quotientMap α (cartanApartment α N) n
    (((roots i).reflection*x)⁻¹*r*((roots i).reflection*x)) ∈
      (originalMiddle α).map (quotientMap α (cartanApartment α N) n)))


local notation "d" => periodicFiniteQuotient α roots ha hb hL hR N K hlift hK hnorm hgen
  hinv n hKN hn hhall hodd htrans hexchange hcore hsign

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd htrans hexchange in
private theorem parameter_separated [Finite L] [Finite R] :
    Separated (sourceRelation α (cartanApartment α N) n) (sourceGraph α) (2*n) := by
  have hline := cartanApartment_noBranching α N K roots ha hb hlift hK hnorm hgen hinv hL hR
  intro a b hab hdist
  exact source_apartment_separated α (cartanApartment α N) n hL hR htrans hline
    (cartanApartment_unique α N roots ha hb hlift hline K hKN hK hnorm hL hR n hhall hodd)
    hexchange (by omega) hab hdist

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd htrans hexchange hcore hsign in
/-- The actual vertex-class stabilizer is exactly the matching original endpoint image. -/
theorem periodic_classStabilizer_eq_endpoint [Finite L] [Finite R] (i : Bool) :
    classStabilizer (sourceRelation α (cartanApartment α N) n)
        (apartmentSetoid_invariant (source_action α)) (base (Universal.cosetFamily α) i) =
      (Universal.cosetFamily α i).map (quotientMap α (cartanApartment α N) n) := by
  change classStabilizer (sourceRelation α (cartanApartment α N) n)
      (apartmentSetoid_invariant (source_action α)) (base (Universal.cosetFamily α) i) =
    (Universal.cosetFamily α i).map (_root_.QuotientGroup.mk'
      (quotientKernel (sourceRelation α (cartanApartment α N) n)
        (apartmentSetoid_invariant (source_action α))))
  rw [← stabilizer_base (F := Universal.cosetFamily α) (i := i)]
  apply classStabilizer_eq_image
  · rw [stabilizer_base]
    have hm := (d).parabolic_isCoatom (finTwoEquiv.symm i)
    rw [← (d).parabolic_image] at hm
    change IsCoatom ((Universal.cosetFamily α (finTwoEquiv (finTwoEquiv.symm i))).map
      (_root_.QuotientGroup.mk' (quotientKernel (sourceRelation α (cartanApartment α N) n)
        (apartmentSetoid_invariant (source_action α))))) at hm
    simpa only [Equiv.apply_symm_apply] using hm
  · refine ⟨(roots (!i)).reflection, ?_⟩
    intro he
    have hfix : (roots (!i)).reflection • base (Universal.cosetFamily α) (!i) =
        base (Universal.cosetFamily α) (!i) := by
      simpa only [ha] using (roots (!i)).fixes_a
    have hadj : (sourceGraph α).Adj (base (Universal.cosetFamily α) (!i))
        (base (Universal.cosetFamily α) i) :=
      ⟨by change (!i) ≠ i; cases i <;> decide, incident_base _ _ _⟩
    have hadj' : (sourceGraph α).Adj (base (Universal.cosetFamily α) (!i))
        ((roots (!i)).reflection • base (Universal.cosetFamily α) i) := by
      simpa only [hfix] using source_action α (roots (!i)).reflection hadj
    have hd := (Universal.cosetGraph_isTree α hL hR).connected.dist_triangle
      (u := (roots (!i)).reflection • base (Universal.cosetFamily α) i)
      (v := base (Universal.cosetFamily α) (!i)) (w := base (Universal.cosetFamily α) i)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj'.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hd
    change (sourceGraph α).dist ((roots (!i)).reflection • base (Universal.cosetFamily α) i)
      (base (Universal.cosetFamily α) i) ≤ 1+1 at hd
    have hsame := parameter_separated α roots ha hb hL hR N K hlift hK hnorm hgen hinv
      n hKN hn hhall hodd htrans hexchange he (by omega)
    have hm := (roots (!i)).sends_b
    rw [hb, Bool.not_not] at hm
    exact (roots (!i)).distinct (by rw [hb, Bool.not_not]; exact hsame.symm.trans hm)

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd htrans hexchange hcore hsign in
/-- The whole Borel is characterized by fixation of both original marked classes. -/
theorem periodic_borel_iff_fixes_classes [Finite L] [Finite R] (g : α.Universal) :
    quotientMap α (cartanApartment α N) n g ∈ (d).tits.B ↔
      sourceRelation α (cartanApartment α N) n
        (g • base (Universal.cosetFamily α) false) (base (Universal.cosetFamily α) false) ∧
      sourceRelation α (cartanApartment α N) n
        (g • base (Universal.cosetFamily α) true) (base (Universal.cosetFamily α) true) := by
  rw [← (d).standard_intersection, ← (d).parabolic_image 0, ← (d).parabolic_image 1]
  change _ ∈ (Universal.cosetFamily α false).map (quotientMap α (cartanApartment α N) n) ⊓
    (Universal.cosetFamily α true).map (quotientMap α (cartanApartment α N) n) ↔ _
  rw [Subgroup.mem_inf, ← periodic_classStabilizer_eq_endpoint α roots ha hb hL hR N K
      hlift hK hnorm hgen hinv n hKN hn hhall hodd htrans hexchange hcore hsign false,
    ← periodic_classStabilizer_eq_endpoint α roots ha hb hL hR N K
      hlift hK hnorm hgen hinv n hKN hn hhall hodd htrans hexchange hcore hsign true]
  exact and_congr (mem_classStabilizer _ _ g _) (mem_classStabilizer _ _ g _)

include ha hb hL hR hlift hK hnorm hgen hinv hn hKN hhall hodd htrans hexchange hcore hsign in
/-- The marked Weyl rotation has the source parameter n, on the same quotient and lifts. -/
theorem periodic_simple_product_order [Finite L] [Finite R] :
    orderOf ((d).simple 0 * (d).simple 1) = n := by
  let q := quotientMap α (cartanApartment α N) n
  let l := cartanLine α roots ha hb hL hR
  let F : N →* (d).tits.N :=
    { toFun g := ⟨q g, ⟨g, g.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' g h := Subtype.ext (map_mul q (g : α.Universal) (h : α.Universal)) }
  let f := (_root_.QuotientGroup.mk' (((d).tits.B ⊓ (d).tits.N).subgroupOf (d).tits.N)).comp F
  have hker (g : N) : f g = 1 ↔
      sourceRelation α (cartanApartment α N) n ((g : α.Universal) • l.vertex 0) (l.vertex 0) ∧
      sourceRelation α (cartanApartment α N) n ((g : α.Universal) • l.vertex 1) (l.vertex 1) := by
    have hmem : f g = 1 ↔ q g ∈ (d).tits.B := by
      constructor
      · intro he
        exact ((_root_.QuotientGroup.eq_one_iff (F g)).mp he).1
      · intro he
        exact (_root_.QuotientGroup.eq_one_iff (F g)).mpr ⟨he, (F g).property⟩
    rw [hmem]
    simpa only [l, cartanLine_zero, cartanLine_one] using
      periodic_borel_iff_fixes_classes α roots ha hb hL hR N K hlift hK hnorm hgen hinv
        n hKN hn hhall hodd htrans hexchange hcore hsign g
  let u : N := ⟨(roots false).reflection * (roots true).reflection,
    N.mul_mem (hlift false) (hlift true)⟩
  have he : f u = (d).simple 0 * (d).simple 1 := by
    change f (⟨(roots false).reflection, hlift false⟩ * ⟨(roots true).reflection, hlift true⟩) = _
    rw [map_mul]
    rfl
  rw [← he]
  refine orderOf_line_rotation (sourceRelation α (cartanApartment α N) n)
    (Universal.cosetGraph_isTree α hL hR).isAcyclic l n (by omega)
    (parameter_separated α roots ha hb hL hR N K hlift hK hnorm hgen hinv
      n hKN hn hhall hodd htrans hexchange) ?_ N f hker u ?_
  · intro i
    change apartmentSetoid (X := α.Universal) (sourceGraph α) (cartanApartment α N) n _ _
    rw [cartanApartment_eq_line α roots ha hb hL hR N K hlift hK hnorm hgen hinv]
    exact apartment_line_period (Universal.cosetGraph_isTree α hL hR).isAcyclic l n i
  · intro i
    have hx : (roots false).reflection • base (Universal.cosetFamily α) false =
        base (Universal.cosetFamily α) false := by simpa only [ha] using (roots false).fixes_a
    have hy : (roots true).reflection • base (Universal.cosetFamily α) true =
        base (Universal.cosetFamily α) true := by simpa only [ha] using (roots true).fixes_a
    change ((roots false).reflection * (roots true).reflection) •
      alternatingVertex _ _ _ i = alternatingVertex _ _ _ (i-2)
    rw [mul_smul, alternatingVertex_right_reflection hx hy (hinv false) (hinv true),
      alternatingVertex_left_reflection hx hy (hinv false) (hinv true)]
    congr 1
    omega

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
