module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.LocalRootConstruction
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentSeparation
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.MarkedQuotient

/-!
# The finite marked quotient from the apartment conditions

Apply the proved uniqueness/exchange separation argument on the literal
universal amalgam tree. The chosen apartment contains both endpoints of
the marked edge. Its translates therefore meet every vertex orbit, and
path transitivity supplies the coverage needed for finiteness. Separation
is derived, and gives the two kernel intersections and exact overlap.

With the remaining Cartan and root-sign algebra explicit, this constructs
the precise `SourceBinary.MarkedQuotient` consumed by finite recognition,
on the quotient of the potentially infinite universal completion. Its
marked amalgam isomorphism starts at the original amalgam and retains
both original endpoint inclusions and the whole middle subgroup.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.6)–(3.7), pp.77–80.
Chapter 14 must still produce the chosen Cartan, apartment uniqueness and
exchange from the preceding local profiles. Splitness and recognition are
not inferred from the Tits system alone.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
variable (hdeg : TwoNeighborsIn (sourceGraph α) T)
variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))

include hbase in
/-- The actual marked edge in the apartment ensures that its translates
meet both vertex orbits of the universal coset tree. -/
theorem source_apartment_orbits (a : SourceVertex α) :
    ∃ g : α.Universal, a ∈ apartmentTranslate T g := by
  obtain ⟨g, hg⟩ := exists_smul_base (Universal.cosetFamily α) a
  exact ⟨g, base (Universal.cosetFamily α) a.type, hbase a.type, hg⟩

include hL hR hbase hdeg htrans in
/-- Coverage follows from the genuine path-transitivity condition. -/
theorem source_apartments_cover :
    ApartmentsCover (X := α.Universal) (sourceGraph α) T (n+1) :=
  apartments_cover_of_transitivity (Universal.cosetGraph_isTree α hL hR)
    (source_action α) hdeg htrans (source_apartment_orbits α T hbase)

include hL hR hbase hdeg htrans in
/-- Finiteness of the actual quotient needs no ambient finiteness assumption. -/
theorem geometric_quotient_finite [Finite L] [Finite R] (hn : 0 < n) :
    Finite (QuotientGroup α T n) :=
  quotient_finite_of_cover α T n hL hR hdeg hn
    (source_apartments_cover α T n hL hR hbase hdeg htrans)

variable (hline : NoBranchingIn (sourceGraph α) T)
variable (hunique : ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)

include hL hR htrans hline hunique hexchange in
/-- The source short-distance separation is proved, not an additional input. -/
theorem source_apartment_separated (hn : 0 < n) :
    Separated (sourceRelation α T n) (sourceGraph α) (2*n) :=
  apartment_separated_of_exchange (Universal.cosetGraph_isTree α hL hR)
    (source_action α) hline hn hunique htrans
    (apartmentExchangeMoves_of_chosen (source_action α) hexchange)

variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (d : RootQuotientData (quotientMap α T n))
variable (hB : d.B = originalMiddle α)
variable (hP : ∀ i, d.endpoint i = Universal.cosetFamily α i)
variable (hBN : d.B.map (quotientMap α T n) ⊓ d.N.map (quotientMap α T n) =
  (d.B ⊓ d.N).map (quotientMap α T n))

/-- The original endpoints with the finite-recognition indexing convention. -/
abbrev recognitionEndpoints : Fin 2 → Subgroup α.Universal :=
  fun i => Universal.cosetFamily α (finTwoEquiv i)

/-- The literal finite-recognition input is constructed from the source
apartment, with both local kernels and both parabolic equations proved. -/
noncomputable def recognitionQuotient [Finite L] [Finite R] :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient (recognitionEndpoints α) where
  D := kernel α T n
  normal := kernel_normal α T n
  finite := geometric_quotient_finite α T n hL hR hbase hdeg htrans (by omega)
  disjoint i := disjoint_iff.mpr (kernel_inf_endpoint α T n hL hR
    (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
      hn hcore (finTwoEquiv i))
  tits := sourceTitsSystem α T n hL hR
    (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
      hn hcore d hB hP hBN
  simple i := sourceSimple α T n hL hR
    (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
      hn hcore d hB hP hBN (finTwoEquiv i)
  simple_injective := (sourceSimple_injective α T n hL hR
    (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
      hn hcore d hB hP hBN).comp finTwoEquiv.injective
  simple_range := by
    rw [← sourceSimple_range α T n hL hR
      (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
        hn hcore d hB hP hBN]
    ext w
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨finTwoEquiv i, hi⟩
    · rintro ⟨j, hj⟩
      obtain ⟨i, rfl⟩ := finTwoEquiv.surjective j
      exact ⟨i, hj⟩
  parabolic_image i := by
    change (Universal.cosetFamily α (finTwoEquiv i)).map (quotientMap α T n) = _
    rw [originalEndpoint_image]
    exact sourceTitsSystem_parabolic α T n hL hR
      (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
        hn hcore d hB hP hBN (finTwoEquiv i)
  borel_image := by
    change ((Universal.left α).range ⊓ (Universal.right α).range).map (quotientMap α T n) = _
    rw [Universal.overlap_eq α hL hR]
    exact (originalMiddle_image α T n).trans (sourceTitsSystem_borel α T n hL hR
      (source_apartment_separated α T n hL hR htrans hline hunique hexchange (by omega))
        hn hcore d hB hP hBN).symm

/-- The finite recognition input includes a marking of the original amalgam,
not just the inclusion amalgam of its two ranges in the universal completion. -/
noncomputable def geometricMarkedIso [Finite L] [Finite R] :
    RankTwoAmalgam.Iso α
      (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
        d hB hP hBN).standardAmalgam :=
  (Universal.markedIso α hL hR).trans
    (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN).markedIso

@[simp] theorem geometricMarkedIso_left_apply [Finite L] [Finite R] (x : L) :
    ((geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN).left x).val =
      quotientMap α T n (Universal.left α x) := by
  exact (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN).markedIso_left_apply ((Universal.markedIso α hL hR).left x)

@[simp] theorem geometricMarkedIso_right_apply [Finite L] [Finite R] (x : R) :
    ((geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN).right x).val =
      quotientMap α T n (Universal.right α x) := by
  exact (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN).markedIso_right_apply ((Universal.markedIso α hL hR).right x)

@[simp] theorem geometricMarkedIso_middle_apply [Finite L] [Finite R] (x : B) :
    ((geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN).middle x).val =
      quotientMap α T n (Universal.left α (α.left x)) := by
  exact (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN).markedIso_middle_apply ((Universal.markedIso α hL hR).middle x)

/-- The original faithful overlap gives a faithful Borel in this particular
constructed finite quotient, as required by the finite-recognition reduction. -/
theorem geometric_borel_core_eq_bot [Finite L] [Finite R] :
    (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN).tits.B.normalCore = ⊥ :=
  (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN).borel_core_eq_bot (Universal.generated α) hcore
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
