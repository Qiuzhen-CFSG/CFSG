module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.CartanUniqueness
public import Theory.GroupTheory.Hall.OddNormalProducts

/-!
# DGS apartment uniqueness from odd path stabilizers

Apply the Hall-Cartan path argument on the actual universal amalgam tree.
Finite endpoint groups give all finite vertex stabilizers. The genuine
oddness conclusion of (14.1)(a) then implies apartment uniqueness, removing
that premise from the existing marked finite quotient constructor. Its
original two endpoint maps and whole middle map are retained.

The chosen Cartan, its apartment symmetries, exchange, and the global root
algebra still require their earlier source proofs. This module proves the
(14.10) inference with those inputs; it does not assert (14.19) or Theorem D.
Source: DGS, *Groups and Graphs* (1985), Part II, pp.210,216–217.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R)

/-- Finite original endpoints give finite stabilizers throughout the actual
universal tree, even though its ambient completion is infinite. -/
theorem source_vertexStabilizer_finite [Finite L] [Finite R] (a : SourceVertex α) :
    Finite (MulAction.stabilizer α.Universal a) := by
  have hf (i : Bool) : Finite (Universal.cosetFamily α i) := by
    cases i
    · exact Finite.of_surjective (Universal.left α).rangeRestrict
        (Universal.left α).rangeRestrict_surjective
    · exact Finite.of_surjective (Universal.right α).rangeRestrict
        (Universal.right α).rangeRestrict_surjective
  obtain ⟨g, hg⟩ := exists_smul_base (Universal.cosetFamily α) a
  rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_base]
  let := hf a.type
  exact Finite.of_surjective _ ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)

variable (T : Set (SourceVertex α)) (n : ℕ) (K N : Subgroup α.Universal)
variable (hKN : K ≤ N) (d : ApartmentSymmetries (sourceGraph α) T N)
variable (hline : NoBranchingIn (sourceGraph α) T)
variable (hK : ∀ k ∈ K, ∀ a ∈ T, k • a = a)
variable (hHall : ∀ a ∈ T, ∀ b ∈ T, (sourceGraph α).Adj a b →
  IsHallSubgroup Subgroup.OddHall.oddPrimes
    (K.subgroupOf (MulAction.stabilizer α.Universal a ⊓ MulAction.stabilizer α.Universal b)))
variable (hodd : ∀ {a b} (p : (sourceGraph α).Walk a b), p.IsPath → p.length = n+1 →
  Odd (Nat.card (pathFixer (X := α.Universal) p)))

include hodd in
/-- The actual odd stabilizer conclusion of (14.1)(a), in Hall notation. -/
theorem source_pathFixer_pi {a b : SourceVertex α} (p : (sourceGraph α).Walk a b)
    (hp : p.IsPath) (hlen : p.length = n+1) :
    IsPiSubgroup Subgroup.OddHall.oddPrimes (pathFixer (X := α.Universal) p) := by
  intro q hq htwo
  change q.val = 2 at htwo
  rw [htwo] at hq
  exact (Nat.not_even_iff_odd.mpr (hodd p hp hlen)) (even_iff_two_dvd.mpr hq)

include hKN d hline hK hHall hodd in
/-- DGS (14.10) on the literal universal tree: the Hall Cartan and odd
length-s stabilizers imply uniqueness of translated apartments. -/
theorem source_apartmentsUnique_of_odd_pathFixers [Finite L] [Finite R] :
    ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1) :=
  apartmentsUnique_of_hall_pathFixers (source_action α) hline (n+1) (by omega)
    K N hKN d hK hHall (source_vertexStabilizer_finite α)
    (fun p hp hlen => source_pathFixer_pi α n hodd p hp hlen)

variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
variable (hdeg : TwoNeighborsIn (sourceGraph α) T)
variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (roots : RootQuotientData (quotientMap α T n))
variable (hB : roots.B = originalMiddle α)
variable (hP : ∀ i, roots.endpoint i = Universal.cosetFamily α i)
variable (hBN : roots.B.map (quotientMap α T n) ⊓ roots.N.map (quotientMap α T n) =
  (roots.B ⊓ roots.N).map (quotientMap α T n))

/-- The earlier local path conclusion now discharges uniqueness in the
actual finite-recognition quotient, preserving both standard parabolics
and the image of the entire original Borel. Exchange and root data remain
with the Chapter 14 assembly. -/
noncomputable abbrev cartanRecognitionQuotient [Finite L] [Finite R] :=
  recognitionQuotient α T n hL hR hbase hdeg htrans hline
    (source_apartmentsUnique_of_odd_pathFixers α T n K N hKN d hline hK hHall hodd)
    hexchange hn hcore roots hB hP hBN

/-- The original amalgam maps, rather than only their abstract endpoint
groups, are retained by this Hall-Cartan application. -/
noncomputable abbrev cartanGeometricMarkedIso [Finite L] [Finite R] :=
  geometricMarkedIso α T n hL hR hbase hdeg htrans hline
    (source_apartmentsUnique_of_odd_pathFixers α T n K N hKN d hline hK hHall hodd)
    hexchange hn hcore roots hB hP hBN
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
