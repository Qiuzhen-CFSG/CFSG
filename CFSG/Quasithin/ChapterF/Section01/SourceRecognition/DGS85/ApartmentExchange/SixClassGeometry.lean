module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentNeighborLiftingGeneral
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphCycles
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphAction
public import Theory.Combinatorics.SimpleGraph.GeneralizedHexagon.RootRigidity
public import Theory.GroupAction.RankTwoCosetGeometry.Distance

/-!
# The raw six-path quotient is a thick generalized hexagon

The apartment relation preserves vertex types. Separation and neighbor lifting
transfer short-path uniqueness from the universal tree, while apartment
shortening gives diameter six. The original source valence supplies thickness.
Apply root rigidity directly to this raw class graph, before any BN-pair or
root-sign argument, with the literal global class action.

Source: DGS, *Groups and Graphs* (1985), (3.6), pp.77--78.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open SimpleGraph SimpleGraph.Walk
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
universe u
variable {P B R : Type u} [Group P] [Group B] [Group R]
variable (A : RankTwoAmalgam P B R) (T : Set (SourceVertex A))
local notation "r" => sourceRelation A T 6
local notation "Δ" => classGraph (sourceGraph A) r

private theorem six_relation_same_type {a b : SourceVertex A} (hab : r a b) : a.type=b.type := by
  induction hab with
  | rel a b hab =>
    obtain ⟨p, _, hlen, _⟩ := hab
    exact (RankTwo.even_walk_iff _ p).mp (by rw [hlen]; decide)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private def six_class_color : Quotient r → Bool :=
  Quotient.lift (fun a : SourceVertex A => a.type) (fun _ _ hh => six_relation_same_type A T hh)

private theorem six_class_color_adj {a b : Quotient r} (hab : (Δ).Adj a b) :
    six_class_color A T a ≠ six_class_color A T b := by
  obtain ⟨_,a,b,rfl,rfl,hab⟩ := hab
  exact hab.1

private theorem six_class_connected
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 12) : (Δ).Connected := by
  exact (Universal.cosetGraph_isTree A hL hR).connected.map
    (classGraphMap hsep (by decide)) Quotient.mk_surjective

private theorem six_class_diameter
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 12)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 7)
    (a b : Quotient r) : (Δ).dist a b ≤ 6 := by
  let tree := Universal.cosetGraph_isTree A hL hR
  have hext : ApartmentExtension (X := A.Universal) (sourceGraph A) T 6 :=
    apartmentExtension_of_cover (X := A.Universal)
    (Γ := sourceGraph A) (T := T) tree.isAcyclic (source_action A) hdeg
    (by decide : 0<6) hcover
  obtain ⟨p,hp⟩ := classGraph_bounded_walks tree.connected hsep (by decide) 6
    (fun a => exists_bounded_representative (sourceGraph A) r a 6
      (apartment_shortening tree.connected hext a)) a b
  exact (dist_le p).trans hp

private theorem six_class_thickness
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hval : ∀ v : SourceVertex A, 3 ≤ Nat.card ((sourceGraph A).neighborSet v))
    (hsep : Separated r (sourceGraph A) 12)
    (hlift : NeighborLifting (sourceGraph A) r) :
    ∀ v a b : Quotient r, ∃ z, (Δ).Adj v z ∧ z≠a ∧ z≠b := by
  intro v a b
  obtain ⟨v,rfl⟩ := Quotient.exists_rep v
  have hcard : 3 ≤ Nat.card ((Δ).neighborSet (Quotient.mk r v)) := by
    let f := classGraphMap hsep (by decide : 1 < 12)
    have heq : Nat.card ((sourceGraph A).neighborSet v) =
        Nat.card ((Δ).neighborSet (Quotient.mk r v)) :=
      Nat.card_congr (Equiv.ofBijective (f.mapNeighborSet v)
        (classGraph_neighbor_bijective
          (Universal.cosetGraph_isTree A hL hR).connected hsep (by decide) hlift v))
    rw [← heq]
    exact hval v
  have hp : ({a,b} : Set (Quotient r)).ncard ≤ 2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (Quotient r))
  have hncard : 3 ≤ ((Δ).neighborSet (Quotient.mk r v)).ncard := by
    rw [←Nat.card_coe_set_eq]
    exact hcard
  obtain ⟨z,hz,hzne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (by omega :
    ({a,b} : Set (Quotient r)).ncard < ((Δ).neighborSet (Quotient.mk r v)).ncard)
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hzne
  exact ⟨z,hz,hzne.1,hzne.2⟩

/-- The raw apartment class graph has generalized-hexagon geometry. -/
def six_class_geometry
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hsep : Separated r (sourceGraph A) 12)
    (hlift : NeighborLifting (sourceGraph A) r)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 7) :
    SimpleGraph.GeneralizedHexagon.Geometry Δ where
  color := six_class_color A T
  color_adj := six_class_color_adj A T
  connected := six_class_connected A T hL hR hsep
  diameter := six_class_diameter A T hL hR hsep hdeg hcover
  short_paths := classGraph_short_paths_unique
    (Universal.cosetGraph_isTree A hL hR) hsep hlift

/-- Fixing five interior stars and one exit kills the original class action. -/
theorem six_class_root_rigidity
    (hL : Function.Injective A.left) (hR : Function.Injective A.right)
    (hval : ∀ v : SourceVertex A, 3 ≤ Nat.card ((sourceGraph A).neighborSet v))
    (hsep : Separated r (sourceGraph A) 12)
    (hlift : NeighborLifting (sourceGraph A) r)
    (hdeg : TwoNeighborsIn (sourceGraph A) T)
    (hcover : ApartmentsCover (X := (A).Universal) (sourceGraph A) T 7)
    {a b : Quotient r} (p : (Δ).Walk a b) (hp : p.IsPath) (hlen : p.length = 6)
    (g : (A).Universal)
    (hstars : ∀ j, 0 < j → j < 6 → ∀ z, (Δ).Adj (p.getVert j) z →
      quotientAction r (apartmentSetoid_invariant (source_action A)) g z = z)
    (z : Quotient r) (hadj : (Δ).Adj b z) (hprev : z ≠ p.getVert 5)
    (hfix : quotientAction r (apartmentSetoid_invariant (source_action A)) g z = z) :
    ∀ v, quotientAction r (apartmentSetoid_invariant (source_action A)) g v = v := by
  let f : Δ ≃g Δ :=
    { toEquiv := quotientAction r (apartmentSetoid_invariant (source_action A)) g
      map_rel_iff' := quotientAction_adj_iff (apartmentSetoid_invariant (source_action A))
        (source_action A) g _ _ }
  exact (six_class_geometry A T hL hR hsep hlift hdeg hcover).root_rigidity
    (six_class_thickness A T hL hR hval hsep hlift) f p hp hlen hstars z hadj hprev hfix

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
