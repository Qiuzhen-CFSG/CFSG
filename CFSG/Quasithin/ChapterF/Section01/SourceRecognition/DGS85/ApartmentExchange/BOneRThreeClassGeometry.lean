module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeCompletion
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentNeighborLifting
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraph

/-!
# The raw generalized triangle from the original r=3 profiles

Apply the constructed apartment neighbor lift to the genuine source exchange.
The resulting graph has the exact equivalence classes used to define the
finite quotient's action kernel. It is finite and bipartite, the literal vertex
quotient is locally bijective, every two classes have a path of length at most
three, short paths are unique, and every class lies on a six-cycle. Both
point/line fibers have unique joins/meets and the original field's panel valence.

The argument uses source path transitivity, apartment extension and separation,
not a marked BN quotient or the missing Borel-image root-sign conclusion.
The nonbinary full-Cartan profiles and original r=3,s=4 parameters remain the
inputs. The other original source branches are not addressed here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(3.6), printed pp.77--78, with the exchange constructed from (14.13).
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open SimpleGraph SimpleGraph.Walk
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

section Types
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)

/-- The raw source graph, using exactly the relation defining the group kernel. -/
abbrev sourceClassGraph := classGraph (sourceGraph α) (sourceRelation α T n)

/-- Every elementary relation has even length, so its full equivalence closure
preserves the two original vertex types. -/
theorem sourceRelation_same_type {a b : SourceVertex α} (hab : sourceRelation α T n a b) :
    a.type = b.type := by
  induction hab with
  | rel a b hab =>
    obtain ⟨p, _, hlen, _⟩ := hab
    exact (Subgroup.CosetGeometry.RankTwo.even_walk_iff _ p).mp
      (by rw [hlen]; exact ⟨n, by omega⟩)
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The point/line type on the actual quotient classes. -/
def sourceClassType : Quotient (sourceRelation α T n) → Bool :=
  Quotient.lift (fun a : SourceVertex α => a.type) (fun _ _ h => sourceRelation_same_type α T n h)

@[simp] theorem sourceClassType_mk (a : SourceVertex α) :
    sourceClassType α T n (Quotient.mk _ a) = a.type := rfl

/-- Adjacent raw classes lie in opposite original type fibers. -/
theorem sourceClassGraph_bipartition {A B : Quotient (sourceRelation α T n)}
    (hab : (sourceClassGraph α T n).Adj A B) :
    sourceClassType α T n A ≠ sourceClassType α T n B := by
  obtain ⟨_, a, b, rfl, rfl, hab⟩ := hab
  exact hab.1
/-- Walk parity records exactly the original point/line types on raw classes. -/
theorem sourceClassGraph_even_walk {a b : Quotient (sourceRelation α T n)}
    (p : (sourceClassGraph α T n).Walk a b) :
    Even p.length ↔ sourceClassType α T n a = sourceClassType α T n b := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    rw [length_cons, Nat.even_add_one, ih]
    have ht := sourceClassGraph_bipartition α T n hab
    cases ha : sourceClassType α T n a <;> cases hb : sourceClassType α T n b <;>
      cases hc : sourceClassType α T n c <;> simp_all
end Types

namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "ρ" => fullCartanPathRoots ds
local notation "N" => apartmentGroup c ρ
local notation "T" => cartanApartment A N
local notation "r" => sourceRelation A T n

/-- The class graph retains the same source relation as the finite group quotient. -/
abbrev fullCartanClassGraph := sourceClassGraph A T n

private theorem fullCartan_tree : (sourceGraph A).IsTree :=
  Universal.cosetGraph_isTree A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))

private theorem fullCartan_apartment_degree : TwoNeighborsIn (sourceGraph A) T :=
  cartanApartment_twoNeighbors A N ρ (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (reflection_mem_apartmentGroup c ρ)

private theorem fullCartan_apartment_extension :
    ApartmentExtension (X := (reducedAmalgam L S).Universal) (sourceGraph A) T n :=
  apartmentExtension_of_cover (fullCartan_tree (L := L) (S := S)).isAcyclic
    (source_action A) (fullCartan_apartment_degree ds)
    (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds))
    (source_apartments_cover A T n (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1)) (cartanApartment_base A N)
      (fullCartan_apartment_degree ds) (fullCartanProfiles_path_transitive ds))

variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include hr in
/-- Both elementary exchange and its equivalence closure now lift neighbors
in the literal original r=3 source quotient. -/
theorem fullCartan_source_neighbor_lifting_of_r_three : NeighborLifting (sourceGraph A) r := by
  have hn : n = 3 := (fullCartanProfiles_parameters ds).1.unique hr.1
  have htrans : BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph A) (n+1) := fullCartanProfiles_path_transitive ds
  rw [hn] at htrans ⊢
  intro a b c hab hbc
  exact apartmentSetoid_neighbor_lift_three (fullCartan_tree (L := L) (S := S))
    (source_action A) (fullCartan_apartment_degree ds) htrans
    (apartmentExchangeMoves_of_chosen (source_action A)
      (fullCartan_source_exchange_of_r_three ds hr)) hab hbc

/-- The map to raw classes is the literal vertex quotient. -/
abbrev fullCartanClassMap : sourceGraph A →g fullCartanClassGraph ds :=
  classGraphMap (fullCartan_source_separated_of_r_three ds hr)
    (by have hn := fullCartanPathLength_gt ds; omega)

/-- Local bijectivity is constructed from source exchange and separation. -/
theorem fullCartanClassMap_neighbor_bijective (a : SourceVertex A) :
    Function.Bijective ((fullCartanClassMap ds hr).mapNeighborSet a) :=
  classGraph_neighbor_bijective (fullCartan_tree (L := L) (S := S)).connected
    (fullCartan_source_separated_of_r_three ds hr)
    (by have hn := fullCartanPathLength_gt ds; omega)
    (fullCartan_source_neighbor_lifting_of_r_three ds hr) a

/-- The raw class graph is finite, even though the universal tree is infinite. -/
theorem fullCartanClassGraph_finite : Finite (Quotient r) := by
  let := (reduced_hypothesis h).finite_parabolic 0
  let := (reduced_hypothesis h).finite_parabolic 1
  exact finite_apartment_classes (fullCartan_tree (L := L) (S := S)).connected
    (source_finite_valence A) (fullCartan_apartment_extension ds)
    (base (Universal.cosetFamily A) false)

include hr in
/-- Source shortening supplies the length-three bound, on the raw graph. -/
theorem fullCartanClassGraph_bounded_walks (a b : Quotient r) :
    ∃ p : (fullCartanClassGraph ds).Walk a b, p.length ≤ 3 := by
  have hn : n = 3 := (fullCartanProfiles_parameters ds).1.unique hr.1
  obtain ⟨p, hp⟩ := classGraph_bounded_walks (fullCartan_tree (L := L) (S := S)).connected
    (fullCartan_source_separated_of_r_three ds hr)
    (by have hn := fullCartanPathLength_gt ds; omega) n
    (fun a => exists_bounded_representative (sourceGraph A) r a n
      (apartment_shortening (fullCartan_tree (L := L) (S := S)).connected
        (fullCartan_apartment_extension ds) a)) a b
  exact ⟨p, hn ▸ hp⟩

include hr in
/-- Distinct short paths cannot join the same raw classes. -/
theorem fullCartanClassGraph_short_paths_unique {a b : Quotient r}
    (p q : (fullCartanClassGraph ds).Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hpl : p.length < 3) (hql : q.length < 3) : p = q := by
  apply classGraph_short_paths_unique (fullCartan_tree (L := L) (S := S))
    (fullCartan_source_separated_of_r_three ds hr)
    (fullCartan_source_neighbor_lifting_of_r_three ds hr) p q hp hq
  have hn : n = 3 := (fullCartanProfiles_parameters ds).1.unique hr.1
  omega

include hr in
/-- A genuine apartment through each representative supplies a six-cycle
through every raw class, completing the source polygon's cycle clause. -/
theorem fullCartanClassGraph_six_cycle (a : Quotient r) :
    ∃ p : (fullCartanClassGraph ds).Walk a a, p.IsCycle ∧ p.length = 6 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep a
  obtain ⟨g, hg⟩ := source_apartment_orbits A T (cartanApartment_base A N) a
  obtain ⟨b, p, hp, hlen, hpT, _⟩ := path_extension_in_set
    (fullCartan_tree (L := L) (S := S)).isAcyclic
    (twoNeighborsIn_translate (source_action A) (fullCartan_apartment_degree ds) g)
    (.nil : (sourceGraph A).Walk a a) (.nil)
    (by intro z hz; have he : z = a := List.mem_singleton.mp hz; exact he ▸ hg)
    (Nat.zero_le (2*n))
  have hab : r b a := Relation.EqvGen.rel _ _ (apartmentStep_symm ⟨p, hp, hlen, g, hpT⟩)
  obtain ⟨q, hq, hql⟩ := classGraph_cycle_of_path
    (fullCartan_source_separated_of_r_three ds hr)
    (by have hn := fullCartanPathLength_gt ds; omega) p hp hlen hab
  have hn : n = 3 := (fullCartanProfiles_parameters ds).1.unique hr.1
  exact ⟨q, hq, by omega⟩

include hr in
/-- The literal quotient map makes the raw graph connected. -/
theorem fullCartanClassGraph_connected : (fullCartanClassGraph ds).Connected :=
  (fullCartan_tree (L := L) (S := S)).connected.map (fullCartanClassMap ds hr)
    Quotient.mk_surjective

include hr in
/-- The distance formulation of the generalized-triangle diameter law. -/
theorem fullCartanClassGraph_diameter (a b : Quotient r) :
    (fullCartanClassGraph ds).dist a b ≤ 3 := by
  obtain ⟨p, hp⟩ := fullCartanClassGraph_bounded_walks ds hr a b
  exact (dist_le p).trans hp

include hr in
/-- The source's diameter law with actual simple paths. -/
theorem fullCartanClassGraph_bounded_paths (a b : Quotient r) :
    ∃ p : (fullCartanClassGraph ds).Walk a b, p.IsPath ∧ p.length ≤ 3 := by
  obtain ⟨p, hp, hlen⟩ := (fullCartanClassGraph_connected ds hr).exists_path_of_dist a b
  exact ⟨p, hp, hlen ▸ fullCartanClassGraph_diameter ds hr a b⟩

include hr in
/-- Two distinct vertices of either raw type fiber have exactly one common
neighbor. These are the projective join and meet laws on the same classes. -/
theorem fullCartanClassGraph_commonNeighbor {a b : Quotient r}
    (htype : sourceClassType A T n a = sourceClassType A T n b) (hne : a ≠ b) :
    ∃! z, (fullCartanClassGraph ds).Adj a z ∧ (fullCartanClassGraph ds).Adj b z := by
  obtain ⟨p, hpl⟩ := fullCartanClassGraph_bounded_walks ds hr a b
  have hp2 : p.length = 2 := by
    obtain ⟨k, hk⟩ := (sourceClassGraph_even_walk A T n p).mpr htype
    have hp0 : p.length ≠ 0 := fun hh => hne (eq_of_length_eq_zero hh)
    omega
  have haz : (fullCartanClassGraph ds).Adj a (p.getVert 1) := by
    simpa only [getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
  have hbz : (fullCartanClassGraph ds).Adj b (p.getVert 1) := by
    have hh := p.adj_getVert_succ (by omega : 1 < p.length)
    rw [show 1+1=p.length from hp2.symm, getVert_length] at hh
    exact hh.symm
  refine ⟨p.getVert 1, ⟨haz, hbz⟩, ?_⟩
  intro w hw
  let q : (fullCartanClassGraph ds).Walk a b := .cons hw.1 (.cons hw.2.symm .nil)
  let t : (fullCartanClassGraph ds).Walk a b := .cons haz (.cons hbz.symm .nil)
  have hq : q.IsPath := by
    apply (IsPath.of_adj hw.2.symm).cons
    simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hw.1.ne, hne⟩
  have ht : t.IsPath := by
    apply (IsPath.of_adj hbz.symm).cons
    simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨haz.ne, hne⟩
  have he := fullCartanClassGraph_short_paths_unique ds hr q t hq ht
    (by change 2 < 3; decide) (by change 2 < 3; decide)
  exact congrArg (fun w => w.getVert 1) he

include hr in
/-- Local bijectivity retains the original field's exact panel valence. -/
theorem fullCartanClassGraph_neighbor_card (a : Quotient r) :
    Nat.card ((fullCartanClassGraph ds).neighborSet a) = Nat.card (ds false).F + 1 := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep a
  have hraw := Nat.card_congr (Equiv.ofBijective _ (fullCartanClassMap_neighbor_bijective ds hr a))
  change Nat.card ((sourceGraph A).neighborSet a) =
    Nat.card ((fullCartanClassGraph ds).neighborSet (Quotient.mk r a)) at hraw
  rw [← hraw]
  have hcover := Nat.card_congr (Equiv.ofBijective _ ((bOne_tree_cover h).neighbor_bijective a))
  have hnorm (i : Bool) : (B₀ L S).subgroupOf (G₀ L S) ≤
      normalizer ((ds i).data.actor : Set (G₀ L S)) := by
    rw [(ds i).actor_eq]
    exact reduced_borel_normalizes_source_actor h _
  exact hcover.trans (neighbor_card_of_actions (reduced_triple h) (ds false).data (ds true).data
    (hnorm false) (hnorm true) (ds false).dimension ((bOne_tree_cover h).vertex a))

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
