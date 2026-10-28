module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneCentralCompletion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassGeometry
public import Theory.GroupTheory.WeakBNPair.RegularTree.ApartmentNeighborLiftingGeneral
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphBalls

/-!
# The literal quotient cover in both natural source branches

Source exchange now lifts neighbors for both original path lengths, three
and four. Separation gives local bijectivity on the same quotient classes
used by the faithful finite completion. The raw graph has the original
field valence, diameter at most n, unique paths shorter than n and a cycle
of length 2n through every vertex. Thus the central branch supplies the
actual generalized quadrangle without a Borel-image or Tits-system premise.

BOneQuotientMidpoint applies this cover to the full midpoint root groups.
Source: DGS, Groups and Graphs (1985), (3.6), pp.77--78, (10.5), p.156.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open SimpleGraph SimpleGraph.Walk
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
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
local notation "Γ" => fullCartanClassGraph ds

private theorem class_cover_tree : (sourceGraph A).IsTree :=
  Universal.cosetGraph_isTree A (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))

private theorem class_cover_degree : TwoNeighborsIn (sourceGraph A) T :=
  cartanApartment_twoNeighbors A N ρ (fullCartanRoots_a ds) (fullCartanRoots_b ds)
    (reflection_mem_apartmentGroup c ρ)

/-- Neighbor lifting through every source identification, also in the
central four-edge branch. -/
theorem full_profile_class_neighbor_lifting : NeighborLifting (sourceGraph A) r :=
  apartmentSetoid_neighbor_lift n (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds))
    (class_cover_tree (L := L) (S := S)) (source_action A) (class_cover_degree ds)
    (fullCartanProfiles_path_transitive ds)
    (apartmentExchangeMoves_of_chosen (source_action A) (full_profile_source_exchange ds))

/-- The same raw class map, with no restriction to the three-edge case. -/
abbrev full_profile_class_map : sourceGraph A →g Γ :=
  classGraphMap (full_profile_separated ds) (by have := fullCartanPathLength_gt ds; omega)

/-- Both natural source branches give a locally bijective quotient graph. -/
theorem full_profile_class_map_neighbor_bijective (a : SourceVertex A) :
    Function.Bijective ((full_profile_class_map ds).mapNeighborSet a) :=
  classGraph_neighbor_bijective (class_cover_tree (L := L) (S := S)).connected
    (full_profile_separated ds) (by have := fullCartanPathLength_gt ds; omega)
    (full_profile_class_neighbor_lifting ds) a

/-- The class graph retains the actual original field valence. -/
theorem full_profile_class_neighbor_card (a : Quotient r) :
    Nat.card ((Γ).neighborSet a) = Nat.card (ds false).F + 1 := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep a
  have hraw := Nat.card_congr (Equiv.ofBijective _
    (full_profile_class_map_neighbor_bijective ds a))
  change Nat.card ((sourceGraph A).neighborSet a) = Nat.card ((Γ).neighborSet (Quotient.mk r a)) at hraw
  rw [←hraw]
  have hcover := Nat.card_congr (Equiv.ofBijective _ ((bOne_tree_cover h).neighbor_bijective a))
  have hnorm (i : Bool) : (B₀ L S).subgroupOf (G₀ L S) ≤
      normalizer ((ds i).data.actor : Set (G₀ L S)) := by
    rw [(ds i).actor_eq]
    exact reduced_borel_normalizes_source_actor h _
  exact hcover.trans (neighbor_card_of_actions (reduced_triple h) (ds false).data (ds true).data
    (hnorm false) (hnorm true) (ds false).dimension ((bOne_tree_cover h).vertex a))

/-- Actual raw walks satisfy the source diameter bound. -/
theorem full_profile_class_bounded_walks (a b : Quotient r) :
    ∃ p : (Γ).Walk a b, p.length ≤ n := by
  have hcover : ApartmentsCover (X := (reducedAmalgam L S).Universal) (sourceGraph A) T (n+1) := source_apartments_cover A T n
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1)) (cartanApartment_base A N)
    (class_cover_degree ds) (fullCartanProfiles_path_transitive ds)
  have hext : ApartmentExtension (X := (reducedAmalgam L S).Universal) (sourceGraph A) T n := apartmentExtension_of_cover (class_cover_tree (L := L) (S := S)).isAcyclic
    (source_action A) (class_cover_degree ds)
    (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) hcover
  exact classGraph_bounded_walks (class_cover_tree (L := L) (S := S)).connected
    (full_profile_separated ds) (by have := fullCartanPathLength_gt ds; omega) n
    (fun a => exists_bounded_representative (sourceGraph A) r a n
      (apartment_shortening (class_cover_tree (L := L) (S := S)).connected hext a)) a b

/-- Short raw paths are unique, with the stronger sum-of-lengths bound. -/
theorem full_profile_class_short_paths_unique {a b : Quotient r}
    (p q : (Γ).Walk a b) (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length+q.length<2*n) : p=q :=
  classGraph_short_paths_unique (class_cover_tree (L := L) (S := S))
    (full_profile_separated ds) (full_profile_class_neighbor_lifting ds) p q hp hq hlen

/-- Every raw class lies on a full apartment cycle. -/
theorem full_profile_class_cycle (a : Quotient r) :
    ∃ p : (Γ).Walk a a, p.IsCycle ∧ p.length=2*n := by
  obtain ⟨a,rfl⟩ := Quotient.exists_rep a
  obtain ⟨g,hg⟩ := source_apartment_orbits A T (cartanApartment_base A N) a
  obtain ⟨b,p,hp,hlen,hpT,_⟩ := path_extension_in_set
    (class_cover_tree (L := L) (S := S)).isAcyclic
    (twoNeighborsIn_translate (source_action A) (class_cover_degree ds) g)
    (.nil : (sourceGraph A).Walk a a) .nil
    (by intro z hz; have he : z=a := List.mem_singleton.mp hz; exact he ▸ hg)
    (Nat.zero_le (2*n))
  exact classGraph_cycle_of_path (full_profile_separated ds)
    (by have := fullCartanPathLength_gt ds; omega) p hp hlen
    (Relation.EqvGen.rel _ _ (apartmentStep_symm ⟨p,hp,hlen,g,hpT⟩))

/-- Exact descent and lift of all balls inside the original stabilizer image. -/
theorem full_profile_class_ball_image (a : SourceVertex A) (k : ℕ) :
    (RankTwo.ballKernel (Universal.cosetFamily A) a k).map (quotientMap A T n) =
      classBallFixer (sourceGraph A) r (apartmentSetoid_invariant (source_action A))
        (Quotient.mk r a) k ⊓
      (RankTwo.stabilizer (Universal.cosetFamily A) a).map (quotientMap A T n) := by
  have he : RankTwo.ballKernel (Universal.cosetFamily A) a k =
      graphBallFixer (X := (reducedAmalgam L S).Universal) (sourceGraph A) a k := by
    ext g
    change (∀ b, (sourceGraph A).edist a b ≤ (k : ℕ∞) → g • b=b) ↔ _
    exact (mem_graphBallFixer (sourceGraph A) a k g).symm
  rw [he]
  exact graphBallFixer_map_eq (apartmentSetoid_invariant (source_action A))
    (full_profile_class_neighbor_lifting ds) (class_cover_tree (L := L) (S := S)).connected
    (source_action A) (full_profile_separated ds) (by have := fullCartanPathLength_gt ds; omega) a k


/-- The complete raw polygon and its local cover, on the SAME classes as
in the faithful finite group quotient. -/
def HasSourceClassPolygon : Prop :=
  Finite (Quotient r) ∧
  (∀ a : SourceVertex A, Function.Bijective ((full_profile_class_map ds).mapNeighborSet a)) ∧
  (∀ a : Quotient r, Nat.card ((Γ).neighborSet a)=Nat.card (ds false).F+1) ∧
  (∀ a b : Quotient r, ∃ p : (Γ).Walk a b, p.length≤n) ∧
  (∀ {a b : Quotient r} (p q : (Γ).Walk a b), p.IsPath → q.IsPath →
    p.length+q.length<2*n → p=q) ∧
  ∀ a : Quotient r, ∃ p : (Γ).Walk a a, p.IsCycle ∧ p.length=2*n

/-- All polygon and cover clauses follow from the original paired profiles. -/
theorem full_profile_source_class_polygon : HasSourceClassPolygon ds :=
  ⟨fullCartanClassGraph_finite ds,full_profile_class_map_neighbor_bijective ds,
    full_profile_class_neighbor_card ds,full_profile_class_bounded_walks ds,
    full_profile_class_short_paths_unique ds,full_profile_class_cycle ds⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
