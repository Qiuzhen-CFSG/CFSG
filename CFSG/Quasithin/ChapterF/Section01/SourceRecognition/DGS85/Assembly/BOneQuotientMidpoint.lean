module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneClassCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneMidpointCover

/-!
# Midpoint symmetries on the actual finite quotient

The full four-edge root fixes the radius-two ball about its midpoint class,
even when that class is represented by a different universal vertex. The
proof uses the constructed local cover and the original full midpoint root,
not an assumed equality between classes and kernel orbits. The quotient
preserves the root's full order q in the central branch.

This supplies the source symmetries needed for uniqueness of a root image at
a quotient midpoint. Such uniqueness and the Borel-image root signs remain
separate steps. BOneQuotientMidpointConsumers applies these results to the
original critical pair and Chapter 12 selected pair, retaining both branches.
Source: DGS, Groups and Graphs (1985), (3.6)--(3.7), pp.77--80,
(10.5), p.156 and (14.1)--(14.2), pp.210--211.
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
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "n" => fullCartanPathLength ds
local notation "T" => cartanApartment A (apartmentGroup c (fullCartanPathRoots ds))
local notation "r" => sourceRelation A T n
local notation "q" => quotientMap A T n
local notation "hrInv" => apartmentSetoid_invariant (source_action A)

/-- The full root image fixes the quotient ball at any representative of
its midpoint class, not just the original universal midpoint. -/
theorem four_path_root_fixes_class_ball {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4)
    (v : SourceVertex A) (hv : r (p.getVert 2) v) :
    (pathRoot (X := (reducedAmalgam L S).Universal) p).map q ≤
      classBallFixer (sourceGraph A) r hrInv (Quotient.mk r v) 2 := by
  rw [←Quotient.sound hv]
  exact (Subgroup.map_mono (four_path_root_fixes_ball_two ds p hp hlen)).trans
    (full_profile_class_ball_image ds (p.getVert 2) 2).le |>.trans inf_le_left

private theorem path_root_map_card {Y : Type*} [Group Y] (f : (reducedAmalgam L S).Universal →* Y)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b)
    (hi : Function.Injective (fun g : RankTwo.stabilizer (Universal.cosetFamily A) a => f g)) :
    Nat.card ((pathRoot (X := (reducedAmalgam L S).Universal) p).map f)=Nat.card (pathRoot (X := (reducedAmalgam L S).Universal) p) := by
  let R := pathRoot (X := (reducedAmalgam L S).Universal) p
  let φ := f.comp R.subtype
  have hf : Function.Injective φ := by
    intro x y he
    have hx : (x:(reducedAmalgam L S).Universal) • a=a := by
      simpa only [SimpleGraph.Walk.getVert_zero] using (pCoreIn_le 2 _ x.property) 0 (Nat.zero_le _)
    have hy : (y:(reducedAmalgam L S).Universal) • a=a := by
      simpa only [SimpleGraph.Walk.getVert_zero] using (pCoreIn_le 2 _ y.property) 0 (Nat.zero_le _)
    have heq := hi (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) he
    exact Subtype.ext (congrArg (fun z : RankTwo.stabilizer (Universal.cosetFamily A) a =>
      (z : (reducedAmalgam L S).Universal)) heq)
  have he := Nat.card_range_of_injective hf
  change Nat.card φ.range=Nat.card R at he
  simpa only [φ,MonoidHom.range_comp,range_subtype] using he

/-- The faithful geometric quotient preserves every path root's order. -/
theorem path_root_quotient_card {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) :
    Nat.card ((pathRoot (X := (reducedAmalgam L S).Universal) p).map q)=Nat.card (pathRoot (X := (reducedAmalgam L S).Universal) p) := by
  let : FaithfulSMul (reducedAmalgam L S).Universal (SourceVertex A) := by
    apply Subgroup.CosetGeometry.faithful_of_core_free
    simpa only [iInf_bool_eq,Universal.cosetFamily,Bool.false_eq_true,
      Bool.cond_false,Bool.cond_true,inf_comm] using original_core_eq_bot h
  apply path_root_map_card q p
  exact quotient_injective_on_stabilizer hrInv
    (Universal.cosetGraph_isTree A (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).connected
    (source_action A) (full_profile_separated ds) (by have := fullCartanPathLength_gt ds; omega) a

private theorem original_midpoint_center_card
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5)
    (i : Bool) : Nat.card (centerIn (BOneMidpoint.actor (ds false).data (ds true).data i)) =
      Nat.card (ds i).F := by
  rcases original_bOne_tree_path_alternatives h (ds false).data (ds true).data
    (ds false).actor_eq (ds true).actor_eq (ds false).dimension (ds true).dimension with
    ⟨_,_,hp,_,_⟩ | ⟨hc₀,hc₁,_,_,_⟩
  · have he := hr.1.unique hp.1
    omega
  · rw [←reduced_actor_center_map,card_map_of_injective (G₀ L S).subtype_injective] at hc₀ hc₁
    cases i
    · exact hc₀
    · exact hc₁

/-- Every four-edge quotient root has the full original midpoint field order. -/
theorem four_path_root_quotient_card
    (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : p.length=4)
    (i : Bool) (g : G₀ L S)
    (hm : g • base (reducedFamily L S) i=(bOne_tree_cover h).vertex (p.getVert 2)) :
    Nat.card ((pathRoot (X := (reducedAmalgam L S).Universal) p).map q)=Nat.card (ds i).F := by
  rw [path_root_quotient_card]
  have hi : Function.Injective (fun x : RankTwo.stabilizer (Universal.cosetFamily A) a =>
      bOne_tree_map h x) := by
    intro x y he
    exact ((bOne_tree_cover h).stabilizerHom_bijective a).1 (Subtype.ext he)
  rw [←path_root_map_card (bOne_tree_map h) p hi,
    four_path_root_original_center ds p hp hlen i g hm,
    card_map_of_injective (MulAut.conj g).injective]
  exact original_midpoint_center_card ds hr i

/-- The original quotient has midpoint-root symmetries of the full source size,
with fixation stated for every representative of each midpoint class. -/
def HasQuotientMidpointGeometry : Prop :=
  HasSourceClassPolygon ds ∧ NeighborLifting (sourceGraph A) r ∧
  ∀ {a b : SourceVertex A} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=4 →
    (∀ v : SourceVertex A, r (p.getVert 2) v →
      (pathRoot (X := (reducedAmalgam L S).Universal) p).map q ≤
        classBallFixer (sourceGraph A) r hrInv (Quotient.mk r v) 2) ∧
    (HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5 →
      ∀ (i : Bool) (g : G₀ L S),
        g • base (reducedFamily L S) i=(bOne_tree_cover h).vertex (p.getVert 2) →
        Nat.card ((pathRoot (X := (reducedAmalgam L S).Universal) p).map q)=Nat.card (ds i).F)

/-- Both original full profiles construct the quotient midpoint geometry. -/
theorem full_profile_quotient_midpoint_geometry : HasQuotientMidpointGeometry ds := by
  refine ⟨full_profile_source_class_polygon ds,full_profile_class_neighbor_lifting ds,?_⟩
  intro a b p hp hl
  exact ⟨four_path_root_fixes_class_ball ds p hp hl,
    fun hr => four_path_root_quotient_card ds hr p hp hl⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
