module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneClassCover
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphCycles
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic

/-!
# The actual class quadrangle

In the central r=4 branch the raw graph of the same apartment classes is a
finite generalized quadrangle of the original field order. Short-path
uniqueness gives girth eight, at most one line on two points and the unique
projection of a point to a nonincident line. The source apartment gives an
eight-cycle through every class; local bijectivity retains every panel size.

The cover and its literal quotient map are supplied by `Assembly.BOneClassCover`.
Midpoint-root descent and original Borel-image signs have their separate
source assembly; no such conclusion is required for this raw geometry.

Source: DGS, Groups and Graphs (1985), (3.6), pp.77--78,
(10.5), p.156, and the natural central case of (14.15), p.219.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction Assembly
open SimpleGraph SimpleGraph.Walk
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
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
local notation "Δ" => fullCartanClassGraph ds

private theorem quadrangle_bounded_paths (a b : Quotient r) :
    ∃ p : (Δ).Walk a b, p.IsPath ∧ p.length ≤ n := by
  classical
  obtain ⟨p, hp⟩ := BOneSource.full_profile_class_bounded_walks ds a b
  exact ⟨p.bypass, p.bypass_isPath, p.length_bypass_le_length.trans hp⟩

variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 4 5)

include hr in
/-- Every raw quadrangle cycle has length at least eight. -/
theorem fullCartanClassGraph_cycle_bound_four (a : Quotient r)
    (p : (Δ).Walk a a) (hp : p.IsCycle) : 8 ≤ p.length := by
  have ht := Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))
  have hh := classGraph_cycle_length ht (BOneSource.full_profile_separated ds)
    (BOneSource.full_profile_class_neighbor_lifting ds) p hp
  have hn : n = 4 := (fullCartanProfiles_parameters ds).1.unique hr.1
  omega

include hr in
theorem fullCartanClassGraph_eight_cycle (a : Quotient r) :
    ∃ p : (Δ).Walk a a, p.IsCycle ∧ p.length = 8 := by
  have hn : n = 4 := (fullCartanProfiles_parameters ds).1.unique hr.1
  obtain ⟨p, hp, hl⟩ := BOneSource.full_profile_class_cycle ds a
  exact ⟨p, hp, by omega⟩

include hr in
/-- Two distinct points or lines have at most one common incident vertex. -/
theorem fullCartanClassGraph_common_neighbor_unique_four
    {a b x y : Quotient r} (hab : a ≠ b)
    (hax : (Δ).Adj a x) (hbx : (Δ).Adj b x) (hay : (Δ).Adj a y) (hby : (Δ).Adj b y) : x = y :=
  SimpleGraph.QuadrangleCollinearity.common_vertex_unique
    (fullCartanClassGraph_cycle_bound_four ds hr) hab hax hbx hay hby

include hr in
/-- A point and a nonincident line have a unique three-edge path between them. -/
theorem fullCartanClassGraph_three_path_four {a b : Quotient r}
    (htype : sourceClassType A T n a ≠ sourceClassType A T n b) (hab : ¬ (Δ).Adj a b) :
    ∃ p : (Δ).Walk a b, p.IsPath ∧ p.length = 3 ∧
      ∀ q : (Δ).Walk a b, q.IsPath → q.length = 3 → q = p := by
  obtain ⟨p, hp, hl⟩ := quadrangle_bounded_paths ds a b
  have hn : n = 4 := (fullCartanProfiles_parameters ds).1.unique hr.1
  have heven : ¬ Even p.length := fun he => htype ((sourceClassGraph_even_walk A T n p).mp he)
  have hnot1 : p.length ≠ 1 := by
    intro he
    apply hab
    have hh := p.adj_getVert_succ (by omega : 0 < p.length)
    rw [getVert_zero, show 0+1=p.length by omega, getVert_length] at hh
    exact hh
  rw [Nat.even_iff] at heven
  have hp3 : p.length = 3 := by omega
  refine ⟨p, hp, hp3, ?_⟩
  intro q hq hq3
  exact BOneSource.full_profile_class_short_paths_unique ds q p hq hp (by omega)

include hr in
/-- The point-line projection axiom, and its dual, on the literal source classes. -/
theorem fullCartanClassGraph_projection_four {a b : Quotient r}
    (htype : sourceClassType A T n a ≠ sourceClassType A T n b) (hab : ¬ (Δ).Adj a b) :
    ∃! z, (Δ).Adj z b ∧ ∃ w, (Δ).Adj a w ∧ (Δ).Adj w z := by
  obtain ⟨p, hp, hlen, huniq⟩ := fullCartanClassGraph_three_path_four ds hr htype hab
  have h01 : (Δ).Adj a (p.getVert 1) := by
    simpa only [getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
  have h12 : (Δ).Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega)
  have h23 : (Δ).Adj (p.getVert 2) b := by
    have hh := p.adj_getVert_succ (by omega : 2 < p.length)
    simpa only [show 2+1=p.length from hlen.symm, getVert_length] using hh
  refine ⟨p.getVert 2, ⟨h23, p.getVert 1, h01, h12⟩, ?_⟩
  rintro z ⟨hzb, w, haw, hwz⟩
  let q : (Δ).Walk a b := .cons haw (.cons hwz (.cons hzb .nil))
  have hwne : w ≠ b := fun he => hab (he ▸ haw)
  have haz : a ≠ z := fun he => hab (he.symm ▸ hzb)
  have hane : a ≠ b := fun he => htype (congrArg (sourceClassType A T n) he)
  have hq : q.IsPath := by
    apply ((IsPath.of_adj hzb).cons ?_).cons
    · simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨haw.ne, haz, hane⟩
    · simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hwz.ne, hwne⟩
  have he := huniq q hq rfl
  exact congrArg (fun w => w.getVert 2) he

/-- The complete raw generalized-quadrangle laws, on the literal apartment classes. -/
structure FullCartanClassQuadrangle : Prop where
  finite : Finite (Quotient r)
  connected : (Δ).Connected
  bipartition : ∀ {a b : Quotient r}, (Δ).Adj a b →
    sourceClassType A T n a ≠ sourceClassType A T n b
  diameter : ∀ a b : Quotient r, ∃ p : (Δ).Walk a b, p.IsPath ∧ p.length ≤ 4
  short_paths_unique : ∀ {a b : Quotient r} (p q : (Δ).Walk a b),
    p.IsPath → q.IsPath → p.length < 4 → q.length < 4 → p = q
  cycle_bound : ∀ a (p : (Δ).Walk a a), p.IsCycle → 8 ≤ p.length
  apartment_cycle : ∀ a : Quotient r, ∃ p : (Δ).Walk a a, p.IsCycle ∧ p.length = 8
  valence : ∀ a : Quotient r, Nat.card ((Δ).neighborSet a) = Nat.card (ds false).F + 1
  projection : ∀ {a b : Quotient r},
    sourceClassType A T n a ≠ sourceClassType A T n b → ¬ (Δ).Adj a b →
    ∃! z, (Δ).Adj z b ∧ ∃ w, (Δ).Adj a w ∧ (Δ).Adj w z

include hr in
/-- The original r=4 full-Cartan profiles construct every quadrangle law. -/
theorem fullProfileClassQuadrangle : FullCartanClassQuadrangle ds := by
  have hn : n = 4 := (fullCartanProfiles_parameters ds).1.unique hr.1
  refine ⟨fullCartanClassGraph_finite ds, ((Universal.cosetGraph_isTree A
      (inclusion_injective (commonBorel_le_parabolic 0))
      (inclusion_injective (commonBorel_le_parabolic 1))).connected.map
        (BOneSource.full_profile_class_map ds) Quotient.mk_surjective),
    sourceClassGraph_bipartition A T n, ?_, ?_, fullCartanClassGraph_cycle_bound_four ds hr,
    fullCartanClassGraph_eight_cycle ds hr, BOneSource.full_profile_class_neighbor_card ds,
    fullCartanClassGraph_projection_four ds hr⟩
  · intro a b
    obtain ⟨p, hp, hl⟩ := quadrangle_bounded_paths ds a b
    exact ⟨p, hp, by omega⟩
  · intro a b p q hp hq hl hl'
    exact BOneSource.full_profile_class_short_paths_unique ds p q hp hq (by omega)

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
