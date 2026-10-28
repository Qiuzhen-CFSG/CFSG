module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound.Base

/-!
# An invariant graph on the fixed HS permutation carrier

The rows were obtained by an orbit search starting at the ordered pair
`(0, 4)` under the two published ATLAS permutations. Here we check
symmetry, absence of loops, degree 22 and invariance under the generators
on all letters in Lean's kernel, and hence invariance under the carrier.

This graph is a concrete tool for the permutation-normalizer calculation
associated with GLS3, Table 5.3m, p.274, which records the degree-100 rank-three
action. We do not assume that description, the graph automorphism order,
or the outer-automorphism table. In particular `generated_le_graphGroup`
does not yet assert that the permutation normalizer preserves this graph.

The orbit search and the action convention are recorded in `source/` and
`HS.lean`, respectively. Python supplies data only; no search result is a
proof premise.
-/

@[expose] public section

namespace Sporadic.LeechRelated.HS.NormalizerIndex
open OrderCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- Binary adjacency rows, with zero-based vertices. -/
def adjacencyRows : List ℕ :=
  [2475883841712904294484680464,
   14828824120736458556442624,
   119463971653212368922837254992,
   255489624933165404331437721088,
   168452333213791229065645277189,
   321871668528521859413616674688,
   319785072580303994501373406212,
   3181996944457063544268263456,
   643893471052268318873721905189,
   21162265952791651495096549421,
   634465936658436631831127261289,
   95982892455106990316005113923,
   89600184714441645891270025345,
   5614270553378333269650837824,
   636765474558526932844481153072,
   168515796857800594382242578528,
   317541744859699343335080088064,
   82633146265160999949977289474,
   951979970926548910768402866328,
   1245817430824984858054426952,
   675296292759862873975177613434,
   475703545338450715101929409408,
   429530231371259547069972736,
   792286840112170637991142756928,
   19923176607184941447912412166,
   39633433595685762421649254456,
   124422650080141868184288149505,
   633830746924023296366454343820,
   19961839839308548549384601665,
   14914671399393546681416564868,
   1215238065986742721208332,
   50845004482823762532465009664,
   257646950701684306342524026979,
   80196891659454590346857021488,
   474524798864517940027590692,
   125382534968889818943984862610,
   93474900708156013717785411616,
   643886776660785730413689569986,
   1114611476530218004590774190215,
   848013105427562398428363423937,
   99074380504671758029942194305,
   10026916340794875601914889216,
   958804139357967269871101710866,
   326527256026888550829451641104,
   278855967806439301395007938593,
   642500724605381661353272446980,
   38846736649948620811931694,
   5324213540640401377339998213,
   10547350091175368552926691904,
   337977729176900059080823988367,
   50581503544371352632501731363,
   11494468668251256353913308292,
   673519222716523193982016135179,
   12398941969671060172745744896,
   673768552748973852270499768976,
   317613227301143351448586699018,
   79241387803668435562675626496,
   806307057433688990651550605350,
   245113341796224970835553747200,
   317379380468971651838928496146,
   22380298265775659264911968512,
   498967207103000825357865587970,
   646902294977721231484656287744,
   102749100626368433450196771856,
   638935526364457517084867493968,
   831983053661238028872987580448,
   952999643186138894348513738753,
   495274316494861882105181921281,
   336874433781348095506655087760,
   203041511999871635290339955522,
   322031421441231760272882008065,
   317536470594101134278380224521,
   21103559267828670254716948592,
   258731587373194980361634857408,
   287202095110553153972214457986,
   481573257955509288257735250948,
   39614124008254621975519955336,
   198462104154255826424137321728,
   17485917480349952716669518854,
   44604536560427267800527672336,
   39628597982801276210394734080,
   180758589822293748403988600868,
   101667225981763678981937700914,
   19866317064003259803486978522,
   79394999738933585334920807424,
   1111835178375018958759401630208,
   84334816558554626306152071888,
   41611530437353171007517544712,
   19807191818822648021261635656,
   178418110601624785311344307332,
   154794536405167606844885504,
   39660322687467652142520746185,
   19885358143940590096185567272,
   336720011811312740446513436952,
   689240056456114079841218724352,
   339352372848104359604754841604,
   950839528283802256005847455756,
   660291503869257623437082648,
   128784491552041684873871949920,
   99073888902963658390762702080]

/-- The explicitly checked orbital relation. -/
def adjacency (x y : Fin 100) : Prop :=
  (adjacencyRows[x.val]! >>> y.val) % 2 = 1

instance adjacencyDecidable : DecidableRel adjacency := fun x y => inferInstanceAs (Decidable ((adjacencyRows[x.val]! >>> y.val) % 2 = 1))

theorem adjacency_irrefl (x : Fin 100) : ¬ adjacency x x := by
  have h : ∀ x : Fin 100, ¬ adjacency x x := by
    apply allFin
    decide +kernel
  exact h x

theorem adjacency_symm (x y : Fin 100) : adjacency x y ↔ adjacency y x := by
  have h : ∀ x y : Fin 100, adjacency x y ↔ adjacency y x := by
    apply allFin
    decide +kernel
  exact h x y

/-- All permutations preserving the explicit adjacency relation. -/
def graphGroup : Subgroup (Equiv.Perm (Fin 100)) where
  carrier := {g | ∀ x y, adjacency (g x) (g y) ↔ adjacency x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro g h hg hh x y
    exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using
      (hg (g⁻¹ x) (g⁻¹ y)).symm

theorem mem_graphGroup_iff (g : Equiv.Perm (Fin 100)) :
    g ∈ graphGroup ↔ ∀ x y, adjacency (g x) (g y) ↔ adjacency x y := Iff.rfl

theorem generatorA_mem_graphGroup : generatorA ∈ graphGroup := by
  rw [mem_graphGroup_iff, ← a_eq_generator]
  apply allFin
  decide +kernel

theorem generatorB_mem_graphGroup : generatorB ∈ graphGroup := by
  rw [mem_graphGroup_iff, ← b_eq_generator]
  apply allFin
  decide +kernel

/-- The defining HS subgroup acts by graph automorphisms. -/
theorem generated_le_graphGroup : generated ≤ graphGroup := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases Set.mem_insert_iff.mp hg with hg | hg
  · exact hg ▸ generatorA_mem_graphGroup
  · exact (Set.mem_singleton_iff.mp hg) ▸ generatorB_mem_graphGroup

/-- The neighbors of a vertex in the explicit graph. -/
def neighbors (x : Fin 100) : Finset (Fin 100) :=
  Finset.univ.filter (adjacency x)

@[simp] theorem mem_neighbors (x y : Fin 100) : y ∈ neighbors x ↔ adjacency x y := by
  simp [neighbors]

/-- Every vertex has exactly 22 neighbors. -/
theorem neighbors_card (x : Fin 100) : (neighbors x).card = 22 := by
  have h : ∀ x : Fin 100, (neighbors x).card = 22 := by
    apply allFin
    decide +kernel
  exact h x

/-- The distinct nonadjacent vertices. -/
def nonneighbors (x : Fin 100) : Finset (Fin 100) :=
  Finset.univ.filter (fun y => y ≠ x ∧ ¬ adjacency x y)

@[simp] theorem mem_nonneighbors (x y : Fin 100) :
    y ∈ nonneighbors x ↔ y ≠ x ∧ ¬ adjacency x y := by
  simp [nonneighbors]

/-- Every vertex has exactly 77 distinct nonneighbors. -/
theorem nonneighbors_card (x : Fin 100) : (nonneighbors x).card = 77 := by
  have h : ∀ x : Fin 100, (nonneighbors x).card = 77 := by
    apply allFin
    decide +kernel
  exact h x

end Sporadic.LeechRelated.HS.NormalizerIndex
