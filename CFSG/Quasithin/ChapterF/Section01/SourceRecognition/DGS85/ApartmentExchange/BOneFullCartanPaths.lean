module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartan

/-!
# The natural source path alternative with whole-Cartan reflections

The paired Chapter 10 actions give Q=Z and the genuine alternative between
regularity lengths three and four. Whole-Cartan correction constructs both
marked reflections even when the actor centers are nontrivial. The actual
universal covering and q+1 neighbor count give thickness; the same source
alternative gives transitivity and odd fixers at the chosen next length.
These data construct both actual path radicals in their reflection apartment.

The nonbinary coordinate markings remain explicit. The selected reflections
retain the central factor in their original-root conjugacy formula. No claim
that this factor lies in that root is made. The source exchange argument,
its corrected (14.14) branch, and quotient root signs remain to be proved.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
universal-tree construction (14.0)--(14.2), pp.208--211.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S))

/-- The preceding natural data and coordinate choices in the nonbinary
branch, with arbitrary actor center. The whole-Cartan reflection is constructed. -/
structure FullCartanReflectionProfile (i : Bool) where
  F : Type uF
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  W : Type uF
  [addGroup : AddCommGroup W]
  [moduleTwo : Module (ZMod 2) W]
  data : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
    (base (reducedFamily L S) (!i)) F W
  actor_eq : data.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)
  dimension : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
    W ≃ₗ[ZMod 2] (Fin 2 → F)
  diagonal : ∀ k : universalBOneActor h i data, (k:(reducedAmalgam L S).Universal)∈cartan c →
    ∃ a : F, ∃ ha : a≠0, universalBOneQuotient h i data k=Matrix.SpecialLinearGroup.diag2 a ha
  full_diagonal : ∀ a : F, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
    ((cartan c).subgroupOf (universalBOneActor h i data)).map (universalBOneQuotient h i data)
  triangular : ∀ k : data.actor, (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
    (base (reducedFamily L S) (!i)) → (data.quotient k).val 1 0=0
  diagonal_parameter : F
  diagonal_ne_zero : diagonal_parameter≠0
  diagonal_ne_one : diagonal_parameter≠1
  start : SourceVertex (reducedAmalgam L S)
  path : (sourceGraph (reducedAmalgam L S)).Walk start
    (base (Universal.cosetFamily (reducedAmalgam L S)) i)
  path_isPath : path.IsPath
  root_element : universalBOneActor h i data
  root_mem : (root_element:(reducedAmalgam L S).Universal)∈
    pathRoot (X := (reducedAmalgam L S).Universal) path
  root_square : root_element*root_element=1
  root_parameter : F
  root_ne_zero : root_parameter≠0
  root_image : universalBOneQuotient h i data root_element=upper root_parameter

attribute [instance] FullCartanReflectionProfile.field FullCartanReflectionProfile.finite
  FullCartanReflectionProfile.charTwo FullCartanReflectionProfile.addGroup FullCartanReflectionProfile.moduleTwo

variable {h c}

/-- Construct whole-Cartan reflections with their explicit central defect. -/
theorem fullCartanProfiles_exists_reflection (d : ∀ i : Bool, FullCartanReflectionProfile.{uF} h c i) (i : Bool) :
    ∃ t : (reducedAmalgam L S).Universal,
      t∈universalBOneActor h i (d i).data ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ orderOf t=2 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (d i).path,
        orderOf y=2 ∧ ∃ z∈centerIn (universalBOneActor h i (d i).data),
          bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
          ∃ g∈universalBOneActor h i (d i).data, g*(z*y)*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (d false).data (d true).data
  have hci : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i) := by
    cases i
    · exact hc.1
    · exact hc.2
  exact source_bOne_full_cartan_reflection h i (d i).data c (d i).actor_eq hci
    (d i).dimension (d i).diagonal (d i).full_diagonal (d i).triangular (d i).diagonal_parameter
    (d i).diagonal_ne_zero (d i).diagonal_ne_one (d i).path (d i).root_element (d i).root_mem
    (d i).root_square (d i).root_parameter (d i).root_ne_zero (d i).root_image

variable (d : ∀ i : Bool, FullCartanReflectionProfile.{uF} h c i)

/-- The chosen reflection is an element of the actual universal completion. -/
def fullCartanReflections (i : Bool) : (reducedAmalgam L S).Universal :=
  Classical.choose (fullCartanProfiles_exists_reflection d i)

/-- Both reflections fix their original marked endpoint. -/
theorem fullCartanReflections_fix (i : Bool) :
    fullCartanReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) i=
      base (Universal.cosetFamily (reducedAmalgam L S)) i :=
  (Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).2.1

/-- Both reflections move the opposite original marked endpoint. -/
theorem fullCartanReflections_move (i : Bool) :
    fullCartanReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  (Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).2.2.1

/-- The lifts are actual involutions. -/
theorem fullCartanReflections_square (i : Bool) : fullCartanReflections d i*fullCartanReflections d i=1 :=
  (Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).2.2.2.1

/-- The whole compatible Cartan is normalized, including its part outside the actor. -/
theorem fullCartanReflections_normalize (i : Bool) :
    fullCartanReflections d i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) :=
  (Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).2.2.2.2.2.1

/-- The selected reflections retain the exact central defect and the
full-kernel Cartan centralization clause. -/
theorem fullCartanReflections_source_clauses (i : Bool) :
    fullCartanReflections d i∈universalBOneActor h i (d i).data ∧
    (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (d i).path,
      orderOf y=2 ∧ ∃ z∈centerIn (universalBOneActor h i (d i).data),
        bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
        ∃ g∈universalBOneActor h i (d i).data,
          g*(z*y)*g⁻¹=fullCartanReflections d i) ∧
    ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute (fullCartanReflections d i) z :=
  ⟨(Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).1,
    (Classical.choose_spec (fullCartanProfiles_exists_reflection d i)).2.2.2.2.2.2⟩

include d in
/-- Retain both actual source path alternatives, including the nontrivial
center case with regularity length four. -/
theorem fullCartanProfiles_path_data :
    ∃ n : ℕ, (n=3 ∨ n=4) ∧
      HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) n (n+1) ∧
      BasedPathTransitive (X := (reducedAmalgam L S).Universal)
        (sourceGraph (reducedAmalgam L S)) (n+1) ∧
      ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
        p.IsPath → p.length=n+1 →
          Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  rcases original_bOne_tree_path_alternatives h (d false).data (d true).data
    (d false).actor_eq (d true).actor_eq (d false).dimension (d true).dimension with
    ⟨_,_,hp,ht,ho⟩ | ⟨_,_,hp,ht,ho⟩
  · exact ⟨3,Or.inl rfl,hp,ht,ho⟩
  · exact ⟨4,Or.inr rfl,hp,ht,ho⟩

/-- The regularity length chosen from the genuine earlier source alternative. -/
def fullCartanPathLength : ℕ := Classical.choose (fullCartanProfiles_path_data d)

/-- Both source lengths are retained. -/
theorem fullCartanPathLength_cases : fullCartanPathLength d=3 ∨ fullCartanPathLength d=4 :=
  (Classical.choose_spec (fullCartanProfiles_path_data d)).1

/-- The chosen length is the actual earlier source parameter, with s=r+1. -/
theorem fullCartanProfiles_parameters :
    HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S))
      (fullCartanPathLength d) (fullCartanPathLength d+1) :=
  (Classical.choose_spec (fullCartanProfiles_path_data d)).2.1

/-- The actual length is long enough for the geometric quotient construction. -/
theorem fullCartanPathLength_gt : 1<fullCartanPathLength d := by
  rcases fullCartanPathLength_cases d with he | he <;> omega

private theorem fullCartanProfiles_normalized (i : Bool) :
    (B₀ L S).subgroupOf (G₀ L S)≤normalizer ((d i).data.actor : Set (G₀ L S)) := by
  rw [(d i).actor_eq]
  exact reduced_borel_normalizes_source_actor h _

include d in
/-- The original q+1 neighbor count proves thickness of the actual universal
tree, for any two forbidden neighbors and in particular the chosen reflections. -/
theorem fullCartanProfiles_tree_thick (v a b : SourceVertex (reducedAmalgam L S)) :
    ∃ z, (sourceGraph (reducedAmalgam L S)).Adj v z ∧ z≠a ∧ z≠b := by
  have hc := Nat.card_congr (Equiv.ofBijective _ ((bOne_tree_cover h).neighbor_bijective v))
  have hv := neighbor_card_of_actions (reduced_triple h) (d false).data (d true).data
    (fullCartanProfiles_normalized d false) (fullCartanProfiles_normalized d true) (d false).dimension
    ((bOne_tree_cover h).vertex v)
  have hcount : Nat.card ((sourceGraph (reducedAmalgam L S)).neighborSet v)=Nat.card (d false).F+1 :=
    hc.trans hv
  have hpair : ({a,b} : Set (SourceVertex (reducedAmalgam L S))).ncard≤2 := by
    simpa using Set.ncard_insert_le a ({b} : Set (SourceVertex (reducedAmalgam L S)))
  have hgt : ({a,b} : Set (SourceVertex (reducedAmalgam L S))).ncard<
      ((sourceGraph (reducedAmalgam L S)).neighborSet v).ncard := by
    rw [Nat.card_coe_set_eq] at hcount
    rw [hcount]
    have : 1<Nat.card (d false).F := Finite.one_lt_card
    omega
  obtain ⟨z,hz,hne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hgt
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hne
  exact ⟨z,hz,hne⟩

local notation "n" => fullCartanPathLength d
local notation "hn" => fullCartanPathLength_gt d
include d in
/-- Transitivity at the chosen next length on the actual universal tree. -/
theorem fullCartanProfiles_path_transitive : BasedPathTransitive
    (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) (n+1) :=
  (Classical.choose_spec (fullCartanProfiles_path_data d)).2.2.1

include d in
/-- Actual fixers at the chosen next length have odd order. -/
theorem fullCartanProfiles_path_odd :
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=n+1 → Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) :=
  (Classical.choose_spec (fullCartanProfiles_path_data d)).2.2.2

local notation "htrans" => fullCartanProfiles_path_transitive d
local notation "hodd" => fullCartanProfiles_path_odd d
/-- Thickness at the two marked endpoints for the chosen reflections. -/
theorem fullCartanProfiles_thickness : ∀ i, ∃ z,
    (sourceGraph (reducedAmalgam L S)).Adj (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
    z≠base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
    z≠fullCartanReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  fun _ => fullCartanProfiles_tree_thick d _ _ _
local notation "hthick" => fullCartanProfiles_thickness d

/-- Feed the actor-selected reflections into the literal long-path radical
construction at both original universal endpoints. -/
def fullCartanPathRoots : Bool → LocalRootAction
    (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) :=
  pathRoots h c n hn (fullCartanReflections d) (fullCartanReflections_fix d)
    (fullCartanReflections_move d) (fullCartanReflections_square d) (fullCartanReflections_normalize d)
    htrans hthick

/-- The constructed roots retain the marked base vertices. -/
theorem fullCartanRoots_a (i : Bool) : (fullCartanPathRoots d i).a=
    base (Universal.cosetFamily (reducedAmalgam L S)) i :=
  pathRoots_a h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

/-- The constructed roots retain the opposite marked vertices. -/
theorem fullCartanRoots_b (i : Bool) : (fullCartanPathRoots d i).b=
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  pathRoots_b h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

/-- The root reflections normalize the whole original Cartan. -/
theorem fullCartanRoots_normalizes (i : Bool) : (fullCartanPathRoots d i).reflection∈
    normalizer (cartan c : Set (reducedAmalgam L S).Universal) :=
  pathRoots_normalizes h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

/-- The same root reflections are involutions. -/
theorem fullCartanRoots_square (i : Bool) :
    (fullCartanPathRoots d i).reflection*(fullCartanPathRoots d i).reflection=1 :=
  pathRoots_square h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

/-- The roots use the same reflections, with their central defect and
full local-kernel clauses retained. -/
theorem fullCartanRoots_reflection (i : Bool) :
    (fullCartanPathRoots d i).reflection=fullCartanReflections d i :=
  pathRoots_reflection h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

/-- Each root is O₂ of the stabilizer of its constructed path
in this same reflection apartment. -/
theorem fullCartanRoots_root (i : Bool) :
    (fullCartanPathRoots d i).root=
      (pathFixer (X := (reducedAmalgam L S).Universal)
        (reflectionPath c (fullCartanReflections d) (fullCartanReflections_fix d)
          (fullCartanReflections_move d) (fullCartanReflections_normalize d) n
          (Nat.zero_lt_of_lt hn) i).walk).pCoreIn 2 :=
  pathRoots_root h c n hn (fullCartanReflections d) (fullCartanReflections_fix d) (fullCartanReflections_move d)
    (fullCartanReflections_square d) (fullCartanReflections_normalize d) htrans hthick i

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
