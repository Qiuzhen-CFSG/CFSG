module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneUniversal

/-!
# Reflections and path roots from the genuine b=1 actor profiles

The two actual Chapter 10 profiles imply Q=Z. In the nonbinary branch with
trivial actor centers, the actor reflection construction supplies involutions
normalizing the whole compatible Cartan, with the prescribed root conjugacy
and full local-kernel centralization. The earlier source path alternative
then gives four-path transitivity and odd four-path fixers; the actual q+1
neighbor count gives thickness. These reflections therefore construct both
length-three path roots on the original universal tree.

The diagonal, triangular and prescribed root markings remain explicit inputs.
They do not assume a reflection or an exchange conclusion. The selected
reflections and root actions have public behavior lemmas so consumers need
not unfold their choices. The other reflection branches, exchange and quotient
root signs remain separate source obligations; this is not (14.19).

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, the universal
tree convention p.208, and (14.1)--(14.2), pp.210--211.
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

/-- The preceding natural profile and coordinate choices in the nonbinary,
trivial-center branch. The actual reflection is constructed, not supplied. -/
structure ActorReflectionProfile (i : Bool) where
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
  center_eq : centerIn data.actor=⊥
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
  path_length : path.length=3
  root_element : universalBOneActor h i data
  root_mem : (root_element:(reducedAmalgam L S).Universal)∈
    pathRoot (X := (reducedAmalgam L S).Universal) path
  root_square : root_element*root_element=1
  root_parameter : F
  root_ne_zero : root_parameter≠0
  root_image : universalBOneQuotient h i data root_element=upper root_parameter

attribute [instance] ActorReflectionProfile.field ActorReflectionProfile.finite
  ActorReflectionProfile.charTwo ActorReflectionProfile.addGroup ActorReflectionProfile.moduleTwo

variable {h c}

/-- Produce the full source reflection clauses from the earlier marked actor profile. -/
theorem actorProfiles_exists_reflection (d : ∀ i : Bool, ActorReflectionProfile.{uF} h c i) (i : Bool) :
    ∃ t : (reducedAmalgam L S).Universal,
      t∈universalBOneActor h i (d i).data ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (d i).path,
        orderOf y=2 ∧ ∃ g∈universalBOneActor h i (d i).data, g*y*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  have hc := paired_cores_eq_centers_of_actions (reduced_triple h) (d false).data (d true).data
  have hci : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i) := by
    cases i
    · exact hc.1
    · exact hc.2
  exact source_bOne_actor_root_reflection h i (d i).data c (d i).actor_eq hci (d i).center_eq
    (d i).dimension (d i).diagonal (d i).full_diagonal (d i).triangular (d i).diagonal_parameter
    (d i).diagonal_ne_zero (d i).diagonal_ne_one (d i).path (d i).root_element (d i).root_mem
    (d i).root_square (d i).root_parameter (d i).root_ne_zero (d i).root_image

variable (d : ∀ i : Bool, ActorReflectionProfile.{uF} h c i)

/-- The chosen reflection is an element of the actual universal completion. -/
def actorReflections (i : Bool) : (reducedAmalgam L S).Universal :=
  Classical.choose (actorProfiles_exists_reflection d i)

/-- Both reflections fix their original marked endpoint. -/
theorem actorReflections_fix (i : Bool) :
    actorReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) i=
      base (Universal.cosetFamily (reducedAmalgam L S)) i :=
  (Classical.choose_spec (actorProfiles_exists_reflection d i)).2.1

/-- Both reflections move the opposite original marked endpoint. -/
theorem actorReflections_move (i : Bool) :
    actorReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  (Classical.choose_spec (actorProfiles_exists_reflection d i)).2.2.1

/-- The lifts are actual involutions. -/
theorem actorReflections_square (i : Bool) : actorReflections d i*actorReflections d i=1 :=
  (Classical.choose_spec (actorProfiles_exists_reflection d i)).2.2.2.1

/-- The whole compatible Cartan is normalized, including its part outside the actor. -/
theorem actorReflections_normalize (i : Bool) :
    actorReflections d i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) :=
  (Classical.choose_spec (actorProfiles_exists_reflection d i)).2.2.2.2.1

/-- Source (14.2)'s extra path-root conjugacy and full-kernel clause remain
available on the same selected reflections used by the quotient construction. -/
theorem actorReflections_source_clauses (i : Bool) :
    actorReflections d i∈universalBOneActor h i (d i).data ∧
    (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) (d i).path,
      orderOf y=2 ∧ ∃ g∈universalBOneActor h i (d i).data,
        g*y*g⁻¹=actorReflections d i) ∧
    ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
      (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute (actorReflections d i) z :=
  ⟨(Classical.choose_spec (actorProfiles_exists_reflection d i)).1,
    (Classical.choose_spec (actorProfiles_exists_reflection d i)).2.2.2.2.2⟩

include d in
/-- The literal Chapter 10 alternative supplies four-path transitivity and
odd four-path stabilizers. Trivial actor centers exclude the five-path branch. -/
theorem actorProfiles_path_data :
    BasedPathTransitive (X := (reducedAmalgam L S).Universal)
      (sourceGraph (reducedAmalgam L S)) 4 ∧
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=4 → Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) := by
  rcases original_bOne_tree_path_alternatives h (d false).data (d true).data
    (d false).actor_eq (d true).actor_eq (d false).dimension (d true).dimension with
    ⟨_,_,_,ht,ho⟩ | ⟨hc,_,_,_,_⟩
  · exact ⟨ht,ho⟩
  · have he : Nat.card (centerIn ((d false).data.actor.map (G₀ L S).subtype))=1 := by
      rw [←reduced_actor_center_map,(d false).center_eq,Subgroup.map_bot]
      simp
    have hgt : 1<Nat.card (d false).F := Finite.one_lt_card
    omega

private theorem actorProfiles_normalized (i : Bool) :
    (B₀ L S).subgroupOf (G₀ L S)≤normalizer ((d i).data.actor : Set (G₀ L S)) := by
  rw [(d i).actor_eq]
  exact reduced_borel_normalizes_source_actor h _

include d in
/-- The original q+1 neighbor count proves thickness of the actual universal
tree, for any two forbidden neighbors and in particular the chosen reflections. -/
theorem actorProfiles_tree_thick (v a b : SourceVertex (reducedAmalgam L S)) :
    ∃ z, (sourceGraph (reducedAmalgam L S)).Adj v z ∧ z≠a ∧ z≠b := by
  have hc := Nat.card_congr (Equiv.ofBijective _ ((bOne_tree_cover h).neighbor_bijective v))
  have hv := neighbor_card_of_actions (reduced_triple h) (d false).data (d true).data
    (actorProfiles_normalized d false) (actorProfiles_normalized d true) (d false).dimension
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

local notation "n" => (3 : ℕ)
local notation "hn" => (Nat.succ_lt_succ (Nat.zero_lt_succ 1))
include d in
/-- Four-path transitivity on the actual universal tree. -/
theorem actorProfiles_path_transitive : BasedPathTransitive
    (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) 4 :=
  (actorProfiles_path_data d).1

include d in
/-- Actual four-path fixers have odd order. -/
theorem actorProfiles_path_odd :
    ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b),
      p.IsPath → p.length=4 → Odd (Nat.card (pathFixer (X := (reducedAmalgam L S).Universal) p)) :=
  (actorProfiles_path_data d).2

local notation "htrans" => actorProfiles_path_transitive d
local notation "hodd" => actorProfiles_path_odd d
/-- Thickness at the two marked endpoints for the chosen reflections. -/
theorem actorProfiles_thickness : ∀ i, ∃ z,
    (sourceGraph (reducedAmalgam L S)).Adj (base (Universal.cosetFamily (reducedAmalgam L S)) i) z ∧
    z≠base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
    z≠actorReflections d i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  fun _ => actorProfiles_tree_thick d _ _ _
local notation "hthick" => actorProfiles_thickness d

/-- Feed the actor-selected reflections into the literal long-path radical
construction at both original universal endpoints. -/
def actorReflectionPathRoots : Bool → LocalRootAction
    (X := (reducedAmalgam L S).Universal) (sourceGraph (reducedAmalgam L S)) :=
  pathRoots h c n hn (actorReflections d) (actorReflections_fix d)
    (actorReflections_move d) (actorReflections_square d) (actorReflections_normalize d)
    htrans hthick

/-- The constructed roots retain the marked base vertices. -/
theorem actorRoots_a (i : Bool) : (actorReflectionPathRoots d i).a=
    base (Universal.cosetFamily (reducedAmalgam L S)) i :=
  pathRoots_a h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

/-- The constructed roots retain the opposite marked vertices. -/
theorem actorRoots_b (i : Bool) : (actorReflectionPathRoots d i).b=
    base (Universal.cosetFamily (reducedAmalgam L S)) (!i) :=
  pathRoots_b h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

/-- The root reflections normalize the whole original Cartan. -/
theorem actorRoots_normalizes (i : Bool) : (actorReflectionPathRoots d i).reflection∈
    normalizer (cartan c : Set (reducedAmalgam L S).Universal) :=
  pathRoots_normalizes h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

/-- The same root reflections are involutions. -/
theorem actorRoots_square (i : Bool) :
    (actorReflectionPathRoots d i).reflection*(actorReflectionPathRoots d i).reflection=1 :=
  pathRoots_square h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

/-- The roots use the very reflections carrying the source conjugacy and
full local-kernel clauses. -/
theorem actorRoots_reflection (i : Bool) :
    (actorReflectionPathRoots d i).reflection=actorReflections d i :=
  pathRoots_reflection h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

/-- Each root is O₂ of the stabilizer of its constructed length-three path
in this same reflection apartment. -/
theorem actorRoots_root (i : Bool) :
    (actorReflectionPathRoots d i).root=
      (pathFixer (X := (reducedAmalgam L S).Universal)
        (reflectionPath c (actorReflections d) (actorReflections_fix d)
          (actorReflections_move d) (actorReflections_normalize d) 3
          (Nat.zero_lt_succ 2) i).walk).pCoreIn 2 :=
  pathRoots_root h c n hn (actorReflections d) (actorReflections_fix d) (actorReflections_move d)
    (actorReflections_square d) (actorReflections_normalize d) htrans hthick i

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
