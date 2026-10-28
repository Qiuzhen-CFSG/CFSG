module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassBorel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeRootSigns

/-!
# Genuine Borel-image root signs from the actual source path radicals

The original covering identifies each universal vertex two-core with the
original one. A path radical is a two-group fixing each interior turn; local
bijectivity preserves the distinct neighbors in that turn. The original
natural-action theorem therefore places its image in the middle core, and
the covering identifies its preimage inside the actual universal stabilizer.

A three-path has an interior line vertex. Its nonidentity radical elements
are consequently conjugate to elements of the original line core and act
as elations on the raw plane. The previously proved geometric signs make
each relevant root conjugate fix the base flag. The elation/Borel comparison
then gives the required signs in the WHOLE ORIGINAL Borel image on the SAME
quotient map. There is no sign, Borel-image, or kernel-orbit lifting premise.

This closes the r=3 root-sign branch for the supplied original full-Cartan
profiles. The binary, central/r=4 and remaining Chapter 14 alternatives
remain separate source obligations.
Source: DGS, *Groups and Graphs* (1985), (10.5), p.156, and (3.7), p.80.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

private theorem cover_core_map {X Y : Type*} [Group X] [Group Y]
    {F : Bool → Subgroup X} {E : Bool → Subgroup Y} {f : X →* Y}
    (cov : RankTwo.CoverData F E f) (v : RankTwo.Vertex F) :
    (Q F v).map f = Q E (cov.vertex v) := by
  let e := cov.stabilizerEquiv v
  change ((pCore 2 (RankTwo.stabilizer F v)).map (RankTwo.stabilizer F v).subtype).map f = _
  rw [Subgroup.map_map]
  have he : f.comp (RankTwo.stabilizer F v).subtype =
      (RankTwo.stabilizer E (cov.vertex v)).subtype.comp e.toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, pCore_map_iso]
  rfl

private theorem cover_mem_core {X Y : Type*} [Group X] [Group Y]
    {F : Bool → Subgroup X} {E : Bool → Subgroup Y} {f : X →* Y}
    (cov : RankTwo.CoverData F E f) (v : RankTwo.Vertex F) (x : X)
    (hx : x ∈ RankTwo.stabilizer F v) (hfx : f x ∈ Q E (cov.vertex v)) : x ∈ Q F v := by
  rw [← cover_core_map cov v] at hfx
  obtain ⟨y, hy, he⟩ := hfx
  have he' : cov.stabilizerEquiv v ⟨y, pCoreIn_le 2 _ hy⟩ = cov.stabilizerEquiv v ⟨x, hx⟩ :=
    Subtype.ext he
  have hyx : y = x := congrArg (fun z : RankTwo.stabilizer F v => (z : X))
    ((cov.stabilizerEquiv v).injective he')
  exact hyx ▸ hy

namespace ReducedCartan
universe uF
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {c : CompatibleCartans L (reducedSylow L S)}
variable (ds : ∀ j : Bool, FullCartanReflectionProfile.{uF} h c j)
local notation "A" => reducedAmalgam L S
local notation "UX" => RankTwoAmalgam.Universal (reducedAmalgam L S)
local notation "F" => Universal.cosetFamily A
local notation "U" => fullCartanUniversalCore (L := L) (S := S)
local notation "Pt" => fullCartanClassPoint ds
local notation "Ln" => fullCartanClassLine ds
local notation "axis" => fullCartanClassAxis ds
local notation "center" => fullCartanClassCenter ds
local notation "ρ" => fullCartanPathRoots ds
local notation "N" => apartmentGroup c ρ
local notation "T" => cartanApartment A N
local notation "n" => fullCartanPathLength ds
local notation "r" => sourceRelation A T n
local notation "q" => quotientMap A T n
variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include ds in
/-- The actual universal path radical lies in every interior vertex two-core. -/
theorem fullCartan_pathRoot_le_interior_core {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (j : ℕ)
    (hj : 0 < j) (hjl : j < p.length) :
    pathRoot (X := UX) p ≤ Q F (p.getVert j) := by
  let cov := bOne_tree_cover h
  let f := bOne_tree_map h
  let R := pathRoot (X := UX) p
  have hprev := p.adj_getVert_succ (by omega : j-1 < p.length)
  rw [show j-1+1=j by omega] at hprev
  have hnext := p.adj_getVert_succ hjl
  have hne : cov.vertex (p.getVert (j-1)) ≠ cov.vertex (p.getVert (j+1)) := by
    intro he
    have he' := (cov.neighbor_bijective (p.getVert j)).1
      (a₁ := ⟨_, hprev.symm⟩) (a₂ := ⟨_, hnext⟩) (Subtype.ext he)
    have hh := hp.getVert_injOn (by omega : j-1 ≤ p.length) (by omega : j+1 ≤ p.length)
      (congrArg Subtype.val he')
    omega
  have hfix (k : ℕ) (hk : k ≤ p.length) :
      R.map f ≤ RankTwo.stabilizer (reducedFamily L S) (cov.vertex (p.getVert k)) := by
    rintro z ⟨x, hx, rfl⟩
    change f x • cov.vertex (p.getVert k) = cov.vertex (p.getVert k)
    rw [← cov.vertex_smul]
    exact congrArg cov.vertex ((pCoreIn_le 2 _ hx) k hk)
  have hn (i : Bool) : (B₀ L S).subgroupOf (G₀ L S) ≤ normalizer ((ds i).data.actor : Set (G₀ L S)) := by
    rw [(ds i).actor_eq]
    exact reduced_borel_normalizes_source_actor h _
  have himage := two_group_fixes_turn (reduced_triple h) (ds false).data (ds true).data
    (hn false) (hn true) (cov.hom.map_adj hprev.symm) (cov.hom.map_adj hnext) hne
    (R.map f) ((isPGroup_pCoreIn 2 (pathFixer (X := UX) p)).map f)
    (hfix j (by omega)) (hfix (j-1) (by omega)) (hfix (j+1) (by omega))
  intro x hx
  exact cover_mem_core cov (p.getVert j) x ((pCoreIn_le 2 _ hx) j (by omega))
    (himage (mem_map_of_mem f hx))

include hr in
theorem fullCartanClass_pathRoot_isElation {a b : SourceVertex A}
    (p : (sourceGraph A).Walk a b) (hp : p.IsPath) (hlen : 3 ≤ p.length)
    (u : UX) (hu : u ∈ pathRoot (X := UX) p) (hne : u ≠ 1) :
    ∃ C : Pt, ∃ l : Ln, IsElation u C l := by
  let j : ℕ := if (p.getVert 1).type then 1 else 2
  have hj : 0 < j ∧ j < p.length := by dsimp [j]; split <;> omega
  have ht : (p.getVert j).type = true := by
    have hh := (p.adj_getVert_succ (by omega : 1 < p.length)).1
    cases h₁ : (p.getVert 1).type <;> cases h₂ : (p.getVert 2).type <;> simp_all [j]
  have huQ := fullCartan_pathRoot_le_interior_core ds p hp j hj.1 hj.2 hu
  obtain ⟨a, ha⟩ := exists_smul_base F (p.getVert j)
  rw [ht] at ha
  rw [← ha, Q_translate] at huQ
  obtain ⟨z, hz, hzu⟩ := huQ
  have hzU : z ∈ U true := by
    change z ∈ (F true).pCoreIn 2
    change z ∈ (RankTwo.stabilizer F (base F true)).pCoreIn 2 at hz
    rwa [RankTwo.stabilizer, stabilizer_base] at hz
  have hz1 : (⟨z, hzU⟩ : U true) ≠ 1 := by
    intro he
    apply hne
    have hz0 : z = 1 := congrArg Subtype.val he
    rw [hz0, map_one] at hzu
    exact hzu.symm
  obtain ⟨C, hc⟩ := fullCartanClassCore_isElation ds hr ⟨z, hzU⟩ hz1
  exact ⟨a • C, a • axis, hzu ▸ hc.conjugate a⟩

include hr in
theorem fullCartanClass_root_isElation (i : Bool) (u : UX) (hu : u ∈ (ρ i).root) (hne : u ≠ 1) :
    ∃ C : Pt, ∃ l : Ln, IsElation u C l := by
  let p := reflectionPath c (fullCartanReflections ds) (fullCartanReflections_fix ds)
    (fullCartanReflections_move ds) (fullCartanReflections_normalize ds)
    n (Nat.zero_lt_of_lt (fullCartanPathLength_gt ds)) i
  rw [fullCartanRoots_root] at hu
  have hn : n = 3 := (fullCartanProfiles_parameters ds).1.unique hr.1
  exact fullCartanClass_pathRoot_isElation ds hr p.walk p.isPath
    (by rw [p.length_eq, hn]) u hu hne

include hr in
/-- The required Borel-image signs, proved for the original roots and literal quotient. -/
theorem fullCartan_quotient_root_sign_of_r_three (i : Bool) (x : UX) (hx : x ∈ N) :
    (∀ u ∈ (ρ i).root, q (x⁻¹*u*x) ∈ (originalMiddle A).map q) ∨
    (∀ u ∈ (ρ i).root, q (((ρ i).reflection*x)⁻¹*u*((ρ i).reflection*x)) ∈
      (originalMiddle A).map q) := by
  have hmem (a u : UX) (hu : u ∈ (ρ i).root)
      (hclass : q (a⁻¹*u*a) ∈
        classStabilizer r (apartmentSetoid_invariant (source_action A)) (base F false) ⊓
        classStabilizer r (apartmentSetoid_invariant (source_action A)) (base F true)) :
      q (a⁻¹*u*a) ∈ (originalMiddle A).map q := by
    by_cases hu1 : u = 1
    · simpa only [hu1, mul_one, inv_mul_cancel, map_one] using ((originalMiddle A).map q).one_mem
    obtain ⟨C, l, he⟩ := fullCartanClass_root_isElation ds hr i u hu hu1
    have hh : IsElation (a⁻¹*u*a) (a⁻¹ • C) (a⁻¹ • l) := by
      simpa only [inv_inv] using he.conjugate a⁻¹
    apply fullCartanClass_elation_mem_borel ds hr _ hh
    · exact Subtype.ext (Quotient.sound ((mem_classStabilizer r
        (apartmentSetoid_invariant (source_action A)) (a⁻¹*u*a) _).mp hclass.1))
    · exact Subtype.ext (Quotient.sound ((mem_classStabilizer r
        (apartmentSetoid_invariant (source_action A)) (a⁻¹*u*a) _).mp hclass.2))
  rcases fullCartan_quotient_root_class_sign_of_r_three ds hr i x hx with hs | hs
  · exact Or.inl (fun u hu => hmem x u hu (hs u hu))
  · exact Or.inr (fun u hu => hmem ((ρ i).reflection*x) u hu (hs u hu))

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
