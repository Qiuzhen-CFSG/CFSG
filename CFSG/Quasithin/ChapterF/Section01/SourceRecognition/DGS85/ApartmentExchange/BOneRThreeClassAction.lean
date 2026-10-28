module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassPlane
public import Theory.GroupTheory.WeakBNPair.RegularTree.ClassGraphAction
public import Theory.Combinatorics.ProjectivePlaneCollineation

/-!
# Original core actions on the raw apartment plane

The universal completion acts by collineations on the same raw classes used
by its finite quotient. Kernel-disjointness shows that a nonidentity element
of an original endpoint still moves a raw point or line. The original covering
identifies each universal endpoint two-core, and their intersection, with the
corresponding original subgroups. Local bijectivity transfers their panel
fixation first to the tree and then to the raw plane.

These statements do not identify the full class stabilizers with endpoint
images. They supply the actual actions and nontriviality needed for the elation
argument, keeping the source-covering map distinct from the class-action kernel.
Source: DGS, *Groups and Graphs* (1985), (3.6), pp.77--78, and (10.5), p.156.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange

section Types
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)

theorem sourceClassType_action (g : α.Universal) (a : Quotient (sourceRelation α T n)) :
    sourceClassType α T n (quotientAction _ (apartmentSetoid_invariant (source_action α)) g a) =
      sourceClassType α T n a := by
  induction a using Quotient.inductionOn with
  | h a => rfl

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
local notation "act" => quotientAction r (apartmentSetoid_invariant (source_action A))

instance fullCartanClassFiber_action (i : Bool) : MulAction (reducedAmalgam L S).Universal (fullCartanClassFiber ds i) where
  smul g a := ⟨act g a.val, (sourceClassType_action A T n g a.val).trans a.property⟩
  one_smul a := Subtype.ext (by change act 1 a.val = a.val; rw [map_one]; rfl)
  mul_smul g k a := Subtype.ext (by change act (g*k) a.val = act g (act k a.val); rw [map_mul]; rfl)

@[simp] theorem fullCartanClassFiber_smul_val (i : Bool) (g : (reducedAmalgam L S).Universal)
    (a : fullCartanClassFiber ds i) : (g • a).val = act g a.val := rfl

instance fullCartanClass_collineation :
    IsCollineationAction (reducedAmalgam L S).Universal (fullCartanClassPoint ds) (fullCartanClassLine ds) where
  smul_mem_smul_iff g p l :=
    quotientAction_adj_iff (apartmentSetoid_invariant (source_action A)) (source_action A) g p.val l.val

def fullCartanClassBase (i : Bool) : fullCartanClassFiber ds i :=
  ⟨Quotient.mk r (base (Universal.cosetFamily A) i), rfl⟩

abbrev fullCartanClassAxis := fullCartanClassBase ds true
abbrev fullCartanClassCenter := fullCartanClassBase ds false

abbrev fullCartanUniversalCore (i : Bool) : Subgroup (reducedAmalgam L S).Universal :=
  (Universal.cosetFamily A i).pCoreIn 2

theorem fullCartanClassBase_fixed (i : Bool) {g : (reducedAmalgam L S).Universal}
    (hg : g ∈ Universal.cosetFamily A i) : g • fullCartanClassBase ds i = fullCartanClassBase ds i := by
  apply Subtype.ext
  change Quotient.mk r (g • base (Universal.cosetFamily A) i) = _
  have he : g • base (Universal.cosetFamily A) i = base (Universal.cosetFamily A) i := by
    rwa [← stabilizer_base (F := Universal.cosetFamily A) (i := i)] at hg
  exact congrArg (Quotient.mk r) he

variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include hr in
theorem fullCartanClass_incident : fullCartanClassCenter ds ∈ fullCartanClassAxis ds :=
  (fullCartanClassMap ds hr).map_adj ⟨Bool.false_ne_true, incident_base _ _ _⟩

include hr in
theorem fullCartanClass_moves {g : (reducedAmalgam L S).Universal} (i : Bool)
    (hg : g ∈ Universal.cosetFamily A i) (hne : g ≠ 1) :
    (∃ p : fullCartanClassPoint ds, g • p ≠ p) ∨
      ∃ l : fullCartanClassLine ds, g • l ≠ l := by
  by_contra! hh
  have hk : g ∈ kernel A T n := by
    apply (mem_quotientKernel r (apartmentSetoid_invariant (source_action A)) g).mpr
    intro v
    apply Quotient.exact
    cases hv : v.type
    · exact congrArg Subtype.val (hh.1 ⟨Quotient.mk r v, hv⟩)
    · exact congrArg Subtype.val (hh.2 ⟨Quotient.mk r v, hv⟩)
  have hb : g ∈ kernel A T n ⊓ Universal.cosetFamily A i := ⟨hk, hg⟩
  rw [fullCartan_kernel_inf_endpoints_of_r_three ds hr i] at hb
  exact hne hb

def universalBOneCoreEquiv (h : HypothesisF11 L S) (i : Bool) :
    fullCartanUniversalCore (L := L) (S := S) i ≃*
      Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let f : fullCartanUniversalCore (L := L) (S := S) i →*
      Q (reducedFamily L S) (base (reducedFamily L S) i) :=
    { toFun x := ⟨bOne_tree_map h x,
        (universalBOne_mem_core_iff h i x (pCoreIn_le 2 _ x.property)).mpr x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ _ _) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y he
    exact Subtype.ext (congrArg (fun z : Universal.cosetFamily A i => (z : (reducedAmalgam L S).Universal)) ((bOne_tree_cover h).injective i
      (a₁ := ⟨x, pCoreIn_le 2 _ x.property⟩) (a₂ := ⟨y, pCoreIn_le 2 _ y.property⟩)
      (congrArg Subtype.val he)))
  · intro y
    have hy := y.property
    have hy' : (y : G₀ L S) ∈ ((Universal.cosetFamily A i).pCoreIn 2).map (bOne_tree_map h) := by
      simpa only [universalBOne_core_map h i] using hy
    obtain ⟨x, hx, he⟩ := hy'
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

@[simp] theorem universalBOneCoreEquiv_apply (h : HypothesisF11 L S) (i : Bool)
    (x : fullCartanUniversalCore (L := L) (S := S) i) :
    (universalBOneCoreEquiv h i x : G₀ L S) = bOne_tree_map h x := rfl

theorem universalBOneCore_fixes_neighbor (h : HypothesisF11 L S) (i : Bool)
    {x : (reducedAmalgam L S).Universal} (hx : x ∈ fullCartanUniversalCore (L := L) (S := S) i)
    {v : SourceVertex A} (hv : (sourceGraph A).Adj (base (Universal.cosetFamily A) i) v) :
    x • v = v := by
  apply universal_vertex_core_fixes_neighbors h _ _ hv
  simpa only [stabilizer_base] using hx

include hr in
theorem fullCartanClassCore_fixes_neighbor (i : Bool)
    {x : (reducedAmalgam L S).Universal} (hx : x ∈ fullCartanUniversalCore (L := L) (S := S) i)
    {v : Quotient r} (hv : (fullCartanClassGraph ds).Adj (fullCartanClassBase ds i).val v) :
    act x v = v :=
  quotientAction_fixes_neighbor (apartmentSetoid_invariant (source_action A))
    (fullCartan_source_neighbor_lifting_of_r_three ds hr)
    (fun _ hv => universalBOneCore_fixes_neighbor h i hx hv) hv

def universalBOneCoreIntersectionEquiv (h : HypothesisF11 L S) :
    (fullCartanUniversalCore (L := L) (S := S) true ⊓
      fullCartanUniversalCore (L := L) (S := S) false : Subgroup (reducedAmalgam L S).Universal) ≃*
    (Q (reducedFamily L S) (base (reducedFamily L S) true) ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) false) : Subgroup (G₀ L S)) := by
  let f : (fullCartanUniversalCore (L := L) (S := S) true ⊓
      fullCartanUniversalCore (L := L) (S := S) false : Subgroup (reducedAmalgam L S).Universal) →*
    (Q (reducedFamily L S) (base (reducedFamily L S) true) ⊓
      Q (reducedFamily L S) (base (reducedFamily L S) false) : Subgroup (G₀ L S)) :=
    { toFun x := ⟨bOne_tree_map h x,
        (universalBOneCoreEquiv h true ⟨x, x.property.1⟩).property,
        (universalBOneCoreEquiv h false ⟨x, x.property.2⟩).property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ _ _) }
  apply MulEquiv.ofBijective f
  constructor
  · intro x y he
    exact Subtype.ext (congrArg (fun z : Universal.cosetFamily A true => (z : (reducedAmalgam L S).Universal)) ((bOne_tree_cover h).injective true
      (a₁ := ⟨x, pCoreIn_le 2 _ x.property.1⟩) (a₂ := ⟨y, pCoreIn_le 2 _ y.property.1⟩)
      (congrArg Subtype.val he)))
  · intro y
    let x := (universalBOneCoreEquiv h true).symm ⟨y, y.property.1⟩
    have hxy : bOne_tree_map h x = y :=
      congrArg Subtype.val ((universalBOneCoreEquiv h true).apply_symm_apply ⟨y, y.property.1⟩)
    have hxP : (x : (reducedAmalgam L S).Universal) ∈ Universal.cosetFamily A false := by
      rw [← stabilizer_base (F := Universal.cosetFamily A) (i := false)]
      exact universalBOneCore_fixes_neighbor h true x.property
        ⟨Bool.false_ne_true.symm, incident_base _ _ _⟩
    have hxQ : (x : (reducedAmalgam L S).Universal) ∈ fullCartanUniversalCore (L := L) (S := S) false :=
      (universalBOne_mem_core_iff h false x hxP).mp (hxy.symm ▸ y.property.2)
    exact ⟨⟨x, x.property, hxQ⟩, Subtype.ext hxy⟩

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
