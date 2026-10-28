module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneRThreeClassGeometry
public import Theory.Combinatorics.UniqueIntersectionCounts

/-!
# The projective plane on the literal r=3 apartment classes

The raw generalized triangle gives a unique common neighbor for distinct
vertices of either type. Count its two-step branches using the original
field's panel valence. Each type fiber has q²+q+1 vertices, and the pencils
have q+1 lines. The finite incidence construction then yields a projective
plane of order q on these exact fibers, with incidence equal to raw adjacency.

No identification with endpoint-image cosets and no marked BN quotient is
used. This supplies the plane for a subsequent source elation/coordinate
argument; equality of the original Borel image with the class edge stabilizer
is still a separate obligation.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(3.6), pp.77--78, and the natural-action r=3 branch of (10.5), pp.156--157.
The two-step count adapts the proved coset-graph argument in
`Theory/GroupAction/RankTwoCosetGeometry/ProjectivePlane.lean` to raw classes.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Configuration
open Theory.GroupTheory.WeakBNPair.RegularTree Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
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
local notation "Γ" => fullCartanClassGraph ds
local notation "color" => sourceClassType A T n

/-- The literal point/line fibers of the raw apartment classes. -/
def fullCartanClassFiber (i : Bool) := {a : Quotient r // color a = i}

abbrev fullCartanClassPoint := fullCartanClassFiber ds false
abbrev fullCartanClassLine := fullCartanClassFiber ds true

instance fullCartanClassFiber_finite (i : Bool) : Finite (fullCartanClassFiber ds i) := by
  let := fullCartanClassGraph_finite ds
  exact inferInstanceAs (Finite {a : Quotient r // color a = i})

/-- Incidence is precisely raw class adjacency. -/
instance fullCartanClassMembership : Membership (fullCartanClassPoint ds) (fullCartanClassLine ds) :=
  ⟨fun l p => (Γ).Adj p.val l.val⟩

private theorem two_step_type {v w z : Quotient r}
    (hvw : (Γ).Adj v w) (hwz : (Γ).Adj w z) : color v = color z := by
  have h₁ := sourceClassGraph_bipartition A T n hvw
  have h₂ := sourceClassGraph_bipartition A T n hwz
  cases hv : color v <;> cases hw : color w <;> cases hz : color z <;> simp_all

variable (hr : HasSourcePathParameters (P := fun i => (P₀ L S i).subgroupOf (G₀ L S)) 3 4)

include hr in
/-- Counting length-two branches gives the projective size of each raw fiber. -/
theorem fullCartanClassFiber_card (i : Bool) :
    Nat.card (fullCartanClassFiber ds i) = Nat.card (ds false).F ^ 2 + Nat.card (ds false).F + 1 := by
  classical
  let q := Nat.card (ds false).F
  let := fullCartanClassGraph_finite ds
  let : Fintype (Quotient r) := Fintype.ofFinite _
  let : Fintype (fullCartanClassFiber ds i) := Fintype.ofFinite _
  let v : Quotient r := Quotient.mk r (base (Universal.cosetFamily A) i)
  have hvi : color v = i := rfl
  let U := Σ w : (Γ).neighborSet v, {z : (Γ).neighborSet w.val // z.val ≠ v}
  let W := {z : fullCartanClassFiber ds i // z.val ≠ v}
  let f : U → W := fun t => ⟨⟨t.2.val.val,
    (two_step_type ds t.1.property t.2.val.property).symm.trans hvi⟩, t.2.property⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hz : a.2.val.val = b.2.val.val := congrArg (fun t : W => t.val.val) hab
      have hw : a.1 = b.1 := by
        apply Subtype.ext
        obtain ⟨w, _, hw⟩ := fullCartanClassGraph_commonNeighbor ds hr
          (two_step_type ds a.1.property a.2.val.property) a.2.property.symm
        exact (hw a.1 ⟨a.1.property, a.2.val.property.symm⟩).trans
          (hw b.1 ⟨b.1.property, hz.symm ▸ b.2.val.property.symm⟩).symm
      cases a with | mk a₁ a₂ =>
        cases b with | mk b₁ b₂ =>
          dsimp only at hw
          subst b₁
          congr 1
          exact Subtype.ext (Subtype.ext hz)
    · intro z
      obtain ⟨w, hw, _⟩ := fullCartanClassGraph_commonNeighbor ds hr
        (hvi.trans z.val.property.symm) z.property.symm
      exact ⟨⟨⟨w, hw.1⟩, ⟨⟨z.val.val, hw.2.symm⟩, z.property⟩⟩, rfl⟩
  have hU : Nat.card U = (q+1)*q := by
    rw [show Nat.card U = ∑ w : (Γ).neighborSet v,
      Nat.card {z : (Γ).neighborSet w.val // z.val ≠ v} from Nat.card_sigma]
    have hrest (w : (Γ).neighborSet v) : Nat.card {z : (Γ).neighborSet w.val // z.val ≠ v} = q := by
      let a : (Γ).neighborSet w.val := ⟨v, (show (Γ).Adj v w.val from w.property).symm⟩
      have he : {z : (Γ).neighborSet w.val // z.val ≠ v} = {z : (Γ).neighborSet w.val // z ≠ a} := by
        congr 1
        ext z
        exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
      rw [he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, fullCartanClassGraph_neighbor_card ds hr]
      exact Nat.add_sub_cancel q 1
    simp_rw [hrest]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
      fullCartanClassGraph_neighbor_card ds hr]
    rfl
  have hW : Nat.card W = Nat.card (fullCartanClassFiber ds i) - 1 := by
    let a : fullCartanClassFiber ds i := ⟨v, hvi⟩
    have he : W = {z : fullCartanClassFiber ds i // z ≠ a} := by
      dsimp only [W]
      congr 1
      ext z
      exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    rw [he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card]
  have he := Nat.card_congr (Equiv.ofBijective f hbij)
  rw [hU, hW] at he
  have hpos : 0 < Nat.card (fullCartanClassFiber ds i) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨v, hvi⟩⟩, inferInstance⟩
  have hsucc := Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)
  change Nat.card (fullCartanClassFiber ds i) = q^2+q+1
  nlinarith

/-- A raw pencil is exactly the graph neighborhood, with no endpoint-coset comparison. -/
def fullCartanClassPencilEquiv (p : fullCartanClassPoint ds) :
    {l : fullCartanClassLine ds // p ∈ l} ≃ (Γ).neighborSet p.val where
  toFun l := ⟨l.val.val, l.property⟩
  invFun l := ⟨⟨l.val, by
    have hh := sourceClassGraph_bipartition A T n l.property
    rw [p.property] at hh
    cases hl : color l.val <;> simp_all⟩, l.property⟩

include hr in
/-- Distinct raw lines meet in exactly one raw point. -/
theorem fullCartanClassLines_intersect (l m : fullCartanClassLine ds) (hne : l ≠ m) :
    ∃! p : fullCartanClassPoint ds, p ∈ l ∧ p ∈ m := by
  obtain ⟨p, hp, hu⟩ := fullCartanClassGraph_commonNeighbor ds hr
    (l.property.trans m.property.symm) (fun he => hne (Subtype.ext he))
  have htype : color p = false := by
    have hh := sourceClassGraph_bipartition A T n hp.1
    rw [l.property] at hh
    cases hP : color p <;> simp_all
  refine ⟨⟨p, htype⟩, ⟨hp.1.symm, hp.2.symm⟩, ?_⟩
  intro q hq
  exact Subtype.ext (hu q.val ⟨hq.1.symm, hq.2.symm⟩)

/-- The projective plane on the SAME raw quotient, constructed before any
Borel-image identification or marked BN quotient. -/
@[instance_reducible] def fullCartanClassPlane :
    ProjectivePlane (fullCartanClassPoint ds) (fullCartanClassLine ds) :=
  projectivePlane_of_unique_intersections (Nat.card (ds false).F) Finite.one_lt_card
    (fullCartanClassFiber_card ds hr true)
    (fun p => (Nat.card_congr (fullCartanClassPencilEquiv ds p)).trans
      (fullCartanClassGraph_neighbor_card ds hr p.val))
    (fullCartanClassLines_intersect ds hr)

/-- Its order is the original natural-action field size. -/
theorem fullCartanClassPlane_order :
    let := fullCartanClassPlane ds hr
    ProjectivePlane.order (fullCartanClassPoint ds) (fullCartanClassLine ds) = Nat.card (ds false).F := by
  let := fullCartanClassPlane ds hr
  let p : fullCartanClassPoint ds := ⟨Quotient.mk r (base (Universal.cosetFamily A) false), rfl⟩
  have he := ProjectivePlane.lineCount_eq (fullCartanClassLine ds) p
  have hc := (Nat.card_congr (fullCartanClassPencilEquiv ds p)).trans
    (fullCartanClassGraph_neighbor_card ds hr p.val)
  change lineCount (fullCartanClassLine ds) p = Nat.card (ds false).F + 1 at hc
  omega

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
