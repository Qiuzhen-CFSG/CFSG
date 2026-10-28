module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/G2/BinaryHexagon.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths, Lean 4.33 public module boundaries, and removal of
one redundant `change` tactic for the unused-tactic linter.
-/

public import Theory.AtlasPort.LinearGroups.G2.RootGroups
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Field.ZMod

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
/-!
The actual binary hexagon consists of the three nonzero vectors of a
zero-product octonion plane. The explicit list is proved complete by ordinary
kernel reduction over six binary coordinates; it is not an assumed permutation
model. The root actions and their fixed-line counts are transported to this
actual geometric line type.
-/
@[expose] public section

namespace Atlas.G2.Binary
open Atlas.SplitOctonion Atlas.G2.Explicit
abbrev K := ZMod 2
abbrev V := Carrier K

/-- A nonzero singular imaginary octonion over the two-element field. -/
def Singular (x : V) : Prop := x ≠ 0 ∧ trace x = 0 ∧ norm x = 0

instance (x : V) : Decidable (Singular x) := by
  unfold Singular
  infer_instance

/-- The three nonzero vectors of a zero-product octonion plane. -/
def IsLine (s : Finset V) : Prop := ∃ x y : V,
    Singular x ∧ Singular y ∧ Singular (x+y) ∧ mul x y = 0 ∧ mul y x = 0 ∧
    s = {x,y,x+y}

def Line := {s : Finset V // IsLine s}

instance : Finite Line := inferInstanceAs (Finite {s : Finset V // IsLine s})

 theorem singular_map (g : Model K) {x:V} (hx : Singular x) : Singular (g.val x) := by
  refine ⟨?_,?_,?_⟩
  · exact fun h => hx.1 (g.val.injective (h.trans (map_zero g.val).symm))
  · rw [automorphism_trace]; exact hx.2.1
  · rw [automorphism_norm]; exact hx.2.2

 def mapLine (g : Model K) (L : Line) : Line := by
  refine ⟨L.val.map g.val.toEquiv.toEmbedding,?_⟩
  obtain ⟨x,y,hx,hy,hxy,hm,hm',he⟩ := L.prop
  refine ⟨g.val x,g.val y,singular_map g hx,singular_map g hy,?_,?_,?_,?_⟩
  · simpa only [map_add] using singular_map g hxy
  · rw [← automorphism_mul,hm,map_zero]
  · rw [← automorphism_mul,hm',map_zero]
  · simp [he,map_add]

 instance lineAction : MulAction (Model K) Line where
  smul := mapLine
  one_smul L := by
    apply Subtype.ext
    change L.val.map _ = L.val
    exact Finset.map_refl
  mul_smul g h L := by
    apply Subtype.ext
    change L.val.map _ = (L.val.map _).map _
    rw [Finset.map_map]
    rfl

noncomputable def lineSign : Model K →* Units ℤ := by
  classical
  letI := Fintype.ofFinite Line
  exact Equiv.Perm.sign.comp (MulAction.toPermHom (Model K) Line)

/-- Six free binary coordinates parametrize the full singular cone. -/
def point (t : Fin 6 → K) : V :=
  let s := t 0*t 5+t 1*t 4+t 2*t 3
  ![t 0,t 1,t 2,s,s,t 3,t 4,t 5]

 theorem square_eq_self (a : K) : a*a=a := by
  have h : ∀ a : ZMod 2, a*a=a := by decide +kernel
  exact h a

theorem point_trace (t : Fin 6 → K) : trace (point t) = 0 := by
 have hc : ∀ a : K, a+a=0 := by decide +kernel
 exact hc _

theorem point_norm (t : Fin 6 → K) : SplitOctonion.norm (point t) = 0 := by
 change (t 0*t 5+t 1*t 4+t 2*t 3)+(t 0*t 5+t 1*t 4+t 2*t 3)*(t 0*t 5+t 1*t 4+t 2*t 3)=0
 rw [square_eq_self]
 have hc : ∀ a : K, a+a=0 := by decide +kernel
 exact hc _

 theorem point_coordinates {x:V} (ht : trace x = 0) (hn : norm x = 0) :
    point ![x 0,x 1,x 2,x 5,x 6,x 7] = x := by
  have hn' : x 0*x 7+x 1*x 6+x 2*x 5+x 3*x 4=0 := hn
  have ht' : x 3+x 4=0 := ht
  have hn4 : x 4=x 3 := by
    have hc : ∀ a : K, -a=a := by decide +kernel
    exact (eq_neg_of_add_eq_zero_right ht').trans (hc _)
  rw [hn4,square_eq_self] at hn'
  have hc : ∀ a : K, -a=a := by decide +kernel
  have hs : x 0*x 7+x 1*x 6+x 2*x 5=x 3 :=
    (eq_neg_of_add_eq_zero_left hn').trans (hc _)
  funext i; fin_cases i <;> simp [point,hs,hn4]

def GoodPair (p : (Fin 6 → K) × (Fin 6 → K)) : Prop :=
  Singular (point p.1) ∧ Singular (point p.2) ∧ Singular (point p.1+point p.2) ∧
  mul (point p.1) (point p.2)=0 ∧ mul (point p.2) (point p.1)=0

instance (p : (Fin 6 → K) × (Fin 6 → K)) : Decidable (GoodPair p) := by
  unfold GoodPair Singular
  infer_instance

def pairs : Finset ((Fin 6 → K) × (Fin 6 → K)) := Finset.univ.filter GoodPair

def lineOfPair (p : (Fin 6 → K) × (Fin 6 → K)) : Finset V :=
  {point p.1,point p.2,point p.1+point p.2}

def lines : Finset (Finset V) := pairs.image lineOfPair

 theorem mem_lines (s : Finset V) : s ∈ lines ↔ IsLine s := by
  constructor
  · intro h
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp h
    have hp' : GoodPair p := (Finset.mem_filter.mp hp).2
    exact ⟨point p.1,point p.2,hp'.1,hp'.2.1,hp'.2.2.1,hp'.2.2.2.1,hp'.2.2.2.2,rfl⟩
  · rintro ⟨x,y,hx,hy,hxy,hm,hm',rfl⟩
    let t : Fin 6 → K := ![x 0,x 1,x 2,x 5,x 6,x 7]
    let u : Fin 6 → K := ![y 0,y 1,y 2,y 5,y 6,y 7]
    have he : point t=x := point_coordinates hx.2.1 hx.2.2
    have he' : point u=y := point_coordinates hy.2.1 hy.2.2
    apply Finset.mem_image.mpr
    refine ⟨(t,u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [GoodPair,he,he'] using And.intro hx ⟨hy,hxy,hm,hm'⟩
    · simp [lineOfPair,he,he']

 def lineEquiv : Line ≃ {s // s ∈ lines} where
  toFun L := ⟨L.val,(mem_lines L.val).mpr L.prop⟩
  invFun L := ⟨L.val,(mem_lines L.val).mp L.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl


set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def explicitLines : Finset (Finset V) :=
  {{![1,0,0,0,0,0,0,0],![0,1,0,0,0,0,0,0],![1,1,0,0,0,0,0,0]},
   {![1,0,0,0,0,0,0,0],![0,0,1,0,0,0,0,0],![1,0,1,0,0,0,0,0]},
   {![1,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0],![1,1,1,0,0,0,0,0]},
   {![0,1,0,0,0,0,0,0],![0,0,0,0,0,1,0,0],![0,1,0,0,0,1,0,0]},
   {![0,1,0,0,0,0,0,0],![1,0,0,0,0,1,0,0],![1,1,0,0,0,1,0,0]},
   {![1,1,0,0,0,0,0,0],![0,0,1,1,1,1,0,0],![1,1,1,1,1,1,0,0]},
   {![1,1,0,0,0,0,0,0],![1,0,1,1,1,1,0,0],![0,1,1,1,1,1,0,0]},
   {![0,0,1,0,0,0,0,0],![0,0,0,0,0,0,1,0],![0,0,1,0,0,0,1,0]},
   {![0,0,1,0,0,0,0,0],![1,0,0,0,0,0,1,0],![1,0,1,0,0,0,1,0]},
   {![1,0,1,0,0,0,0,0],![0,1,0,1,1,0,1,0],![1,1,1,1,1,0,1,0]},
   {![1,0,1,0,0,0,0,0],![1,1,0,1,1,0,1,0],![0,1,1,1,1,0,1,0]},
   {![0,1,1,0,0,0,0,0],![0,0,0,0,0,1,1,0],![0,1,1,0,0,1,1,0]},
   {![0,1,1,0,0,0,0,0],![1,0,0,0,0,1,1,0],![1,1,1,0,0,1,1,0]},
   {![1,1,1,0,0,0,0,0],![0,1,0,1,1,1,1,0],![1,0,1,1,1,1,1,0]},
   {![1,1,1,0,0,0,0,0],![1,1,0,1,1,1,1,0],![0,0,1,1,1,1,1,0]},
   {![0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,1],![0,0,0,0,0,1,0,1]},
   {![0,0,0,0,0,1,0,0],![0,1,0,0,0,0,0,1],![0,1,0,0,0,1,0,1]},
   {![1,0,0,0,0,1,0,0],![0,0,1,0,0,0,0,1],![1,0,1,0,0,1,0,1]},
   {![1,0,0,0,0,1,0,0],![0,1,1,0,0,0,0,1],![1,1,1,0,0,1,0,1]},
   {![0,1,0,0,0,1,0,0],![1,0,0,1,1,0,0,1],![1,1,0,1,1,1,0,1]},
   {![0,1,0,0,0,1,0,0],![1,1,0,1,1,0,0,1],![1,0,0,1,1,1,0,1]},
   {![1,1,0,0,0,1,0,0],![1,0,1,1,1,0,0,1],![0,1,1,1,1,1,0,1]},
   {![1,1,0,0,0,1,0,0],![1,1,1,1,1,0,0,1],![0,0,1,1,1,1,0,1]},
   {![0,0,1,1,1,1,0,0],![0,0,0,0,0,0,1,1],![0,0,1,1,1,1,1,1]},
   {![0,0,1,1,1,1,0,0],![1,1,0,0,0,0,1,1],![1,1,1,1,1,1,1,1]},
   {![1,0,1,1,1,1,0,0],![0,0,1,0,0,0,1,1],![1,0,0,1,1,1,1,1]},
   {![1,0,1,1,1,1,0,0],![1,1,1,0,0,0,1,1],![0,1,0,1,1,1,1,1]},
   {![0,1,1,1,1,1,0,0],![1,0,1,1,1,0,1,1],![1,1,0,0,0,1,1,1]},
   {![0,1,1,1,1,1,0,0],![0,1,1,1,1,0,1,1],![0,0,0,0,0,1,1,1]},
   {![1,1,1,1,1,1,0,0],![1,0,0,1,1,0,1,1],![0,1,1,0,0,1,1,1]},
   {![1,1,1,1,1,1,0,0],![0,1,0,1,1,0,1,1],![1,0,1,0,0,1,1,1]},
   {![0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,1],![0,0,0,0,0,0,1,1]},
   {![0,0,0,0,0,0,1,0],![0,0,1,0,0,0,0,1],![0,0,1,0,0,0,1,1]},
   {![1,0,0,0,0,0,1,0],![0,1,0,0,0,0,0,1],![1,1,0,0,0,0,1,1]},
   {![1,0,0,0,0,0,1,0],![0,1,1,0,0,0,0,1],![1,1,1,0,0,0,1,1]},
   {![0,0,1,0,0,0,1,0],![1,0,0,1,1,0,0,1],![1,0,1,1,1,0,1,1]},
   {![0,0,1,0,0,0,1,0],![1,0,1,1,1,0,0,1],![1,0,0,1,1,0,1,1]},
   {![1,0,1,0,0,0,1,0],![1,1,0,1,1,0,0,1],![0,1,1,1,1,0,1,1]},
   {![1,0,1,0,0,0,1,0],![1,1,1,1,1,0,0,1],![0,1,0,1,1,0,1,1]},
   {![0,1,0,1,1,0,1,0],![0,0,0,0,0,1,0,1],![0,1,0,1,1,1,1,1]},
   {![0,1,0,1,1,0,1,0],![1,0,1,0,0,1,0,1],![1,1,1,1,1,1,1,1]},
   {![1,1,0,1,1,0,1,0],![0,1,0,0,0,1,0,1],![1,0,0,1,1,1,1,1]},
   {![1,1,0,1,1,0,1,0],![1,1,1,0,0,1,0,1],![0,0,1,1,1,1,1,1]},
   {![0,1,1,1,1,0,1,0],![1,1,0,1,1,1,0,1],![1,0,1,0,0,1,1,1]},
   {![0,1,1,1,1,0,1,0],![0,1,1,1,1,1,0,1],![0,0,0,0,0,1,1,1]},
   {![1,1,1,1,1,0,1,0],![1,0,0,1,1,1,0,1],![0,1,1,0,0,1,1,1]},
   {![1,1,1,1,1,0,1,0],![0,0,1,1,1,1,0,1],![1,1,0,0,0,1,1,1]},
   {![0,0,0,0,0,1,1,0],![0,0,0,0,0,0,0,1],![0,0,0,0,0,1,1,1]},
   {![0,0,0,0,0,1,1,0],![0,1,1,0,0,0,0,1],![0,1,1,0,0,1,1,1]},
   {![1,0,0,0,0,1,1,0],![0,1,0,0,0,0,0,1],![1,1,0,0,0,1,1,1]},
   {![1,0,0,0,0,1,1,0],![0,0,1,0,0,0,0,1],![1,0,1,0,0,1,1,1]},
   {![0,1,1,0,0,1,1,0],![1,0,0,1,1,0,0,1],![1,1,1,1,1,1,1,1]},
   {![0,1,1,0,0,1,1,0],![1,1,1,1,1,0,0,1],![1,0,0,1,1,1,1,1]},
   {![1,1,1,0,0,1,1,0],![1,1,0,1,1,0,0,1],![0,0,1,1,1,1,1,1]},
   {![1,1,1,0,0,1,1,0],![1,0,1,1,1,0,0,1],![0,1,0,1,1,1,1,1]},
   {![0,1,0,1,1,1,1,0],![0,0,0,0,0,1,0,1],![0,1,0,1,1,0,1,1]},
   {![0,1,0,1,1,1,1,0],![1,1,1,0,0,1,0,1],![1,0,1,1,1,0,1,1]},
   {![1,1,0,1,1,1,1,0],![0,1,0,0,0,1,0,1],![1,0,0,1,1,0,1,1]},
   {![1,1,0,1,1,1,1,0],![1,0,1,0,0,1,0,1],![0,1,1,1,1,0,1,1]},
   {![0,0,1,1,1,1,1,0],![1,1,0,1,1,1,0,1],![1,1,1,0,0,0,1,1]},
   {![0,0,1,1,1,1,1,0],![0,0,1,1,1,1,0,1],![0,0,0,0,0,0,1,1]},
   {![1,0,1,1,1,1,1,0],![1,0,0,1,1,1,0,1],![0,0,1,0,0,0,1,1]},
   {![1,0,1,1,1,1,1,0],![0,1,1,1,1,1,0,1],![1,1,0,0,0,0,1,1]}}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem card_explicitLines : explicitLines.card = 63 := by decide +kernel

def explicitFixedLines (g : Model K) : Finset (Finset V) :=
  explicitLines.filter (fun s => s.map g.val.toEquiv.toEmbedding = s)

theorem fixed_rootA_count : (explicitFixedLines (rootA (1 : K))).card = 7 := by decide +kernel

theorem fixed_rootF_count : (explicitFixedLines (rootF (1 : K))).card = 9 := by decide +kernel

private theorem goodRow0 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,0,0,0],u) →
    lineOfPair (![0,0,0,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow1 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,0,0,0],u) →
    lineOfPair (![1,0,0,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow2 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,0,0,0],u) →
    lineOfPair (![0,1,0,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow3 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,0,0,0],u) →
    lineOfPair (![1,1,0,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow4 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,0,0,0],u) →
    lineOfPair (![0,0,1,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow5 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,0,0,0],u) →
    lineOfPair (![1,0,1,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow6 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,0,0,0],u) →
    lineOfPair (![0,1,1,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow7 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,0,0,0],u) →
    lineOfPair (![1,1,1,0,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow8 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,1,0,0],u) →
    lineOfPair (![0,0,0,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow9 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,1,0,0],u) →
    lineOfPair (![1,0,0,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow10 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,1,0,0],u) →
    lineOfPair (![0,1,0,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow11 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,1,0,0],u) →
    lineOfPair (![1,1,0,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow12 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,1,0,0],u) →
    lineOfPair (![0,0,1,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow13 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,1,0,0],u) →
    lineOfPair (![1,0,1,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow14 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,1,0,0],u) →
    lineOfPair (![0,1,1,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow15 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,1,0,0],u) →
    lineOfPair (![1,1,1,1,0,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow16 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,0,1,0],u) →
    lineOfPair (![0,0,0,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow17 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,0,1,0],u) →
    lineOfPair (![1,0,0,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow18 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,0,1,0],u) →
    lineOfPair (![0,1,0,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow19 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,0,1,0],u) →
    lineOfPair (![1,1,0,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow20 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,0,1,0],u) →
    lineOfPair (![0,0,1,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow21 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,0,1,0],u) →
    lineOfPair (![1,0,1,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow22 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,0,1,0],u) →
    lineOfPair (![0,1,1,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow23 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,0,1,0],u) →
    lineOfPair (![1,1,1,0,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow24 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,1,1,0],u) →
    lineOfPair (![0,0,0,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow25 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,1,1,0],u) →
    lineOfPair (![1,0,0,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow26 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,1,1,0],u) →
    lineOfPair (![0,1,0,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow27 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,1,1,0],u) →
    lineOfPair (![1,1,0,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow28 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,1,1,0],u) →
    lineOfPair (![0,0,1,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow29 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,1,1,0],u) →
    lineOfPair (![1,0,1,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow30 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,1,1,0],u) →
    lineOfPair (![0,1,1,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow31 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,1,1,0],u) →
    lineOfPair (![1,1,1,1,1,0],u) ∈ explicitLines := by decide +kernel

private theorem goodRow32 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,0,0,1],u) →
    lineOfPair (![0,0,0,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow33 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,0,0,1],u) →
    lineOfPair (![1,0,0,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow34 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,0,0,1],u) →
    lineOfPair (![0,1,0,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow35 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,0,0,1],u) →
    lineOfPair (![1,1,0,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow36 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,0,0,1],u) →
    lineOfPair (![0,0,1,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow37 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,0,0,1],u) →
    lineOfPair (![1,0,1,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow38 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,0,0,1],u) →
    lineOfPair (![0,1,1,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow39 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,0,0,1],u) →
    lineOfPair (![1,1,1,0,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow40 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,1,0,1],u) →
    lineOfPair (![0,0,0,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow41 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,1,0,1],u) →
    lineOfPair (![1,0,0,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow42 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,1,0,1],u) →
    lineOfPair (![0,1,0,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow43 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,1,0,1],u) →
    lineOfPair (![1,1,0,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow44 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,1,0,1],u) →
    lineOfPair (![0,0,1,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow45 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,1,0,1],u) →
    lineOfPair (![1,0,1,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow46 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,1,0,1],u) →
    lineOfPair (![0,1,1,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow47 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,1,0,1],u) →
    lineOfPair (![1,1,1,1,0,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow48 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,0,1,1],u) →
    lineOfPair (![0,0,0,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow49 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,0,1,1],u) →
    lineOfPair (![1,0,0,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow50 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,0,1,1],u) →
    lineOfPair (![0,1,0,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow51 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,0,1,1],u) →
    lineOfPair (![1,1,0,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow52 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,0,1,1],u) →
    lineOfPair (![0,0,1,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow53 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,0,1,1],u) →
    lineOfPair (![1,0,1,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow54 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,0,1,1],u) →
    lineOfPair (![0,1,1,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow55 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,0,1,1],u) →
    lineOfPair (![1,1,1,0,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow56 : ∀ u : Fin 6 → K, GoodPair (![0,0,0,1,1,1],u) →
    lineOfPair (![0,0,0,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow57 : ∀ u : Fin 6 → K, GoodPair (![1,0,0,1,1,1],u) →
    lineOfPair (![1,0,0,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow58 : ∀ u : Fin 6 → K, GoodPair (![0,1,0,1,1,1],u) →
    lineOfPair (![0,1,0,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow59 : ∀ u : Fin 6 → K, GoodPair (![1,1,0,1,1,1],u) →
    lineOfPair (![1,1,0,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow60 : ∀ u : Fin 6 → K, GoodPair (![0,0,1,1,1,1],u) →
    lineOfPair (![0,0,1,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow61 : ∀ u : Fin 6 → K, GoodPair (![1,0,1,1,1,1],u) →
    lineOfPair (![1,0,1,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow62 : ∀ u : Fin 6 → K, GoodPair (![0,1,1,1,1,1],u) →
    lineOfPair (![0,1,1,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem goodRow63 : ∀ u : Fin 6 → K, GoodPair (![1,1,1,1,1,1],u) →
    lineOfPair (![1,1,1,1,1,1],u) ∈ explicitLines := by decide +kernel

private theorem binaryParameter_cases (P : (Fin 6 → K) → Prop)
    (h0 : P ![0,0,0,0,0,0])
    (h1 : P ![1,0,0,0,0,0])
    (h2 : P ![0,1,0,0,0,0])
    (h3 : P ![1,1,0,0,0,0])
    (h4 : P ![0,0,1,0,0,0])
    (h5 : P ![1,0,1,0,0,0])
    (h6 : P ![0,1,1,0,0,0])
    (h7 : P ![1,1,1,0,0,0])
    (h8 : P ![0,0,0,1,0,0])
    (h9 : P ![1,0,0,1,0,0])
    (h10 : P ![0,1,0,1,0,0])
    (h11 : P ![1,1,0,1,0,0])
    (h12 : P ![0,0,1,1,0,0])
    (h13 : P ![1,0,1,1,0,0])
    (h14 : P ![0,1,1,1,0,0])
    (h15 : P ![1,1,1,1,0,0])
    (h16 : P ![0,0,0,0,1,0])
    (h17 : P ![1,0,0,0,1,0])
    (h18 : P ![0,1,0,0,1,0])
    (h19 : P ![1,1,0,0,1,0])
    (h20 : P ![0,0,1,0,1,0])
    (h21 : P ![1,0,1,0,1,0])
    (h22 : P ![0,1,1,0,1,0])
    (h23 : P ![1,1,1,0,1,0])
    (h24 : P ![0,0,0,1,1,0])
    (h25 : P ![1,0,0,1,1,0])
    (h26 : P ![0,1,0,1,1,0])
    (h27 : P ![1,1,0,1,1,0])
    (h28 : P ![0,0,1,1,1,0])
    (h29 : P ![1,0,1,1,1,0])
    (h30 : P ![0,1,1,1,1,0])
    (h31 : P ![1,1,1,1,1,0])
    (h32 : P ![0,0,0,0,0,1])
    (h33 : P ![1,0,0,0,0,1])
    (h34 : P ![0,1,0,0,0,1])
    (h35 : P ![1,1,0,0,0,1])
    (h36 : P ![0,0,1,0,0,1])
    (h37 : P ![1,0,1,0,0,1])
    (h38 : P ![0,1,1,0,0,1])
    (h39 : P ![1,1,1,0,0,1])
    (h40 : P ![0,0,0,1,0,1])
    (h41 : P ![1,0,0,1,0,1])
    (h42 : P ![0,1,0,1,0,1])
    (h43 : P ![1,1,0,1,0,1])
    (h44 : P ![0,0,1,1,0,1])
    (h45 : P ![1,0,1,1,0,1])
    (h46 : P ![0,1,1,1,0,1])
    (h47 : P ![1,1,1,1,0,1])
    (h48 : P ![0,0,0,0,1,1])
    (h49 : P ![1,0,0,0,1,1])
    (h50 : P ![0,1,0,0,1,1])
    (h51 : P ![1,1,0,0,1,1])
    (h52 : P ![0,0,1,0,1,1])
    (h53 : P ![1,0,1,0,1,1])
    (h54 : P ![0,1,1,0,1,1])
    (h55 : P ![1,1,1,0,1,1])
    (h56 : P ![0,0,0,1,1,1])
    (h57 : P ![1,0,0,1,1,1])
    (h58 : P ![0,1,0,1,1,1])
    (h59 : P ![1,1,0,1,1,1])
    (h60 : P ![0,0,1,1,1,1])
    (h61 : P ![1,0,1,1,1,1])
    (h62 : P ![0,1,1,1,1,1])
    (h63 : P ![1,1,1,1,1,1])
    (t : Fin 6 → K) : P t := by
  have ht : t = ![t 0,t 1,t 2,t 3,t 4,t 5] := by
    funext i; fin_cases i <;> rfl
  rw [ht]
  have hz : ∀ a : K, a=0 ∨ a=1 := by decide
  rcases hz (t 0) with c0|c0
  all_goals rcases hz (t 1) with c1|c1
  all_goals rcases hz (t 2) with c2|c2
  all_goals rcases hz (t 3) with c3|c3
  all_goals rcases hz (t 4) with c4|c4
  all_goals rcases hz (t 5) with c5|c5
  all_goals simp only [c0,c1,c2,c3,c4,c5]
  · exact h0
  · exact h32
  · exact h16
  · exact h48
  · exact h8
  · exact h40
  · exact h24
  · exact h56
  · exact h4
  · exact h36
  · exact h20
  · exact h52
  · exact h12
  · exact h44
  · exact h28
  · exact h60
  · exact h2
  · exact h34
  · exact h18
  · exact h50
  · exact h10
  · exact h42
  · exact h26
  · exact h58
  · exact h6
  · exact h38
  · exact h22
  · exact h54
  · exact h14
  · exact h46
  · exact h30
  · exact h62
  · exact h1
  · exact h33
  · exact h17
  · exact h49
  · exact h9
  · exact h41
  · exact h25
  · exact h57
  · exact h5
  · exact h37
  · exact h21
  · exact h53
  · exact h13
  · exact h45
  · exact h29
  · exact h61
  · exact h3
  · exact h35
  · exact h19
  · exact h51
  · exact h11
  · exact h43
  · exact h27
  · exact h59
  · exact h7
  · exact h39
  · exact h23
  · exact h55
  · exact h15
  · exact h47
  · exact h31
  · exact h63

theorem all_good_pairs (t u : Fin 6 → K) (h : GoodPair (t,u)) :
    lineOfPair (t,u) ∈ explicitLines :=
  binaryParameter_cases (fun t => ∀ u, GoodPair (t,u) → lineOfPair (t,u) ∈ explicitLines)
    goodRow0 goodRow1 goodRow2 goodRow3 goodRow4 goodRow5 goodRow6 goodRow7
    goodRow8 goodRow9 goodRow10 goodRow11 goodRow12 goodRow13 goodRow14 goodRow15
    goodRow16 goodRow17 goodRow18 goodRow19 goodRow20 goodRow21 goodRow22 goodRow23
    goodRow24 goodRow25 goodRow26 goodRow27 goodRow28 goodRow29 goodRow30 goodRow31
    goodRow32 goodRow33 goodRow34 goodRow35 goodRow36 goodRow37 goodRow38 goodRow39
    goodRow40 goodRow41 goodRow42 goodRow43 goodRow44 goodRow45 goodRow46 goodRow47
    goodRow48 goodRow49 goodRow50 goodRow51 goodRow52 goodRow53 goodRow54 goodRow55
    goodRow56 goodRow57 goodRow58 goodRow59 goodRow60 goodRow61 goodRow62 goodRow63 t u h

theorem explicitLines_sound (s : Finset V) (hs : s ∈ explicitLines) : IsLine s := by
  simp only [explicitLines,Finset.mem_insert,Finset.mem_singleton] at hs
  rcases hs with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst s
    exact ⟨![1,0,0,0,0,0,0,0],![0,1,0,0,0,0,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,0,0,0],![0,0,1,0,0,0,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,0,0,0],![0,1,1,0,0,0,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,0,0,0,0,0],![0,0,0,0,0,1,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,0,0,0,0,0],![1,0,0,0,0,1,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,0,0,0,0,0],![0,0,1,1,1,1,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,0,0,0,0,0],![1,0,1,1,1,1,0,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,0,0,0,0,0],![0,0,0,0,0,0,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,0,0,0,0,0],![1,0,0,0,0,0,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,0,0,0,0,0],![0,1,0,1,1,0,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,0,0,0,0,0],![1,1,0,1,1,0,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,0,0,0,0,0],![0,0,0,0,0,1,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,0,0,0,0,0],![1,0,0,0,0,1,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,0,0,0,0,0],![0,1,0,1,1,1,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,0,0,0,0,0],![1,1,0,1,1,1,1,0],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,1,0,0],![0,0,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,1,0,0],![0,1,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,1,0,0],![0,0,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,1,0,0],![0,1,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,0,0,1,0,0],![1,0,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,0,0,1,0,0],![1,1,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,0,0,1,0,0],![1,0,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,0,0,1,0,0],![1,1,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,1,1,1,0,0],![0,0,0,0,0,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,1,1,1,0,0],![1,1,0,0,0,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,1,1,1,0,0],![0,0,1,0,0,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,1,1,1,0,0],![1,1,1,0,0,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,1,1,1,0,0],![1,0,1,1,1,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,1,1,1,0,0],![0,1,1,1,1,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,1,1,1,0,0],![1,0,0,1,1,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,1,1,1,0,0],![0,1,0,1,1,0,1,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,0,1,0],![0,0,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,0,1,0],![0,0,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,0,1,0],![0,1,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,0,1,0],![0,1,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,0,0,0,1,0],![1,0,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,0,0,0,1,0],![1,0,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,0,0,0,1,0],![1,1,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,0,0,0,1,0],![1,1,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,1,1,0,1,0],![0,0,0,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,1,1,0,1,0],![1,0,1,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,1,1,0,1,0],![0,1,0,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,1,1,0,1,0],![1,1,1,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,1,1,0,1,0],![1,1,0,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,1,1,0,1,0],![0,1,1,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,1,1,0,1,0],![1,0,0,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,1,1,0,1,0],![0,0,1,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,1,1,0],![0,0,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,0,0,0,1,1,0],![0,1,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,1,1,0],![0,1,0,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,0,0,0,1,1,0],![0,0,1,0,0,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,0,0,1,1,0],![1,0,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,1,0,0,1,1,0],![1,1,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,0,0,1,1,0],![1,1,0,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,1,0,0,1,1,0],![1,0,1,1,1,0,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,1,1,1,1,0],![0,0,0,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,1,0,1,1,1,1,0],![1,1,1,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,1,1,1,1,0],![0,1,0,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,1,0,1,1,1,1,0],![1,0,1,0,0,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,1,1,1,1,0],![1,1,0,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![0,0,1,1,1,1,1,0],![0,0,1,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,1,1,1,1,0],![1,0,0,1,1,1,0,1],by decide +kernel⟩
  · subst s
    exact ⟨![1,0,1,1,1,1,1,0],![0,1,1,1,1,1,0,1],by decide +kernel⟩

theorem lines_eq_explicitLines : lines = explicitLines := by
  apply Finset.Subset.antisymm
  · intro s hs
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hs
    exact all_good_pairs p.1 p.2 (Finset.mem_filter.mp hp).2
  · intro s hs
    exact (mem_lines s).mpr (explicitLines_sound s hs)

theorem card_lines : lines.card = 63 := by rw [lines_eq_explicitLines,card_explicitLines]

theorem card_Line : Nat.card Line = 63 := by
  rw [Nat.card_congr lineEquiv,Nat.card_eq_fintype_card,Fintype.card_coe,card_lines]

def fixedLineEquiv (g : Model K) : {L : Line // g • L = L} ≃
    {s : Finset V // s ∈ explicitFixedLines g} where
  toFun L := ⟨L.val.val,Finset.mem_filter.mpr ⟨by
    rw [← lines_eq_explicitLines]; exact (mem_lines _).mpr L.val.prop,
    congrArg Subtype.val L.prop⟩⟩
  invFun s := ⟨⟨s.val,explicitLines_sound _ (Finset.mem_filter.mp s.prop).1⟩,
    Subtype.ext (Finset.mem_filter.mp s.prop).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fixed_rootA : Nat.card {L : Line // rootA (1 : K) • L = L} = 7 := by
  rw [Nat.card_congr (fixedLineEquiv _),Nat.card_eq_fintype_card,Fintype.card_coe,fixed_rootA_count]

theorem card_fixed_rootF : Nat.card {L : Line // rootF (1 : K) • L = L} = 9 := by
  rw [Nat.card_congr (fixedLineEquiv _),Nat.card_eq_fintype_card,Fintype.card_coe,fixed_rootF_count]

end Atlas.G2.Binary
