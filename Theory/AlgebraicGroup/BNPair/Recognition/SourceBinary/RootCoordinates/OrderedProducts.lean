module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.Recurrence
/-!
# Unique ordered positive-root products

Iterate the right-ascent recurrence along reduced alternating words.
For w = (sᵢ₁⋯sᵢₖ)⁻¹ the ordered list begins with Xᵢ₁; every remaining
factor is conjugated on the right by a lift of sᵢ₁. Iterating gives actual
subgroups of U, each a conjugate in the original N of one of the two
original simple roots. The list has length k, and its product is U_w.
The corresponding iterated Cartesian product maps bijectively to U_w by
literal ordered multiplication. At the longest word this gives unique
coordinates on all of U, together with its product-of-root-orders formula.
The full H normalizes every factor. In particular a normal subgroup
containing both original simple roots contains U, the generation premise
used by the whole-quotient recognition argument.

Source: Carter 2.5.10, 2.5.12 and 2.5.17,
`refs/KGroup/GLS3/Chapter2Ca2.tex`. No root commutator relation is used.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
universe u
variable {Y : Type u} [Group Y]

/-- Coordinates in an ordered list of subgroups, without commutation assumptions. -/
@[expose] def RootTuple : List (Subgroup Y) → Type u
  | [] => PUnit
  | A::l => A × RootTuple l

/-- Multiply coordinates in the stated order. -/
@[expose] def rootProduct : (l : List (Subgroup Y)) → RootTuple l → Y
  | [], _ => 1
  | _::l, p => p.1 * rootProduct l p.2

/-- Right conjugation transports a subgroup's elements bijectively. -/
def rightConjugateEquiv (A : Subgroup Y) (n : Y) : A ≃ rightConjugate A n :=
  { toFun := fun a => ⟨n⁻¹*a*n, by
      change n*(n⁻¹*(a:Y)*n)*n⁻¹ ∈ A
      simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel_right, mul_inv_cancel, mul_one] using a.property⟩
    invFun := fun a => ⟨n*a*n⁻¹, a.property⟩
    left_inv := by intro a; apply Subtype.ext; simp [mul_assoc]
    right_inv := by intro a; apply Subtype.ext; simp [mul_assoc] }

@[simp] theorem rightConjugateEquiv_apply (A : Subgroup Y) (n : Y) (a : A) :
    (rightConjugateEquiv A n a : Y) = n⁻¹*a*n := by rfl

/-- Transport every coordinate through the same right conjugation. -/
def conjugateTuple (l : List (Subgroup Y)) (n : Y) :
    RootTuple l ≃ RootTuple (l.map (fun A => rightConjugate A n)) :=
  match l with
  | [] => Equiv.refl _
  | A::l => Equiv.prodCongr (rightConjugateEquiv A n) (conjugateTuple l n)

theorem rootProduct_conjugateTuple (l : List (Subgroup Y)) (n : Y) (p : RootTuple l) :
    rootProduct (l.map (fun A => rightConjugate A n)) (conjugateTuple l n p) =
      n⁻¹*rootProduct l p*n := by
  induction l with
  | nil => change 1 = n⁻¹*1*n; simp
  | cons A l ih =>
    change (n⁻¹*(p.1:Y)*n)*rootProduct _ (conjugateTuple l n p.2) = _
    rw [ih]
    simp only [rootProduct, mul_assoc, mul_inv_cancel_left]

theorem rootProduct_range (l : List (Subgroup Y)) :
    Set.range (rootProduct l) = (l.map (fun A => (A : Set Y))).prod := by
  induction l with
  | nil =>
    ext x
    simp [rootProduct, RootTuple, Set.mem_one]
  | cons A l ih =>
    ext x
    change (∃ p : A × RootTuple l, (p.1:Y)*rootProduct l p.2 = x) ↔
      x ∈ (A:Set Y)*((l.map (fun C => (C:Set Y))).prod)
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.1,p.1.property,rootProduct l p.2,ih ▸ ⟨p.2,rfl⟩,rfl⟩
    · rintro ⟨a,ha,z,hz,rfl⟩
      rw [← ih] at hz
      obtain ⟨p,rfl⟩ := hz
      exact ⟨(⟨a,ha⟩,p),rfl⟩

theorem rootProduct_mem (l : List (Subgroup Y)) (K : Subgroup Y)
    (hK : ∀ A ∈ l, A ≤ K) (p : RootTuple l) : rootProduct l p ∈ K := by
  induction l with
  | nil => exact K.one_mem
  | cons A l ih =>
    exact K.mul_mem (hK A (by simp) p.1.property)
      (ih (fun C hC => hK C (List.mem_cons_of_mem _ hC)) p.2)

private theorem one_mem_subgroup_product (l : List (Subgroup Y)) :
    (1:Y) ∈ (l.map (fun A => (A:Set Y))).prod := by
  induction l with
  | nil => exact rfl
  | cons A l ih => exact ⟨1,A.one_mem,1,ih,one_mul _⟩

private theorem subgroup_le_product_of_mem (l : List (Subgroup Y))
    (A : Subgroup Y) (hA : A ∈ l) :
    (A:Set Y) ⊆ (l.map (fun C => (C:Set Y))).prod := by
  induction l with
  | nil => simp at hA
  | cons C l ih =>
    rcases List.mem_cons.mp hA with rfl | hA
    · intro a ha
      exact ⟨a,ha,1,one_mem_subgroup_product l,mul_one _⟩
    · intro a ha
      exact ⟨1,C.one_mem,a,ih hA ha,one_mul _⟩

theorem card_rootTuple (l : List (Subgroup Y)) :
    Nat.card (RootTuple l) = (l.map (fun A : Subgroup _ => Nat.card A)).prod := by
  induction l with
  | nil => simp [RootTuple]
  | cons A l ih =>
    change Nat.card (A × RootTuple l) = Nat.card A*(l.map (fun C : Subgroup _ => Nat.card C)).prod
    rw [Nat.card_prod, ih]

private def subgroupTypeCongr {A C : Subgroup Y} (h : A = C) : A ≃ C :=
  { toFun := fun a => ⟨a,h ▸ a.property⟩
    invFun := fun a => ⟨a,h.symm ▸ a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (d : MarkedQuotient P) (split : SplitData d.tits)

/-- The positive factors obtained by iterating Carter's recurrence.
The first factor is Xᵢ and the remaining factors are conjugated by nᵢ. -/
@[expose] def orderedRoots : Bool → ℕ → List (Subgroup (X ⧸ d.D))
  | _, 0 => []
  | b, n+1 => simpleRoot d split (if b then 1 else 0) ::
      (orderedRoots (!b) n).map (fun A =>
        rightConjugate A (representative (d.simple (if b then 1 else 0)) : X ⧸ d.D))

theorem orderedRoots_length (b : Bool) (n : ℕ) : (orderedRoots d split b n).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp only [orderedRoots, List.length_cons, List.length_map, ih]

private theorem alternatingWord_inv_step (b : Bool) (n : ℕ) :
    (alternatingWord d b (n+1))⁻¹ =
      (alternatingWord d (!b) n)⁻¹*d.simple (if b then 1 else 0) := by
  have hi : (d.simple (if b then 1 else 0))⁻¹ = d.simple (if b then 1 else 0) :=
    inv_eq_of_mul_eq_one_right (by
      simpa only [pow_two] using (d.tits.involutions _ (d.simple_mem _)).2)
  rw [alternatingWord, mul_inv_rev, hi]

/-- Unique ordered root coordinates for every reduced alternating word. -/
def orderedCoordinates (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d) :
    RootTuple (orderedRoots d split b n) ≃
      rootIntersection split (longest d) (alternatingWord d b n)⁻¹ :=
  match n with
  | 0 =>
    { toFun := fun _ => ⟨1, one_mem _⟩
      invFun := fun _ => PUnit.unit
      left_inv := by intro p; cases p; rfl
      right_inv := by
        intro u
        apply Subtype.ext
        have hu := u.property
        simp only [alternatingWord, inv_one] at hu
        rw [rootIntersection_one, mem_bot] at hu
        exact hu.symm }
  | n+1 =>
    let i : Fin 2 := if b then 1 else 0
    let ni := representative (d.simple i)
    let w := (alternatingWord d (!b) n)⁻¹
    have hstep : d.tits.wordLength (w*d.simple i) = d.tits.wordLength w+1 := by
      rw [← alternatingWord_inv_step d b n, wordLength_inv, wordLength_inv,
        wordLength_alternatingWord d b hn,
        wordLength_alternatingWord d (!b) (by omega)]
    (Equiv.prodCongr (Equiv.refl _) ((conjugateTuple (orderedRoots d split (!b) n) (ni:X ⧸ d.D)).symm.trans
      ((orderedCoordinates (!b) n (by omega)).trans
        (rightConjugateEquiv (rootIntersection split (longest d) w) (ni:X ⧸ d.D))))).trans
      ((ascentCoordinates d split w i hstep ni (representative_spec _)).trans
        (subgroupTypeCongr (congrArg (fun v => rootIntersection split (longest d) v)
          (alternatingWord_inv_step d b n).symm)))

theorem orderedCoordinates_apply (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d)
    (p : RootTuple (orderedRoots d split b n)) :
    (orderedCoordinates d split b n hn p : X ⧸ d.D) =
      rootProduct (orderedRoots d split b n) p := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih =>
    let ni := representative (d.simple (if b then 1 else 0))
    let tail := (conjugateTuple (orderedRoots d split (!b) n) (ni:X ⧸ d.D)).symm p.2
    have hp := rootProduct_conjugateTuple (orderedRoots d split (!b) n) (ni:X ⧸ d.D) tail
    rw [Equiv.apply_symm_apply] at hp
    have hstep : d.tits.wordLength ((alternatingWord d (!b) n)⁻¹*d.simple (if b then 1 else 0)) =
        d.tits.wordLength ((alternatingWord d (!b) n)⁻¹)+1 := by
      rw [← alternatingWord_inv_step d b n, wordLength_inv, wordLength_inv,
        wordLength_alternatingWord d b hn,
        wordLength_alternatingWord d (!b) (by omega)]
    change (ascentCoordinates d split (alternatingWord d (!b) n)⁻¹ (if b then 1 else 0)
      hstep ni (representative_spec _) (p.1,
        rightConjugateEquiv _ (ni:X ⧸ d.D)
          (orderedCoordinates d split (!b) n (by omega) tail)) : X ⧸ d.D) = _
    rw [ascentCoordinates_apply, rightConjugateEquiv_apply, ih]
    exact congrArg (fun z : X ⧸ d.D => (p.1:X ⧸ d.D)*z) hp.symm

/-- Every positive factor is a conjugate in the same N of one of the same two roots. -/
theorem orderedRoots_are_simple_conjugates (b : Bool) (n : ℕ)
    (A : Subgroup (X ⧸ d.D)) (hA : A ∈ orderedRoots d split b n) :
    ∃ i : Fin 2, ∃ ni : d.tits.N,
      A = rightConjugate (simpleRoot d split i) (ni : X ⧸ d.D) := by
  induction n generalizing b A with
  | zero => simp [orderedRoots] at hA
  | succ n ih =>
    rcases List.mem_cons.mp hA with h | h
    · subst A
      exact ⟨if b then 1 else 0,1,by simp only [coe_one, rightConjugate_one]⟩
    · obtain ⟨C,hC,rfl⟩ := List.mem_map.mp h
      obtain ⟨i,ni,rfl⟩ := ih (!b) C hC
      refine ⟨i,ni*representative (d.simple (if b then 1 else 0)),?_⟩
      exact (rightConjugate_mul _ _ _).symm

/-- The ordered set product is exactly the indicated root intersection. -/
theorem orderedRoots_product (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d) :
    ((orderedRoots d split b n).map (fun A => (A : Set (X ⧸ d.D)))).prod =
      rootIntersection split (longest d) (alternatingWord d b n)⁻¹ := by
  rw [← rootProduct_range]
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    rw [← orderedCoordinates_apply d split b n hn]
    exact (orderedCoordinates d split b n hn p).property
  · intro hx
    obtain ⟨p,hp⟩ := (orderedCoordinates d split b n hn).surjective ⟨x,hx⟩
    refine ⟨p,?_⟩
    rw [← orderedCoordinates_apply d split b n hn]
    exact congrArg Subtype.val hp

/-- Every factor is positive: it lies in the indicated root intersection. -/
theorem orderedRoots_le (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d)
    (A : Subgroup (X ⧸ d.D)) (hA : A ∈ orderedRoots d split b n) :
    A ≤ rootIntersection split (longest d) (alternatingWord d b n)⁻¹ := by
  have h := subgroup_le_product_of_mem (orderedRoots d split b n) A hA
  rwa [orderedRoots_product d split b n hn] at h

/-- The entire original H normalizes every positive factor. -/
theorem orderedRoots_torus_normalizes (b : Bool) (n : ℕ)
    (A : Subgroup (X ⧸ d.D)) (hA : A ∈ orderedRoots d split b n) :
    d.tits.B ⊓ d.tits.N ≤ normalizer (A : Set (X ⧸ d.D)) := by
  obtain ⟨i,ni,rfl⟩ := orderedRoots_are_simple_conjugates d split b n A hA
  exact torus_normalizes_rightConjugate (simpleRoot d split i)
    (torus_normalizes_simpleRoot d split i) ni

theorem rootIntersection_card_ordered (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder d) :
    Nat.card (rootIntersection split (longest d) (alternatingWord d b n)⁻¹) =
      ((orderedRoots d split b n).map (fun A : Subgroup _ => Nat.card A)).prod := by
  rw [← Nat.card_congr (orderedCoordinates d split b n hn), card_rootTuple]

/-- Longest-word coordinates give unique ordered positive-root coordinates on U. -/
def unipotentOrderedCoordinates (b : Bool) :
    RootTuple (orderedRoots d split b (rotationOrder d)) ≃ split.U :=
  (orderedCoordinates d split b (rotationOrder d) le_rfl).trans
    (subgroupTypeCongr (by
      rw [alternatingWord_longest, longest_inv, rootIntersection_longest]))

@[simp] theorem unipotentOrderedCoordinates_apply (b : Bool)
    (p : RootTuple (orderedRoots d split b (rotationOrder d))) :
    (unipotentOrderedCoordinates d split b p : X ⧸ d.D) =
      rootProduct (orderedRoots d split b (rotationOrder d)) p := by
  dsimp only [unipotentOrderedCoordinates, Equiv.trans_apply, subgroupTypeCongr]
  exact orderedCoordinates_apply d split b (rotationOrder d) le_rfl p

/-- The actual positive-root factorization of U, for either alternating expression. -/
theorem unipotent_ordered_product (b : Bool) :
    ((orderedRoots d split b (rotationOrder d)).map (fun A => (A : Set (X ⧸ d.D)))).prod =
      split.U := by
  rw [orderedRoots_product d split b _ le_rfl, alternatingWord_longest, longest_inv,
    rootIntersection_longest]

/-- The order of U is literally the product of the positive-root orders. -/
theorem unipotent_card_ordered (b : Bool) :
    Nat.card split.U =
      ((orderedRoots d split b (rotationOrder d)).map (fun A : Subgroup _ => Nat.card A)).prod := by
  rw [← Nat.card_congr (unipotentOrderedCoordinates d split b), card_rootTuple]

/-- A normal subgroup containing both original simple roots contains U.
This is the root-coordinate premise in the whole-quotient recognition route. -/
theorem unipotent_le_normal_of_simpleRoots_le (K : Subgroup (X ⧸ d.D)) [K.Normal]
    (hK : ∀ i, simpleRoot d split i ≤ K) : split.U ≤ K := by
  intro x hx
  obtain ⟨p,hp⟩ := (unipotentOrderedCoordinates d split false).surjective ⟨x,hx⟩
  have hm := rootProduct_mem (orderedRoots d split false (rotationOrder d)) K (by
    intro A hA
    obtain ⟨i,ni,rfl⟩ := orderedRoots_are_simple_conjugates d split false _ A hA
    intro a ha
    have hb : (ni:X ⧸ d.D)*a*(ni:X ⧸ d.D)⁻¹ ∈ K := hK i ha
    have hc := (inferInstance : K.Normal).conj_mem _ hb (ni:X ⧸ d.D)⁻¹
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hc) p
  have he : rootProduct (orderedRoots d split false (rotationOrder d)) p = x :=
    (unipotentOrderedCoordinates_apply d split false p).symm.trans (congrArg Subtype.val hp)
  rwa [he] at hm

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
