module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.CubicFixedProducts

/-!
# Cubic centralizers in the actual octagon radicals

Unique ordered root coordinates restrict bijectively to coordinates fixed by
one Cartan element. Consequently fixed subgroup orders multiply even when
the roots do not commute. If this element fixes one whole root family and
has no nonidentity fixed point on the other family, its centralizers in
the two radicals have orders q³ and q⁴; its centralizer in U has order q⁴.
Both endpoint orientations are retained.

These are the centralizer counts used in Fong--Seitz I (6G), pp.49--51.
The source application constructs the actor and discharges every root
fixed-point premise from the original full panel markings.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure

variable {Y : Type*} [Group Y]

private def infTuple (C : Subgroup Y) (l : List (Subgroup Y)) :
    RootTuple (l.map (fun A => A ⊓ C)) → RootTuple l :=
  match l with
  | [] => id
  | _::l => fun p => (⟨p.1, p.1.property.1⟩, infTuple C l p.2)

private theorem infTuple_injective (C : Subgroup Y) (l : List (Subgroup Y)) :
    Function.Injective (infTuple C l) := by
  induction l with
  | nil => exact Function.injective_id
  | cons A l ih =>
    intro p q he
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun r : RootTuple (A::l) => (r.1 : Y)) he)
    · exact ih (congrArg (fun r : RootTuple (A::l) => r.2) he)

private theorem product_infTuple (C : Subgroup Y) (l : List (Subgroup Y))
    (p : RootTuple (l.map (fun A => A ⊓ C))) :
    rootProduct l (infTuple C l p) = rootProduct (l.map (fun A => A ⊓ C)) p := by
  induction l with
  | nil => rfl
  | cons A l ih =>
    change (p.1 : Y) * rootProduct l (infTuple C l p.2) =
      (p.1 : Y) * rootProduct (l.map (fun A => A ⊓ C)) p.2
    rw [ih]

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

/-- Fixed coordinates are unique, so their orders multiply in every reduced interval. -/
theorem ordered_root_centralizer_card (b : Bool) (n : ℕ)
    (hn : n ≤ rotationOrder Q)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) :
    Nat.card (rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹ ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
      ((orderedRoots Q split b n).map (fun A =>
        Nat.card (A ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
          Subgroup (X ⧸ Q.D)))).prod := by
  let l := orderedRoots Q split b n
  let C := centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D))
  let K := rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹ ⊓ C
  have hinj : Function.Injective (rootProduct l) := by
    intro p q he
    apply (orderedCoordinates Q split b n hn).injective
    apply Subtype.ext
    simpa only [orderedCoordinates_apply] using he
  have he : (K : Set (X ⧸ Q.D)) =
      Set.range (rootProduct (l.map (fun A => A ⊓ C))) := by
    have hh := ordered_root_product_conj_fixed Q split b n hn c
    rw [rootProduct_range, orderedRoots_product Q split b n hn,
      ← rootProduct_range] at hh
    exact hh
  let f : RootTuple (l.map (fun A => A ⊓ C)) → K :=
    fun p => ⟨rootProduct _ p, he.symm.subset (Set.mem_range_self p)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      apply infTuple_injective C l
      apply hinj
      simpa only [product_infTuple] using congrArg Subtype.val hpq
    · intro x
      obtain ⟨p,hp⟩ := he.subset x.property
      exact ⟨p, Subtype.ext hp⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), card_rootTuple]
  simp only [List.map_map, Function.comp_def, l, C]

private theorem right_rep (i : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split i v) (representative w : X ⧸ Q.D) =
      rootAt Q split i (v*w) := rootAt_right Q split i v w _ (representative_spec _)

private theorem right_simple (i : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split i) (representative w : X ⧸ Q.D) =
      rootAt Q split i w := rfl

/-- The seven-root interval is the literal opposite-panel radical. -/
private theorem radical_interval (hm : rotationOrder Q = 8) (b : Bool) :
    rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
      simpleRemainder Q split (if b then 0 else 1) := by
  have he : longest Q = Q.simple (if b then 0 else 1)*alternatingWord Q b 7 := by
    have hh := (alternatingWord_longest Q (!b)).symm
    rw [hm] at hh
    cases b <;> exact hh
  change split.U ⊓ unipotentConjugate split
    (longest Q*(alternatingWord Q b 7)⁻¹) = _
  rw [he,mul_inv_cancel_right]
  rfl

/-- A root-family fixed order determines both radical fixed orders and the
full Sylow fixed order. No commutativity of these products is required. -/
theorem octagon_centralizer_orders_of_root_orders (hm : rotationOrder Q = 8)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D))) (f : Fin 2 → ℕ)
    (hf : ∀ i w, Nat.card (rootAt Q split i w ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = f i) :
    (∀ i j : Fin 2, i ≠ j →
      Nat.card (simpleRemainder Q split i ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
        f i ^ 3 * f j ^ 4) ∧
    Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
      Subgroup (X ⧸ Q.D)) = f 0 ^ 4 * f 1 ^ 4 := by
  have hs (i : Fin 2) : Nat.card (simpleRoot Q split i ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = f i := by
    simpa only [rootAt_one] using hf i 1
  have h0 := ordered_root_centralizer_card Q split true 7 (by omega) c
  have h1 := ordered_root_centralizer_card Q split false 7 (by omega) c
  have hU := ordered_root_centralizer_card Q split false 8 (by omega) c
  rw [radical_interval Q split hm] at h0 h1
  have hu : rootIntersection split (longest Q) (alternatingWord Q false 8)⁻¹ = split.U := by
    rw [← hm, alternatingWord_longest, longest_inv, rootIntersection_longest]
  rw [hu] at hU
  simp only [orderedRoots, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
    List.map_cons, List.map_nil, right_simple, right_rep, List.prod_cons, List.prod_nil,
    hs, hf, mul_one] at h0 h1 hU
  constructor
  · intro i j hij
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact (hij rfl).elim
    · rw [h0]; ring
    · rw [h1]; ring
    · exact (hij rfl).elim
  · rw [hU]; ring

/-- If an actor fixes one entire root family and is fixed-point-free on the
other, its two radical centralizers have orders `q³` and `q⁴`, and the full
Sylow centralizer has order `q⁴`. The endpoints may have either orientation. -/
theorem octagon_separated_root_centralizer_orders (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j)
    (c : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)))
    (hc : ∀ w : Weyl Q,
      (c : X ⧸ Q.D) ∈ centralizer (rootAt Q split i w : Set (X ⧸ Q.D)) ∧
      rootAt Q split j w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) = ⊥) :
    Nat.card (simpleRemainder Q split i ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
        Nat.card (simpleRoot Q split i)^3 ∧
    Nat.card (simpleRemainder Q split j ⊓
      centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
        Nat.card (simpleRoot Q split i)^4 ∧
    Nat.card (split.U ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) :
      Subgroup (X ⧸ Q.D)) = Nat.card (simpleRoot Q split i)^4 := by
  let f : Fin 2 → ℕ := fun k => if k = i then Nat.card (simpleRoot Q split i) else 1
  have hf (k : Fin 2) (w : Weyl Q) :
      Nat.card (rootAt Q split k w ⊓
        centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) = f k := by
    by_cases hki : k = i
    · subst k
      have he : rootAt Q split i w ⊓ centralizer ({(c : X ⧸ Q.D)} : Set (X ⧸ Q.D)) =
          rootAt Q split i w := inf_eq_left.mpr fun x hx =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hc w).1 x hx)
      rw [he, rootAt, card_rightConjugate]
      simp only [f, ↓reduceIte]
    · have hkj : k = j := by omega
      subst k
      rw [(hc w).2, card_bot]
      simp only [f, hki, ↓reduceIte]
  obtain ⟨hR,hU⟩ := octagon_centralizer_orders_of_root_orders Q split hm c f hf
  refine ⟨?_, ?_, ?_⟩
  · simpa only [f, hij.symm, ↓reduceIte, one_pow, mul_one] using hR i j hij
  · simpa only [f, hij.symm, ↓reduceIte, one_pow, one_mul] using hR j i hij.symm
  · rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;>
      simpa [f] using hU

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
