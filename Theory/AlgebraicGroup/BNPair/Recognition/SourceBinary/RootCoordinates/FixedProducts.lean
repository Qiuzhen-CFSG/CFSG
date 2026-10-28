module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Full Cartan fixed points in ordered root coordinates

Unique products of two disjoint Cartan-normalized subgroups identify their
Cartan-fixed subgroup with the product of the two fixed subgroups. Applying
this at each root-intersection ascent gives the alternating fixed-point
count. An octagon remainder has seven coordinates, with four roots of the
opposite type and three roots of its own type.

The affine octagon exclusion uses this exact count on the original full
Cartan. No commutativity of the whole remainder is assumed. This is the
ordered-coordinate argument underlying Fong--Seitz I (3B), specialized to
the octagon geometry used in (6F), printed pp.45--49.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates

private theorem fixed_product_card {Y : Type*} [Group Y] [Finite Y]
    (A B K H : Subgroup Y) (hA : H ≤ normalizer (A : Set Y))
    (hB : H ≤ normalizer (B : Set Y))
    (hd : Disjoint A B) (hp : (K : Set Y) = (A : Set Y)*(B : Set Y)) :
    Nat.card (K ⊓ centralizer (H : Set Y) : Subgroup Y) =
      Nat.card (A ⊓ centralizer (H : Set Y) : Subgroup Y) *
        Nat.card (B ⊓ centralizer (H : Set Y) : Subgroup Y) := by
  let C := centralizer (H : Set Y)
  let f : ↥(A ⊓ C) × ↥(B ⊓ C) → ↥(K ⊓ C) := fun p =>
    ⟨p.1*p.2,by
      refine ⟨?_,C.mul_mem p.1.property.2 p.2.property.2⟩
      change (p.1 : Y) * (p.2 : Y) ∈ (K : Set Y)
      rw [hp]
      exact ⟨p.1,p.1.property.1,p.2,p.2.property.1,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have hh := mul_injective_of_disjoint hd (a₁ := (⟨p.1,p.1.property.1⟩,⟨p.2,p.2.property.1⟩))
        (a₂ := (⟨q.1,q.1.property.1⟩,⟨q.2,q.2.property.1⟩)) (congrArg Subtype.val he)
      exact Prod.ext (Subtype.ext (congrArg (fun z : A × B => (z.1 : Y)) hh))
        (Subtype.ext (congrArg (fun z : A × B => (z.2 : Y)) hh))
    · intro x
      have hx := x.property.1
      change (x : Y) ∈ (K : Set Y) at hx
      rw [hp] at hx
      obtain ⟨a,ha,b,hb,hab⟩ := hx
      change a*b = (x : Y) at hab
      have hfixed (t : Y) (ht : t ∈ H) : t*a*t⁻¹=a ∧ t*b*t⁻¹=b := by
        have hta := (mem_normalizer_iff.mp (hA ht) a).mp ha
        have htb := (mem_normalizer_iff.mp (hB ht) b).mp hb
        have he : (t*a*t⁻¹)*(t*b*t⁻¹)=a*b := by
          calc
            _ = t*(a*b)*t⁻¹ := by group
            _ = _ := by rw [hab,mem_centralizer_iff.mp x.property.2 t ht,mul_inv_cancel_right]
        have hh := mul_injective_of_disjoint hd
          (a₁ := (⟨t*a*t⁻¹,hta⟩,⟨t*b*t⁻¹,htb⟩)) (a₂ := (⟨a,ha⟩,⟨b,hb⟩)) he
        exact ⟨congrArg (fun z : A × B => (z.1:Y)) hh,
          congrArg (fun z : A × B => (z.2:Y)) hh⟩
      have haC : a ∈ C := mem_centralizer_iff.mpr fun t ht =>
        mul_inv_eq_iff_eq_mul.mp (hfixed t ht).1
      have hbC : b ∈ C := mem_centralizer_iff.mpr fun t ht =>
        mul_inv_eq_iff_eq_mul.mp (hfixed t ht).2
      exact ⟨(⟨a,ha,haC⟩,⟨b,hb,hbC⟩),Subtype.ext hab⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hf),Nat.card_prod]

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private def alternatingFixedOrder (c : Fin 2 → ℕ) : Bool → ℕ → ℕ
  | _, 0 => 1
  | b, n+1 => c (if b then 1 else 0) * alternatingFixedOrder c (!b) n

private theorem interval_fixed_card (b : Bool) (n : ℕ) (hn : n ≤ rotationOrder Q) :
    Nat.card ((rootIntersection split (longest Q) (alternatingWord Q b n)⁻¹) ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
      alternatingFixedOrder (fun i => Nat.card (simpleRoot Q split i ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D))) b n := by
  induction n generalizing b with
  | zero =>
    simp only [alternatingWord,inv_one,rootIntersection_one,bot_inf_eq,card_bot,alternatingFixedOrder]
  | succ n ih =>
    let i : Fin 2 := if b then 1 else 0
    let w := (alternatingWord Q (!b) n)⁻¹
    let s := representative (Q.simple i)
    have hword : (alternatingWord Q b (n+1))⁻¹ = w*Q.simple i := by
      rw [alternatingWord,mul_inv_rev]
      congr 1
      exact inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using
        (Q.tits.involutions _ (Q.simple_mem i)).2)
    have hstep : Q.tits.wordLength (w*Q.simple i) = Q.tits.wordLength w+1 := by
      rw [←hword,wordLength_inv,wordLength_alternatingWord Q b hn]
      dsimp only [w]
      rw [wordLength_inv,wordLength_alternatingWord Q (!b) (by omega)]
    rw [hword]
    rw [fixed_product_card (simpleRoot Q split i)
      (rightConjugate (rootIntersection split (longest Q) w) (s : X ⧸ Q.D))
      _ (Q.tits.B ⊓ Q.tits.N) (torus_normalizes_simpleRoot Q split i)
      (torus_normalizes_rightConjugate _ (torus_normalizes_rootIntersection split _ _) s)
      (rootIntersection_ascent_disjoint Q split w i hstep s (representative_spec _))
      (rootIntersection_ascent_product Q split w i hstep s (representative_spec _))]
    have hcent : rightConjugate (centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)))
        (s : X ⧸ Q.D) = centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) :=
      rightConjugate_eq_self _ (normalizer_le_normalizer_centralizer _ (torus_normalizes s))
    have hmove : rightConjugate (rootIntersection split (longest Q) w) (s : X ⧸ Q.D) ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) =
        rightConjugate (rootIntersection split (longest Q) w ⊓
          centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D))) (s : X ⧸ Q.D) := by
      rw [rightConjugate_inf,hcent]
    rw [hmove,card_rightConjugate,ih (!b) (by omega)]
    rfl

/-- The full Cartan fixed subgroup of an octagon radical has the literal
four-by-three product of the two simple-root fixed orders. -/
theorem octagon_radical_cartan_fixed_card (hm : rotationOrder Q = 8)
    (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split j ⊓
      centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D)) =
      Nat.card (simpleRoot Q split i ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D))^4 *
      Nat.card (simpleRoot Q split j ⊓
        centralizer (↑(Q.tits.B ⊓ Q.tits.N) : Set (X ⧸ Q.D)) : Subgroup (X ⧸ Q.D))^3 := by
  have hrad (b : Bool) :
      rootIntersection split (longest Q) (alternatingWord Q b 7)⁻¹ =
        simpleRemainder Q split (if b then 0 else 1) := by
    have he : longest Q = Q.simple (if b then 0 else 1)*alternatingWord Q b 7 := by
      have hh := (alternatingWord_longest Q (!b)).symm
      rw [hm] at hh
      cases b <;> exact hh
    change split.U ⊓ unipotentConjugate split (longest Q*(alternatingWord Q b 7)⁻¹) = _
    rw [he,mul_inv_cancel_right]
    rfl
  have h0 := interval_fixed_card Q split false 7 (by omega)
  have h1 := interval_fixed_card Q split true 7 (by omega)
  rw [hrad] at h0 h1
  simp only [alternatingFixedOrder,Bool.false_eq_true,↓reduceIte,Bool.not_false,Bool.not_true,mul_one] at h0 h1
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact (hij rfl).elim
  · rw [h0]; ring
  · rw [h1]; ring
  · exact (hij rfl).elim

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
