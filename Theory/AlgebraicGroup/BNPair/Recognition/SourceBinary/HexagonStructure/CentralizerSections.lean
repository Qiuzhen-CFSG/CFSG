module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiSections
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.MiddleFixed
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanActions
public import Theory.Frattini.ProductIndex

/-!
# The actual two-root centralizer section in the hexagon

Unique five-root coordinates let a Cartan subgroup's fixed points be tested
coordinatewise. If it acts without fixed points on the three type-i roots
and centralizes the two type-j roots, its radical centralizer is literally
U_j^(s_i) U_j^(s_i s_j). Centralizing R_j makes this an invariant RootSection;
the specified reflection moves its first factor to the disjoint second one.

For an actual nonsolvable Suzuki R_j, the existing effective-section bound
then gives 2^(4b) <= |C/Phi(C)|, while the two root Frattini quotients give
|C/Phi(C)| <= 2^(2b). This is a contradiction on the actual source action.
The fixed-point premises are proved for the source three-core in
SuzukiCartan; they are not asserted by the coordinate or numerical argument.

Source: Fong--Seitz I (6C), printed pp.39--40. All roots and right-conjugation
words belong to the same marked quotient. No whole-panel model is inferred
from an isomorphism of the root-generated subgroup.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem radical_card (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Nat.card (simpleRemainder Q split j) =
      Nat.card (simpleRoot Q split i)^3 * Nat.card (simpleRoot Q split j)^2 := by
  have hu : Nat.card split.U =
      (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))^3 := by
    have hh := unipotent_card_even Q split 3 hm
    have hi : i = 0 ∨ i = 1 := by omega
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact (hij rfl).elim
    · exact hh
    · simpa only [mul_comm] using hh
    · exact (hij rfl).elim
  have hh := unipotent_card_simple Q split j
  rw [hu] at hh
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := simpleRoot Q split j))
  calc
    _ = (Nat.card (simpleRoot Q split i)*Nat.card (simpleRoot Q split j))^3 := hh.symm
    _ = _ := by ring

/-- Unique literal five-root coordinates on the source radical. -/
def radicalCoordinates (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j) :
    (simpleRoot Q split i × rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j) × rootAt Q split i (Q.simple j)) ≃
        simpleRemainder Q split j := by
  let f : (simpleRoot Q split i × rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j) × rootAt Q split i (Q.simple j)) →
        simpleRemainder Q split j := fun z => ⟨(z.1 : X ⧸ Q.D)*z.2.1*z.2.2.1*z.2.2.2.1*z.2.2.2.2, by
          rw [← SetLike.mem_coe, radical_five_product Q split hm i j hij]
          exact ⟨_,⟨_,⟨_,⟨_,z.1.property,_,z.2.1.property,rfl⟩,
            _,z.2.2.1.property,rfl⟩,_,z.2.2.2.1.property,rfl⟩,_,z.2.2.2.2.property,rfl⟩⟩
  apply Equiv.ofBijective f
  apply (Nat.bijective_iff_surjective_and_card f).mpr
  constructor
  · intro x
    have hx := x.property
    rw [← SetLike.mem_coe, radical_five_product Q split hm i j hij] at hx
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,hx⟩ := hx
    exact ⟨(⟨a,ha⟩,⟨b,hb⟩,⟨c,hc⟩,⟨d,hd⟩,⟨e,he⟩),Subtype.ext hx⟩
  · rw [radical_card Q split hm i j hij]
    simp only [Nat.card_prod, rootAt, card_rightConjugate]
    ring

@[simp] theorem radicalCoordinates_apply (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (z : simpleRoot Q split i × rootAt Q split j (Q.simple i) ×
      rootAt Q split i (Q.simple j*Q.simple i) ×
      rootAt Q split j (Q.simple i*Q.simple j) × rootAt Q split i (Q.simple j)) :
    (radicalCoordinates Q split hm i j hij z : X ⧸ Q.D) =
      (z.1 : X ⧸ Q.D)*z.2.1*z.2.2.1*z.2.2.2.1*z.2.2.2.2 := by
  unfold radicalCoordinates
  rfl

/-- The literal fixed subgroup in (6C), before any representation bound.
The three type-i roots have no fixed points, and T fixes both type-j roots. -/
theorem radical_centralizer_product (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (T : Subgroup (X ⧸ Q.D))
    (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hfree : ∀ w, rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w, rootAt Q split j w ≤ centralizer (T : Set (X ⧸ Q.D))) :
    ((simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D))) : Set (X ⧸ Q.D)) =
      (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
      (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let A := simpleRoot Q split i
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split j (Q.simple i*Q.simple j)
  let E := rootAt Q split i (Q.simple j)
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨⟨a,b,c,d,e⟩,he⟩ := (radicalCoordinates Q split hm i j hij).surjective ⟨x,hx.1⟩
    have he' : (a : X ⧸ Q.D)*b*c*d*e = x := congrArg Subtype.val he
    have htuple (t : X ⧸ Q.D) (ht : t ∈ T) :
        (A.normalizerMonoidHom ⟨t,torus_normalizes_simpleRoot Q split i (hTH ht)⟩ a,
         B.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ b,
         C.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ c,
         D.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split j _ (hTH ht)⟩ d,
         E.normalizerMonoidHom ⟨t,rootAt_torus_normalizes Q split i _ (hTH ht)⟩ e) =
          (a,b,c,d,e) := by
      apply (radicalCoordinates Q split hm i j hij).injective
      apply Subtype.ext
      change (t*a*t⁻¹)*(t*b*t⁻¹)*(t*c*t⁻¹)*(t*d*t⁻¹)*(t*e*t⁻¹) = (a : X ⧸ Q.D)*b*c*d*e
      calc
        _ = t*((a : X ⧸ Q.D)*b*c*d*e)*t⁻¹ := by group
        _ = _ := by
          rw [he', mem_centralizer_iff.mp hx.2 t ht, mul_inv_cancel_right]
    have ha : (a : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
      rw [mem_centralizer_iff]
      intro t ht
      exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.1 : X ⧸ Q.D)) (htuple t ht))
    have hc : (c : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
      rw [mem_centralizer_iff]
      intro t ht
      exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.1 : X ⧸ Q.D)) (htuple t ht))
    have hec : (e : X ⧸ Q.D) ∈ centralizer (T : Set (X ⧸ Q.D)) := by
      rw [mem_centralizer_iff]
      intro t ht
      exact mul_inv_eq_iff_eq_mul.mp (congrArg (fun z : A × B × C × D × E => (z.2.2.2.2 : X ⧸ Q.D)) (htuple t ht))
    have ha1 : (a : X ⧸ Q.D) = 1 := mem_bot.mp
      ((by simpa only [rootAt_one] using hfree 1) ▸ ⟨a.property,ha⟩)
    have hc1 : (c : X ⧸ Q.D) = 1 := mem_bot.mp (hfree _ ▸ ⟨c.property,hc⟩)
    have he1 : (e : X ⧸ Q.D) = 1 := mem_bot.mp (hfree _ ▸ ⟨e.property,hec⟩)
    rw [ha1,hc1,he1,one_mul,mul_one,mul_one] at he'
    exact ⟨b,b.property,d,d.property,he'⟩
  · rintro x ⟨b,hb,d,hd,rfl⟩
    refine ⟨?_,mul_mem (hfix _ hb) (hfix _ hd)⟩
    apply middleRoots_le_remainder Q split hm i j hij
    exact mul_mem (mem_sup_left (mem_sup_left hb)) (mem_sup_right hd)

/-- The genuine invariant centralizer section, with bottom denominator. -/
@[expose] def centralizerSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (T : Subgroup (X ⧸ Q.D))
    (hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D))) :
    RootSection Q split j where
  numerator := simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D))
  le_radical := inf_le_left
  normalized :=
    (le_inf ((rankOne_le_parabolic Q split j).trans
        (remainder_parabolic_normalizes Q split j hKj))
      ((le_centralizer_iff.mp hTR).trans (centralizer (T : Set (X ⧸ Q.D))).le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
  denominator := ⊥
  invariant _ := map_bot _

/-- An own-root conjugate detects the actual reflection on the centralizer
section. It is moved to the disjoint root with word s_i s_j. -/
theorem centralizerSection_action_ne_one (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (T : Subgroup (X ⧸ Q.D))
    (hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)))
    (hfix : rootAt Q split j (Q.simple i) ≤ centralizer (T : Set (X ⧸ Q.D))) :
    (centralizerSection Q split j hKj T hTR).action ≠ 1 := by
  let d := centralizerSection Q split j hKj T hTR
  intro he
  apply rootAt_ne_bot Q split j (Q.simple i)
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,
    (middleRoots_le_remainder Q split hm i j hij) (mem_sup_left (mem_sup_left ha)),hfix ha⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  have hx : d.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x))
      (show d.action r⁻¹ = 1 by rw [he]; rfl)
    rw [d.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hxa : (s.val : X ⧸ Q.D)⁻¹*a*s.val = a := by
    have hh := congrArg Subtype.val hx
    rw [d.numeratorAction_apply] at hh
    simpa only [r,x,coe_inv,inv_inv] using hh
  have hconj : a ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [← rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq, ← hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  exact mem_bot.mpr (disjoint_def.mp
    (exchanged_roots_disjoint Q split hm j i hij.symm) ha hconj)

/-- The centralizer product has Frattini index at most the product of the
two root Frattini indices, with exactly the source conjugation words. -/
theorem centralizerSection_frattini_bound (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hfree : ∀ w, rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w, rootAt Q split j w ≤ centralizer (T : Set (X ⧸ Q.D))) :
    let C := simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D))
    Nat.card (C ⧸ frattini C) ≤
      Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j))^2 := by
  let C := simpleRemainder Q split j ⊓ centralizer (T : Set (X ⧸ Q.D))
  have hp := radical_centralizer_product Q split hm i j hij T hTH hfree hfix
  have hle (w) (hw : rootAt Q split j w ≤ simpleRemainder Q split j) :
      rootAt Q split j w ≤ C := le_inf hw (hfix w)
  have hB := hle (Q.simple i) ((show rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j from
    le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij))
  have hD := hle (Q.simple i*Q.simple j) ((show rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j from
    le_sup_right).trans (middleRoots_le_remainder Q split hm i j hij))
  have hh := frattini_index_le_ambient_product _ _ C
    (split.isTwo.to_le (inf_le_left.trans inf_le_left)) hB hD hp
  have hc (w : Weyl Q) :
      Nat.card (rootAt Q split j w ⧸ frattini (rootAt Q split j w)) =
        Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j)) :=
    Nat.card_congr (QuotientGroup.congr _ _
      (ReeSource.RootAction.conjugateEquiv (simpleRoot Q split j) (representative w))
      (frattini_map_equiv _)).toEquiv
  simpa only [hc,pow_two] using hh

/-- The (6C) contradiction on the literal centralizer section. The Cartan
fixed-point hypotheses are mathematical inputs here, not numerical bounds. -/
theorem no_suzuki_centralizer_section (hhex : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    {m : ℕ} (hm : 0 < m)
    (μ : rankOne Q split j ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (hroot : Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j)) ≤ 2^(2*m+1))
    (T : Subgroup (X ⧸ Q.D)) (hTH : T ≤ Q.tits.B ⊓ Q.tits.N)
    (hfree : ∀ w, rootAt Q split i w ⊓ centralizer (T : Set (X ⧸ Q.D)) = ⊥)
    (hfix : ∀ w, rootAt Q split j w ≤ centralizer (T : Set (X ⧸ Q.D))) : False := by
  have hTR : T ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · simpa only [rootAt_one] using hfix 1
    · exact hfix (Q.simple j)
  let d := centralizerSection Q split j hKj T hTR
  have hlo := suzuki_section_card_bound Q split j hm μ d
    (centralizerSection_action_ne_one Q split hhex i j hij s hKj T hTR (hfix _))
  have he : d.effectiveDenominator = frattini d.numerator := by
    rw [d.effectiveDenominator_eq]
    exact sup_bot_eq _
  change 2^(4*(2*m+1)) ≤ d.effectiveDenominator.index at hlo
  rw [he] at hlo
  have hup := centralizerSection_frattini_bound Q split hhex i j hij T hTH hfree hfix
  have hh : 2^(4*(2*m+1)) ≤ 2^(2*(2*m+1)) := by
    calc
      _ ≤ Nat.card (d.numerator ⧸ frattini d.numerator) := hlo
      _ ≤ Nat.card (simpleRoot Q split j ⧸ frattini (simpleRoot Q split j))^2 := hup
      _ ≤ (2^(2*m+1))^2 := Nat.pow_le_pow_left hroot 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hn := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hh
  omega

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
