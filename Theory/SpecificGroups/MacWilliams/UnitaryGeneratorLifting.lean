module

public import Theory.SpecificGroups.MacWilliams.UnitaryFrame
public import Theory.GroupTheory.PGroup.ThreeInvolutionOrder

/-!
# Central-quotient squares and lifting unitary frames

For a group of exponent four with elementary center and central involutions,
squaring descends to an anisotropic quadratic map on the central quotient.
Central commutators give its bilinear polar map. We retain the evaluation
identities, including the presentation convention `x⁻¹ * y⁻¹ * x * y`.
The square-map construction adapts the proof in
`IsPGroup.exists_anisotropic_center_quotient_square_map` without changing that
shared interface.

For a group of order 64 with three automorphism-transitive involutions and
center of order four, each nonidentity square fiber has twenty elements,
hence five central cosets. A supplied unitary quadratic frame then lifts to
the exact generating relations: choose representatives for coordinates 0–3
and the specified central elements for coordinates 4–5. These elements
generate both the center and the central quotient, so they generate the group.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(b), printed p.386,
and MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped commutatorElement
namespace MacWilliamsSylow

/-- The central-quotient square and polar maps with their quadratic laws and
explicit evaluation on representatives. The polar convention is `rightComm`. -/
public theorem exists_center_quotient_square_data
    {P : Type*} [Group P] [IsElementaryAbelian 2 (center P)]
    (hD : commutator P ≤ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hexp : ∀ x : P, x ^ 4 = 1) :
    ∃ (square : P ⧸ center P → center P)
      (polar : P ⧸ center P → P ⧸ center P → center P),
      square 1 = 1 ∧
      (∀ x y, square (x * y) = square x * square y * polar x y) ∧
      (∀ x y z, polar (x * y) z = polar x z * polar y z) ∧
      (∀ x, square x = 1 → x = 1) ∧
      (∀ x : P, (square (QuotientGroup.mk x) : P) = x ^ 2) ∧
      (∀ x y : P, (polar (QuotientGroup.mk x) (QuotientGroup.mk y) : P) =
        rightComm x y) := by
  have hsq (x : P) : x ^ 2 ∈ center P :=
    hcentral _ (by simpa only [← pow_mul] using hexp x)
  have hZ (z : P) (hz : z ∈ center P) : z ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian z hz
  have hsame (x y : P)
      (hxy : QuotientGroup.mk' (center P) x = QuotientGroup.mk' (center P) y) :
      x ^ 2 = y ^ 2 := by
    have hm : x⁻¹ * y ∈ center P := QuotientGroup.eq.mp hxy
    have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp hm x
    have he := hc.mul_pow 2
    simpa only [mul_inv_cancel_left, hZ _ hm, mul_one] using he.symm
  let square : P ⧸ center P → center P :=
    Quotient.lift (fun x => ⟨x ^ 2, hsq x⟩) (by
      intro x y hxy
      exact Subtype.ext (hsame x y (Quotient.sound hxy)))
  have hsquare (x : P) : (square (QuotientGroup.mk' (center P) x) : P) = x ^ 2 := rfl
  let polar (x y : P ⧸ center P) : center P :=
    (square x * square y)⁻¹ * square (x * y)
  have hcomm (x y : P) : ⁅x,y⁆ ∈ center P :=
    hD (commutator_mem_commutator (mem_top x) (mem_top y))
  have hmul (x y : P) : (x * y) ^ 2 = x ^ 2 * y ^ 2 * ⁅x,y⁆ := by
    have hx : ∀ z : P, z * x ^ 2 = x ^ 2 * z := mem_center_iff.mp (hsq x)
    have hc : ∀ z : P, z * ⁅x,y⁆ = ⁅x,y⁆ * z := mem_center_iff.mp (hcomm x y)
    symm
    calc
      x ^ 2 * y ^ 2 * ⁅x,y⁆ = ⁅x,y⁆ * (x ^ 2 * y ^ 2) := hc _
      _ = x * y * x⁻¹ * (y⁻¹ * x ^ 2) * y ^ 2 := by
        simp only [commutatorElement_def, mul_assoc]
      _ = x * y * x⁻¹ * (x ^ 2 * y⁻¹) * y ^ 2 := by rw [hx]
      _ = (x * y) ^ 2 := by simp only [pow_two]; group
  have hpolar (x y : P) :
      (polar (QuotientGroup.mk' (center P) x) (QuotientGroup.mk' (center P) y) : P) =
        ⁅x,y⁆ := by
    change (x ^ 2 * y ^ 2)⁻¹ * (x * y) ^ 2 = _
    rw [hmul, inv_mul_cancel_left]
  refine ⟨square, polar, ?_, ?_, ?_, ?_, hsquare, ?_⟩
  · exact Subtype.ext (one_pow 2)
  · intro x y
    simp only [polar, mul_inv_cancel_left]
  · intro x y z
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        induction z using QuotientGroup.induction_on with
        | H z =>
          apply Subtype.ext
          change (polar (QuotientGroup.mk' (center P) (x * y))
              (QuotientGroup.mk' (center P) z) : P) =
            (polar (QuotientGroup.mk' (center P) x) (QuotientGroup.mk' (center P) z) : P) *
            (polar (QuotientGroup.mk' (center P) y) (QuotientGroup.mk' (center P) z) : P)
          simp only [hpolar]
          rw [commutatorElement_mul_left_eq_conj_mul]
          have hc := mem_center_iff.mp (hcomm y z)
          rw [hc x]
          simp only [mul_assoc, mul_inv_cancel, mul_one]
          exact (hc ⁅x,z⁆).symm
  · intro x hx
    induction x using QuotientGroup.induction_on with
    | H x =>
      apply (QuotientGroup.eq_one_iff x).mpr
      exact hcentral x (congrArg Subtype.val hx)

  · intro x y
    change (polar (QuotientGroup.mk' (center P) x) (QuotientGroup.mk' (center P) y) : P) = _
    rw [hpolar]
    have hc := mem_center_iff.mp (hcomm x y)
    have he : rightComm x y = ⁅x⁻¹, y⁻¹⁆ := by
      simp only [rightComm, commutatorElement_def, inv_inv]
    rw [he, commutatorElement_inv_left, commutatorElement_inv_left,
      hc y⁻¹, mul_assoc ⁅x,y⁆ y⁻¹ y, inv_mul_cancel, mul_one,
      hc x⁻¹, mul_assoc, inv_mul_cancel, mul_one]

/-- Lift a quadratic frame using arbitrary representatives of its first four
coordinates and its prescribed central generators in the last two. -/
public theorem UnitaryQuadraticFrame.exists_generating_lifts
    {P : Type*} [Group P]
    {square : P ⧸ center P → center P}
    {polar : P ⧸ center P → P ⧸ center P → center P}
    (hsquare : ∀ x : P, (square (QuotientGroup.mk x) : P) = x ^ 2)
    (hpolar : ∀ x y : P,
      (polar (QuotientGroup.mk x) (QuotientGroup.mk y) : P) = rightComm x y)
    (F : UnitaryQuadraticFrame square polar) :
    ∃ x : Fin 6 → P, Relations unitaryTable x ∧ closure (Set.range x) = ⊤ := by
  classical
  let q := QuotientGroup.mk' (center P)
  obtain ⟨r, hr⟩ : ∃ r : Fin 6 → P, ∀ i, q (r i) = F.quotientGenerator i := by
    choose r hr using fun i => QuotientGroup.mk'_surjective (center P) (F.quotientGenerator i)
    exact ⟨r, hr⟩
  let x (i : Fin 6) : P := if i.val < 4 then r i else F.centralGenerator i
  have hxlast (i : Fin 6) (hi : 4 ≤ i.val) : x i = F.centralGenerator i := by
    simp [x, show ¬i.val < 4 by omega]
  have hxq (i : Fin 6) : q (x i) = F.quotientGenerator i := by
    by_cases hi : i.val < 4
    · simp [x, hi, hr]
    · rw [hxlast i (by omega), F.quotient_last i (by omega)]
      exact (QuotientGroup.eq_one_iff _).mpr (F.centralGenerator i).property
  have hword (w : List (Fin 6)) (hw : ∀ i ∈ w, 4 ≤ i.val) :
      word x w = ((word F.centralGenerator w : center P) : P) := by
    change word x w = (center P).subtype (word F.centralGenerator w)
    rw [map_word]
    unfold word
    congr 1
    exact List.map_congr_left fun i hi => hxlast i (hw i hi)
  have hswords (i : Fin 6) : ∀ j ∈ unitaryTable.square i, 4 ≤ j.val := by
    fin_cases i <;> simp [unitaryTable]
  have hcwords (i j : Fin 6) : ∀ k ∈ unitaryTable.commutator j i, 4 ≤ k.val := by
    fin_cases i <;> fin_cases j <;> simp [unitaryTable]
  refine ⟨x, ⟨?_, ?_⟩, ?_⟩
  · intro i
    rw [hword _ (hswords i), ← F.square_eq, ← hxq]
    exact (pow_two (x i)).symm.trans (hsquare (x i)).symm
  · intro i j hij
    rw [hword _ (hcwords i j), ← F.polar_eq i j hij, ← hxq, ← hxq]
    exact (hpolar (x j) (x i)).symm
  · let H := closure (Set.range x)
    have hxmem (i) : x i ∈ H := subset_closure ⟨i, rfl⟩
    have hZ : center P ≤ H := by
      have hh : closure (Set.range F.centralGenerator) ≤ H.comap (center P).subtype := by
        rw [closure_le]
        rintro _ ⟨i, rfl⟩
        change (F.centralGenerator i : P) ∈ H
        by_cases hi : i.val < 4
        · rw [F.central_first i hi]
          exact H.one_mem
        · rw [← hxlast i (by omega)]
          exact hxmem i
      rw [F.central_closure] at hh
      intro z hz
      exact hh (show (⟨z, hz⟩ : center P) ∈ ⊤ from mem_top _)
    have hmap : H.map q = ⊤ := by
      change (closure (Set.range x)).map q = ⊤
      rw [MonoidHom.map_closure, ← Set.range_comp]
      simpa only [Function.comp_def, hxq] using F.quotient_closure
    have hker : q.ker ≤ H := by
      simpa only [q, QuotientGroup.ker_mk'] using hZ
    have hh := congrArg (Subgroup.comap q) hmap
    rwa [comap_map_eq_self hker, comap_top] at hh

/-- Nonzero quotient square fibers contain five cosets: their twenty group
square roots split into central cosets of size four. -/
public theorem card_center_quotient_square_fiber
    {P : Type*} [Group P] [Finite P] [IsElementaryAbelian 2 (center P)]
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) (hcard : Nat.card P = 64)
    (hZcard : Nat.card (center P) = 4)
    (square : P ⧸ center P → center P)
    (hsquare : ∀ x : P, (square (QuotientGroup.mk x) : P) = x ^ 2)
    (z : center P) (hz : z ≠ 1) : Nat.card {v // square v = z} = 5 := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzorder : orderOf (z : P) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z : P) z.property)
    (fun h => hz (Subtype.ext h))
  have hcount := IsPGroup.card_eq_four_add_three_mul_square_fiber
    hcentral hthree htrans hexp (z : P) hzorder
  have he : {x : P // x ^ 2 = (z : P)} ≃ {v // square v = z} × center P :=
    (Equiv.subtypeEquiv (groupEquivQuotientProdSubgroup (s := center P))
      (p := fun x => x ^ 2 = (z : P))
      (q := fun v : (P ⧸ center P) × center P => square v.1 = z) (fun x => by
        change x ^ 2 = (z : P) ↔ square (QuotientGroup.mk x) = z
        rw [← hsquare x, Subtype.ext_iff])).trans
      (@Equiv.prodSubtypeFstEquivSubtypeProd (P ⧸ center P) (center P)
        (fun v => square v = z))
  have hf := Nat.card_congr he
  rw [Nat.card_prod, hZcard] at hf
  rw [hcard, hf] at hcount
  omega

/-- The actual central-quotient quadratic data, balanced over the three nonzero
central values, together with the lift of every supplied unitary frame.
No existence or classification of quadratic frames is assumed here. -/
public theorem exists_balanced_square_data_and_generating_lifts
    {P : Type*} [Group P] [Finite P] [IsElementaryAbelian 2 (center P)]
    (hD : commutator P ≤ center P)
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (htrans : ∀ x y : P, orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut P, a x = y)
    (hexp : ∀ x : P, x ^ 4 = 1) (hcard : Nat.card P = 64)
    (hZcard : Nat.card (center P) = 4) :
    ∃ (square : P ⧸ center P → center P)
      (polar : P ⧸ center P → P ⧸ center P → center P),
      square 1 = 1 ∧
      (∀ x y, square (x * y) = square x * square y * polar x y) ∧
      (∀ x y z, polar (x * y) z = polar x z * polar y z) ∧
      (∀ x, square x = 1 → x = 1) ∧
      (∀ x : P, (square (QuotientGroup.mk x) : P) = x ^ 2) ∧
      (∀ x y : P, (polar (QuotientGroup.mk x) (QuotientGroup.mk y) : P) =
        rightComm x y) ∧
      (∀ z : center P, z ≠ 1 → Nat.card {v // square v = z} = 5) ∧
      (∀ _F : UnitaryQuadraticFrame square polar,
        ∃ x : Fin 6 → P, Relations unitaryTable x ∧ closure (Set.range x) = ⊤) := by
  obtain ⟨square, polar, h1, hq, hb, ha, hs, hp⟩ :=
    exists_center_quotient_square_data hD hcentral hexp
  exact ⟨square, polar, h1, hq, hb, ha, hs, hp,
    card_center_quotient_square_fiber hcentral hthree htrans hexp hcard hZcard square hs,
    fun F => F.exists_generating_lifts hs hp⟩

end MacWilliamsSylow
