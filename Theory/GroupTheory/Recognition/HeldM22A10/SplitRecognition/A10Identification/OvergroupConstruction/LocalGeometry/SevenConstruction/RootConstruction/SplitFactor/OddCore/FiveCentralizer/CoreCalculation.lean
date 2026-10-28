module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.Setup
public import Theory.GroupAction.KleinFourCardinality

/-!
# The odd core of Held's five-element centralizer

Assume the earlier local calculation |C_G(mu) ∩ C_G(w)| = 20.
On K = O(C_G(w)), the fixed subgroups for mu, lambda and mu*lambda
have equal orders because uv cycles the actors. Each fixed order divides
five, and the common fixed subgroup contains the central subgroup <w>.
The Brauer–Wielandt formula therefore gives |K| ≤ 5. Since <w> ≤ K,
we obtain K = <w> and |K| = 5.

The order-twenty calculation remains an explicit premise. This is the
odd-core step of Held's Lemma 5.3, not its final recognition assertion.
Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, printed p.236.
-/

open Subgroup
noncomputable section

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e) (w : G) (hwA : w ∈ L.A)


private theorem fixed_card_conjugate {H : Type*} [Group H]
    (a b c : MulAut H) (h : ∀ x, c (a x) = b (c x)) :
    Nat.card a.fixedSubgroup = Nat.card b.fixedSubgroup := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv c.toEquiv ?_
  intro x
  simp only [MulAut.mem_fixedSubgroup]
  change a x = x ↔ b (c x) = c x
  constructor
  · intro hx
    rw [← h, hx]
  · intro hx
    apply c.injective
    rw [h, hx]

variable [Finite G]

include L hwA

/-- The order-twenty intersection forces the odd core to have order five. -/
public theorem oddCore_card_of_intersection_card (hw : orderOf w = 5)
    (h20 : Nat.card (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) = 20) :
    Nat.card (pPrimeCore 2 (ambient w)) = 5 := by
  let H := ambient w
  let K := pPrimeCore 2 H
  let f : H →* MulAut K := MulAut.conjNormal
  let a := f (first D e L w hwA)
  let b := f (second D e L w hwA)
  have ha : Function.Involutive a := by
    intro k
    change (a * a) k = k
    rw [← pow_two, show a ^ 2 = 1 from by
      dsimp only [a]; rw [← map_pow, first_square, map_one]]
    rfl
  have hb : Function.Involutive b := by
    intro k
    change (b * b) k = k
    rw [← pow_two, show b ^ 2 = 1 from by
      dsimp only [b]; rw [← map_pow, second_square, map_one]]
    rfl
  have hab : Commute a b := (first_commute_second D e L w hwA).map f
  have habcard : Nat.card a.fixedSubgroup = Nat.card b.fixedSubgroup := by
    apply fixed_card_conjugate a b ((f (cycler D e L w hwA))⁻¹)
    intro x
    have he := congrArg f (cycle_first D e L w hwA)
    simp only [map_mul, map_inv] at he
    have he' : (f (cycler D e L w hwA))⁻¹ * a = b * (f (cycler D e L w hwA))⁻¹ := by
      apply (mul_right_cancel_iff (a := f (cycler D e L w hwA))).mp
      simpa only [mul_assoc, inv_mul_cancel, mul_one, a, b] using he
    exact congrArg (fun t : MulAut K => t x) he'
  have hproductcard : Nat.card b.fixedSubgroup = Nat.card (a*b).fixedSubgroup := by
    apply fixed_card_conjugate b (a*b) ((f (cycler D e L w hwA))⁻¹)
    intro x
    have he := congrArg f (cycle_second D e L w hwA)
    simp only [map_mul, map_inv] at he
    have he' : (f (cycler D e L w hwA))⁻¹ * b = (a*b) * (f (cycler D e L w hwA))⁻¹ := by
      apply (mul_right_cancel_iff (a := f (cycler D e L w hwA))).mp
      simpa only [mul_assoc, inv_mul_cancel, mul_one, a, b] using he
    exact congrArg (fun t : MulAut K => t x) he'
  have hd20 : Nat.card a.fixedSubgroup ∣ 20 := by
    let j : a.fixedSubgroup →* (centralizer ({mu D e} : Set G) ⊓ H : Subgroup G) :=
      { toFun := fun x => ⟨x.val.val.val, by
          refine ⟨?_, x.val.val.property⟩
          apply mem_centralizer_singleton_iff.mpr
          have hx := congrArg (fun k : K => ((k : H) : G))
            ((MulAut.mem_fixedSubgroup a x.val).mp x.property)
          change mu D e * x.val.val.val * (mu D e)⁻¹ = x.val.val.val at hx
          exact (mul_inv_eq_iff_eq_mul.mp hx).symm⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    rw [← h20]
    apply card_dvd_of_injective j
    intro x y h
    have hh := congrArg (fun z :
      (centralizer ({mu D e} : Set G) ⊓ H : Subgroup G) => (z : G)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext hh))
  have hd5 : Nat.card a.fixedSubgroup ∣ 5 := by
    have hc : Nat.Coprime (Nat.card a.fixedSubgroup) 4 :=
      ((pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right
        a.fixedSubgroup.card_subgroup_dvd_card).symm.pow_right 2
    exact hc.dvd_of_dvd_mul_left (show Nat.card a.fixedSubgroup ∣ 4 * 5 from hd20)
  have hcommon : 5 ≤ Nat.card (a.fixedSubgroup ⊓ b.fixedSubgroup : Subgroup K) := by
    let R := (kernel w).subgroupOf K
    have hRcard : Nat.card R = 5 :=
      (Nat.card_congr (subgroupOfEquivOfLe (kernel_le_oddCore w hw)).toEquiv).trans
        (kernel_card w hw)
    have hle : R ≤ a.fixedSubgroup ⊓ b.fixedSubgroup := by
      intro x hx
      have hfix (z : H) : f z x = x := by
        apply Subtype.ext
        change z * (x : H) * z⁻¹ = x
        have hc : z * (x : H) = (x : H) * z :=
          mem_center_iff.mp (kernel_le_center w hx) z
        rw [hc, mul_inv_cancel_right]
      exact ⟨(MulAut.mem_fixedSubgroup _ _).mpr (hfix _),
        (MulAut.mem_fixedSubgroup _ _).mpr (hfix _)⟩
    rw [← hRcard]
    exact card_le_of_le hle
  have hodd : Odd (Nat.card K) := Nat.coprime_two_left.mp
    (pPrimeCore_coprime_card (p := 2) (G := H))
  have hformula := Theory.GroupAction.brauerWielandt_fixedSubgroup_card hodd a b ha hb hab
  rw [← hproductcard, ← habcard] at hformula
  have hfixle : Nat.card a.fixedSubgroup ≤ 5 := Nat.le_of_dvd (by decide) hd5
  have hpowle := Nat.pow_le_pow_left hfixle 3
  have hcommon2 : 25 ≤ Nat.card (a.fixedSubgroup ⊓ b.fixedSubgroup : Subgroup K)^2 := by
    nlinarith
  have hmul := Nat.mul_le_mul_left (Nat.card K) hcommon2
  have hKge : 5 ≤ Nat.card K := by
    rw [← kernel_card w hw]
    exact card_le_of_le (kernel_le_oddCore w hw)
  nlinarith

/-- Under the same local premise, the odd core is the central subgroup <w>. -/
public theorem oddCore_eq_kernel_of_intersection_card (hw : orderOf w = 5)
    (h20 : Nat.card (centralizer ({mu D e} : Set G) ⊓ ambient w : Subgroup G) = 20) :
    pPrimeCore 2 (ambient w) = kernel w := by
  symm
  apply eq_of_le_of_card_ge (kernel_le_oddCore w hw)
  rw [kernel_card w hw, oddCore_card_of_intersection_card D e L w hwA hw h20]

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore.FiveCentralizer
