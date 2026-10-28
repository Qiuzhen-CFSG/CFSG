module
public import Theory.GroupAction.ElementaryTwoCyclicFixedOdd
public import Theory.GroupTheory.OddPrimeSectionCentralizers.FullCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.QuotientActionCentralizer

/-!
# Elementary binary action images in odd rank-two sections

Let D be a quotient of a finite group of p-rank at most two, and let R be
a normal p-subgroup of D for p odd. Every elementary two-subgroup B of D
has image of order at most four on R. Each nontrivial image element has
an involution representative in B; the section centralizer theorem makes
its fixed subgroup cyclic. Coprime fixed-point generation bounds the
faithful elementary image, including when the original B has a kernel.

The second theorem uses the literal characteristic restriction to a
subgroup of Oₚ(D). Its kernel contains the kernel of conjugation on the
embedded subgroup, so the same order bound applies to that exact map.

Source: Aschbacher–Smith A.1.31(1–2), printed pp.27–28; the action-rank
step in 14.5.11, printed pp.1015–1016, refs/quasithin.pdf.
-/

open Subgroup
public section
namespace Theory.GroupTheory
variable {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
  {p : ℕ} [Fact p.Prime]

/-- On a normal odd p-subgroup in a rank-two section, every elementary
binary actor has image of order at most four. Rank is kept on the cover. -/
theorem elementary_two_prime_action_card_le_four
    (hp : Odd p) (q : E →* D) (hq : Function.Surjective q)
    (hr : primeRank p E ≤ 2) (R : Subgroup D) [R.Normal] (hR : IsPGroup p R)
    (B : Subgroup D) [IsElementaryAbelian 2 B] :
    Nat.card (B.map (MulAut.conjNormal : D →* MulAut R)) ≤ 4 := by
  let a : D →* MulAut R := MulAut.conjNormal
  let J := B.map a
  let : IsElementaryAbelian 2 J := IsElementaryAbelian.map a
  apply ElementaryTwoCyclicFixedOdd.card_le_four hp hR J.subtype J.subtype_injective
  intro t ht
  obtain ⟨b,hb,hbt⟩ := t.property
  have hbn : b ≠ 1 := by
    intro he
    apply ht
    apply Subtype.ext
    rw [←hbt,he,map_one]
    rfl
  have hb2 : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hb) hbn
  have hbm : b ∉ centralizer (R : Set D) := by
    intro hz
    apply ht
    apply Subtype.ext
    rw [←hbt]
    change b ∈ (MulAut.conjNormal : D →* MulAut R).ker
    rwa [MulAut.conjNormal_ker_eq_centralizer]
  let C := R ⊓ centralizer ({b} : Set D)
  let : IsCyclic C := cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    hp q hq hr R hR b hb2 hbm C (hR.to_le inf_le_left) inf_le_right
  let j : (t : MulAut R).fixedSubgroup →* C :=
    { toFun := fun x => ⟨x.val, x.val.property, mem_centralizer_singleton_iff.mpr (by
        have hx := (MulAut.mem_fixedSubgroup _ _).mp x.property
        have hx' : a b x.val = x.val :=
          (congrArg (fun c : MulAut R => c x.val) hbt).trans hx
        have hh := congrArg (fun z : R => (z : D)) hx'
        change b * (x.val : D) * b⁻¹ = (x.val : D) at hh
        exact (mul_inv_eq_iff_eq_mul.mp hh).symm)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact isCyclic_of_injective j (fun x y h => Subtype.ext (Subtype.ext
    (congrArg (fun z : C => (z : D)) h)))
/-- The order-four bound uses the literal restriction to a characteristic
subgroup of the prime core, as in the supercritical source reduction. -/
theorem characteristic_prime_core_action_card_le_four
    (hp : Odd p) (q : E →* D) (hq : Function.Surjective q)
    (hr : primeRank p E ≤ 2) (R : Subgroup (pCore p D)) [R.Characteristic]
    (B : Subgroup D) [IsElementaryAbelian 2 B] :
    let a := (MulAut.characteristic R).comp
      (MulAut.conjNormal : D →* MulAut (pCore p D))
    Nat.card (B.map a) ≤ 4 := by
  let R' := R.map (pCore p D).subtype
  let : R'.Characteristic := inferInstanceAs (R.map (pCore p D).subtype).Characteristic
  let a := (MulAut.characteristic R).comp
    (MulAut.conjNormal : D →* MulAut (pCore p D))
  let b : D →* MulAut R' := MulAut.conjNormal
  have hk : b.ker ≤ a.ker := by
    rw [MulAut.conjNormal_ker_eq_centralizer]
    intro x hx
    apply MulEquiv.ext
    intro r
    apply Subtype.ext
    apply Subtype.ext
    change x * (r.val : D) * x⁻¹ = (r.val : D)
    rw [←hx (r.val : D) (mem_map_of_mem (pCore p D).subtype r.property),mul_inv_cancel_right]
  apply (card_map_le_card_map_of_ker_le B a b hk).trans
  exact elementary_two_prime_action_card_le_four hp q hq hr R'
    ((pCore_isPGroup (p := p) (G := D)).to_subgroup R |>.map (pCore p D).subtype) B
end Theory.GroupTheory
