module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.NormalForm.Coefficients
public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist

/-!
# Reduction of triality involution cocycles to the actual Sylow subgroup

Let sigma preserve a Sylow two-subgroup U and satisfy sigma² = 1. For any
cocycle g * sigma(g) = 1, the map xU ↦ g * sigma(x)U is an involution on the
odd-sized coset space. A fixed coset supplies h with h⁻¹*g*sigma(h) in U.
This is still a cocycle, and a solution there gives a solution in the full
group, with the literal conjugating-element orientation retained.

The application below uses the proved coefficient action on the original
positive subgroup, its actual Sylow witness, and the canonical Frobenius
involution. Only the positive-subgroup cocycle calculation remains explicit;
no ambient algebraic-group comparison or general Lang theorem is needed for
this reduction. The scalar root-coordinate calculation is a separate input.

Application: the field-involution case of Aschbacher–Smith 16.1.3–4,
printed p.1171, `refs/quasithin.pdf`. The field convention and Lang
interpretation are GLS3 §§2.1 and 2.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm
open OuterOdd Parabolics

private theorem exists_fixed_of_involutive {X : Type*} [Finite X]
    (f : X → X) (hf : Function.Involutive f) (hodd : ¬ 2 ∣ Nat.card X) :
    ∃ x, f x = x := by
  let e : Equiv.Perm X := hf.toPerm f
  have he : e^2 = 1 := by
    ext x
    exact hf x
  have hA : IsPGroup 2 (Subgroup.zpowers e) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one he
  obtain ⟨x, hx⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card X hodd
  exact ⟨x, hx ⟨e, Subgroup.mem_zpowers e⟩⟩

private theorem exists_twisted_conjugate_mem_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (c : MulAut G) (hc : c^2 = 1)
    (hS : (S : Subgroup G).map c.toMonoidHom = S)
    (g : G) (hg : g * c g = 1) :
    ∃ h : G, h⁻¹ * g * c h ∈ S := by
  let Q := G ⧸ (S : Subgroup G)
  let f : Q → Q := Quotient.map' (fun x => g * c x) (by
    intro x y hxy
    apply QuotientGroup.leftRel_apply.mpr
    have hh : c (x⁻¹ * y) ∈ (S : Subgroup G) := by
      rw [← hS]
      exact ⟨x⁻¹ * y, QuotientGroup.leftRel_apply.mp hxy, rfl⟩
    simpa only [map_mul, map_inv, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hh)
  have hf : Function.Involutive f := by
    intro x
    induction x using Quotient.inductionOn with
    | h x =>
      change (Quotient.mk'' (g * c (g * c x)) : Q) = Quotient.mk'' x
      congr 1
      have hc' : c (c x) = x := DFunLike.congr_fun hc x
      rw [map_mul, hc', ← mul_assoc, hg, one_mul]
  obtain ⟨x, hx⟩ := exists_fixed_of_involutive f hf S.not_dvd_index
  obtain ⟨h, rfl⟩ := Quotient.mk''_surjective x
  refine ⟨h, ?_⟩
  have hh := QuotientGroup.leftRel_apply.mp (Quotient.exact' hx.symm)
  change h⁻¹ * g * c h ∈ (S : Subgroup G)
  rw [mul_assoc]
  exact hh

private theorem cocycle_solutions_of_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (c : MulAut G) (hc : c^2 = 1)
    (hS : (S : Subgroup G).map c.toMonoidHom = S)
    (hlocal : ∀ u : G, u ∈ S → u * c u = 1 →
      ∃ v : G, v ∈ S ∧ u = v⁻¹ * c v)
    (g : G) (hg : g * c g = 1) : ∃ h : G, g = h⁻¹ * c h := by
  obtain ⟨h, hh⟩ := exists_twisted_conjugate_mem_sylow S c hc hS g hg
  have hu : (h⁻¹ * g * c h) * c (h⁻¹ * g * c h) = 1 := by
    have hc' : c (c h) = h := DFunLike.congr_fun hc h
    simp only [map_mul, map_inv, hc']
    calc
      _ = h⁻¹ * (g * c g) * h := by group
      _ = 1 := by rw [hg]; group
  obtain ⟨v, _, hv⟩ := hlocal _ hh hu
  refine ⟨v * h⁻¹, ?_⟩
  have hhg : g = h * (v⁻¹ * c v) * (c h)⁻¹ := by
    rw [← hv]
    group
  rw [hhg]
  simp only [map_mul, map_inv]
  group

/-- Solving the norm-one equation in the genuine positive subgroup suffices
for every norm-one element of the carrier. -/
theorem canonical_cocycle_solutions_of_unipotent
    (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m) (hnm : n = 2*m)
    (hlocal : ∀ u : BinaryCarrier n hn, u ∈ unipotent (binaryParameters n hn) →
      u * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) u = 1 →
      ∃ v : BinaryCarrier n hn, v ∈ unipotent (binaryParameters n hn) ∧
        u = v⁻¹ * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) v)
    (g : BinaryCarrier n hn)
    (hg : g * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) g = 1) :
    ∃ h : BinaryCarrier n hn,
      g = h⁻¹ * coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) h := by
  have hs : coefficientFrobenius n hn (3*m) ^ 2 = 1 :=
    coefficientFrobenius_order_two n hn m hm hnm ▸
      pow_orderOf_eq_one (coefficientFrobenius n hn (3*m))
  have hc : coefficientAction (binaryParameters n hn) (coefficientFrobenius n hn (3*m)) ^ 2 = 1 := by
    rw [← map_pow, hs, map_one]
  exact cocycle_solutions_of_sylow (unipotentSylow (binaryParameters n hn) rfl) _ hc
    (coefficientAction_unipotent _ _) hlocal g hg

end Triality.Standard.EvenField.NormalForm
