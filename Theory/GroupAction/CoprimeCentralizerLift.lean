module

public import Theory.GroupAction.SubgroupQuotientFullAction

/-!
# Lifting a fixed coset into a centralizer product

If `D` normalizes `P` and its abelian normal subgroup `V`, and `|D|` is
coprime to `|V|`, an element of `P` fixed modulo `V` belongs to `C_P(D)V`.
The proof uses the coprime fixed-point quotient theorem on the literal
subgroup quotient, then translates the lift back into the ambient group.

This is the fixed-point lifting argument in coprime action; one application
is Aschbacher–Smith, 15.3.61(2), printed p.1150.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A fixed coset has a representative centralizing the actual actor. -/
theorem mem_centralizer_sup_of_coprime_fixed_coset
    (P V D : Subgroup G) (hVP : V ≤ P)
    [(V.subgroupOf P).Normal] [IsMulCommutative (V.subgroupOf P)]
    (hDP : D ≤ normalizer (P : Set G))
    (hDV : D ≤ normalizer (V : Set G))
    (hcop : Nat.Coprime (Nat.card D) (Nat.card V))
    (x : G) (hx : x ∈ P)
    (hfixed : ∀ d ∈ D, MulAut.conj d x / x ∈ V) :
    x ∈ (P ⊓ centralizer (D : Set G)) ⊔ V := by
  let _ : MulDistribMulAction D P := conjMulDistribMulActionOfLeNormalizer D P hDP
  have hInv : IsInvariant D P (V.subgroupOf P) := by
    constructor
    intro d p
    exact mem_normalizer_iff.mp (hDV d.property) p
  have hcop' : Nat.Coprime (Nat.card D) (Nat.card (V.subgroupOf P)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVP).toEquiv]
    exact hcop
  let _ := quotientMulDistribMulAction (V.subgroupOf P) hInv
  let xP : P := ⟨x, hx⟩
  have hq : QuotientGroup.mk' (V.subgroupOf P) xP ∈
      FixedPoints.subgroup D (P ⧸ V.subgroupOf P) := by
    intro d
    change QuotientGroup.mk' (V.subgroupOf P) (d • xP) =
      QuotientGroup.mk' (V.subgroupOf P) xP
    exact QuotientGroup.eq_iff_div_mem.mpr (hfixed d d.property)
  rw [fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative _ hInv hcop'] at hq
  obtain ⟨b, hb, hbx⟩ := hq
  have hbC : (b : G) ∈ centralizer (D : Set G) := by
    apply mem_centralizer_iff.mpr
    intro d hd
    have he := congrArg (fun p : P => (p : G)) (hb (⟨d, hd⟩ : D))
    change d * (b : G) * d⁻¹ = b at he
    have he' := congrArg (fun t : G => t * d) he
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he'
  have hbV' : b / xP ∈ V.subgroupOf P := QuotientGroup.eq_iff_div_mem.mp hbx
  have hbV : (b : G) / x ∈ V := hbV'
  have hc : ((b : G) / x)⁻¹ * b ∈ (P ⊓ centralizer (D : Set G)) ⊔ V :=
    mul_mem ((show V ≤ (P ⊓ centralizer (D : Set G)) ⊔ V from le_sup_right)
      (V.inv_mem hbV))
      ((show P ⊓ centralizer (D : Set G) ≤ (P ⊓ centralizer (D : Set G)) ⊔ V
        from le_sup_left) ⟨b.property, hbC⟩)
  simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel,
    mul_one] using hc

end Subgroup
