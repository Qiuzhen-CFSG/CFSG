module
public import Theory.GroupAction.Invariant
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import Theory.GroupAction.SubgroupConjugation

/-!
# Fixed representatives for prime-group actors

For an equivariant homomorphism, a prime-group actor fixes a representative
of every fixed image point whenever the kernel order is prime to that
prime. Each fiber has the kernel's cardinality, so orbit counting supplies
a fixed point. Neither the source group nor the kernel must be abelian.
The subgroup application covers the literal quotient by its centralizer.

This generalizes the binary fiber argument in `TwoGroupFixedImage`.
Source: Kurzweil–Stellmacher, §11.1.3, pp.306–307; the order-seven
application is Aschbacher–Smith 5.2.2, printed p.648.
-/

public section
namespace MonoidHom
private def kernelEquivFiber {G H : Type*} [Group G] [Group H]
    (f : G →* H) (x : G) : f.ker ≃ {z : G // f z = f x} where
  toFun n := ⟨x * n, by simp [f.mem_ker.mp n.property]⟩
  invFun z := ⟨x⁻¹ * z, by simp [mem_ker, z.property]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Fixed image points lift through a kernel of order prime to the actor prime. -/
theorem map_fixedPoints_eq_of_prime_coprime_kernel
    {A G H : Type*} [Group A] [Group G] [Group H] [Finite G]
    [MulDistribMulAction A G] [MulDistribMulAction A H]
    {p : ℕ} [Fact p.Prime]
    (hA : IsPGroup p A) (f : G →* H) (hker : ¬ p ∣ Nat.card f.ker)
    (hequiv : ∀ a : A, ∀ g : G, f (a • g) = a • f g) :
    (FixedPoints.subgroup A G).map f = f.range ⊓ FixedPoints.subgroup A H := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, fun a => (hequiv a x).symm.trans (congrArg f (hx a))⟩
  · rintro y ⟨⟨x, rfl⟩, hfix⟩
    let Fiber := {z : G // f z = f x}
    have hnot : ¬ p ∣ Nat.card Fiber := by
      rwa [Nat.card_congr (kernelEquivFiber f x).symm]
    let : MulAction A Fiber :=
      { smul := fun a z => ⟨a • z.val, by rw [hequiv, z.property, hfix a]⟩
        one_smul := fun z => Subtype.ext (one_smul A z.val)
        mul_smul := fun a b z => Subtype.ext (mul_smul a b z.val) }
    obtain ⟨z, hz⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card Fiber hnot
    exact ⟨z.val, fun a => congrArg Subtype.val (hz a), z.property⟩
end MonoidHom

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A prime-group actor trivial on the quotient has a centralizer covering it. -/
theorem centralizer_quotient_surjective_of_prime_fixed
    {p : ℕ} [Fact p.Prime] (L E : Subgroup G) (N : Subgroup L) [N.Normal]
    (hE : IsPGroup p E) (hEN : E ≤ normalizer (L : Set G))
    (hcop : ¬ p ∣ Nat.card N)
    (hfixed : ∀ e ∈ E, ∀ l ∈ L, e * l * e⁻¹ * l⁻¹ ∈ N.map L.subtype) :
    Function.Surjective ((QuotientGroup.mk' N).comp
      (inclusion (show L ⊓ centralizer (E : Set G) ≤ L from inf_le_left))) := by
  let : MulDistribMulAction E L := conjMulDistribMulActionOfLeNormalizer E L hEN
  let : MulDistribMulAction E (L ⧸ N) := MulDistribMulAction.compHom _ (1 : E →* MulAut (L ⧸ N))
  let q := QuotientGroup.mk' N
  have heq (e : E) (l : L) : q (e • l) = q l := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨v,hv,he⟩ := hfixed e e.property l l.property
    have hh : (e • l) / l = v := by
      apply Subtype.ext
      exact (show (e : G) * l * (e : G)⁻¹ / l = (v : G) by
        simpa only [div_eq_mul_inv, Subgroup.subtype_apply] using he.symm)
    exact hh ▸ hv
  have hm := q.map_fixedPoints_eq_of_prime_coprime_kernel hE
    (by simpa only [q,QuotientGroup.ker_mk'] using hcop)
    (fun e l => heq e l)
  intro y
  have hy : y ∈ (FixedPoints.subgroup E L).map q := by
    rw [hm]
    exact ⟨⟨(QuotientGroup.mk'_surjective N y).choose,
      (QuotientGroup.mk'_surjective N y).choose_spec⟩,fun _ => rfl⟩
  obtain ⟨l,hl,rfl⟩ := hy
  refine ⟨⟨l, l.property, ?_⟩,rfl⟩
  intro e he
  have hh := congrArg Subtype.val (hl (⟨e,he⟩ : E))
  change e * (l : G) * e⁻¹ = l at hh
  exact mul_inv_eq_iff_eq_mul.mp hh
end Subgroup
