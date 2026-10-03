module
public import Theory.GroupAction.Quotient

/-!
# Exact fixed subgroups across a coprime abelian kernel

For an equivariant surjection of groups, suppose the kernel is abelian,
its order is coprime to that of the finite actor, and the kernel has no
nonidentity fixed point. Restriction of the original homomorphism is then
an isomorphism between the exact fixed subgroups of source and target.

The kernel is invariant by equivariance. The existing coprime fixed-point
quotient theorem lifts any fixed point in the target to a fixed source
point, giving surjectivity of the restriction. The fixed-kernel hypothesis
gives injectivity. Both action instances and the homomorphism are retained
literally, with a pointwise formula for the resulting isomorphism.

This is the fixed-subgroup lifting step for D* acting on Q_a/Z_a in
Stellmacher (9.1), Journal of Algebra190 (1997), p.48. No campaign imports
or elementary-group hypotheses are needed in the general theorem.
-/
namespace MonoidHom
public theorem fixed_subgroup_equiv_of_coprime_abelian_kernel
    {D Q W : Type*} [Group D] [Finite D] [Group Q] [Finite Q] [Group W]
    [MulDistribMulAction D Q] [MulDistribMulAction D W]
    (f : Q →* W) (hf : Function.Surjective f)
    [IsMulCommutative f.ker]
    (hcop : Nat.Coprime (Nat.card D) (Nat.card f.ker))
    (hequiv : ∀ d : D, ∀ q : Q, f (d • q) = d • f q)
    (hfree : FixedPoints.subgroup D Q ⊓ f.ker = ⊥) :
    ∃ iso : FixedPoints.subgroup D Q ≃* FixedPoints.subgroup D W,
      ∀ q, (iso q : W) = f (q : Q) := by
  let CQ := FixedPoints.subgroup D Q
  let CW := FixedPoints.subgroup D W
  let r : CQ →* CW := (f.comp CQ.subtype).codRestrict CW (by
    intro q d
    change d • f (q : Q) = f (q : Q)
    rw [← hequiv, q.property d])
  have hrinj : Function.Injective r := by
    apply (ker_eq_bot_iff _).mp
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hfree]
    refine ⟨q.property, ?_⟩
    exact congrArg Subtype.val (mem_ker.mp hq)
  have hInv : IsInvariant D Q f.ker := by
    constructor
    intro d q
    simp only [mem_ker, hequiv]
    constructor
    · intro hq
      rw [hq, smul_one]
    · intro hq
      have hh := congrArg (fun w => d⁻¹ • w) hq
      simpa only [inv_smul_smul, smul_one] using hh
  let _ := quotientMulDistribMulAction (A := D) f.ker hInv
  have hfixmap := fixedPoints_subgroup_quotient_eq_map_of_isMulCommutative f.ker hInv hcop
  have hrsurj : Function.Surjective r := by
    intro w
    obtain ⟨q,hq⟩ := hf w
    have hqfix : (QuotientGroup.mk' f.ker) q ∈ FixedPoints.subgroup D (Q ⧸ f.ker) := by
      intro d
      change (QuotientGroup.mk' f.ker) (d • q) = (QuotientGroup.mk' f.ker) q
      apply QuotientGroup.eq_iff_div_mem.mpr
      change f ((d • q) / q) = 1
      rw [map_div, hequiv, hq, w.property d]
      exact div_self' (w : W)
    rw [hfixmap] at hqfix
    obtain ⟨fixed, hfixed, heq⟩ := hqfix
    have hfq : f fixed = f q := by
      have hmem := QuotientGroup.eq_iff_div_mem.mp heq
      change f (fixed / q) = 1 at hmem
      rw [map_div, div_eq_one] at hmem
      exact hmem
    exact ⟨⟨fixed,hfixed⟩, Subtype.ext (hfq.trans hq)⟩
  exact ⟨MulEquiv.ofBijective r ⟨hrinj, hrsurj⟩, fun _ => rfl⟩
end MonoidHom
