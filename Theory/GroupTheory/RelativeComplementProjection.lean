module

public import Mathlib.GroupTheory.Complement

/-!
# Projection onto a complement inside a subgroup

If R and C generate H, have trivial intersection, and R is normal in H,
then H/R is canonically isomorphic to C. The quotient map followed by this
isomorphism is a surjective retraction with kernel R, interpreted as a subgroup
of H. Only relative normality is needed; H can be a subgroup of a larger group.

The proof uses unique factorization in the internal semidirect product and
the quotient equivalence for complementary subgroups. This is the elementary
projection step in Levi decompositions, as in GLS3 §2.6, Theorem 2.6.5(g).
-/

public section

noncomputable section
namespace Subgroup
variable {G : Type*} [Group G] {H R C : Subgroup G}

/-- The factors are complementary inside their actual overgroup. -/
theorem relative_isComplement (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] :
    (C.subgroupOf H).IsComplement' (R.subgroupOf H) := by
  refine ⟨Subgroup.mul_injective_of_disjoint ?_, ?_⟩
  · apply Subgroup.disjoint_def.mpr
    intro x hxC hxR
    exact Subtype.ext (Subgroup.disjoint_def.mp hd hxR hxC)
  · intro g
    have htop : C.subgroupOf H ⊔ R.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hC hR, sup_comm, hgen, Subgroup.subgroupOf_self]
    have hg : g ∈ C.subgroupOf H ⊔ R.subgroupOf H := htop.symm ▸ Subgroup.mem_top g
    obtain ⟨c, hc, r, hr, hcr⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    exact ⟨(⟨c, hc⟩, ⟨r, hr⟩), hcr⟩

/-- The quotient by a relatively normal factor is its complement. -/
@[expose] def relativeQuotientEquiv (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] :
    H ⧸ R.subgroupOf H ≃* C :=
  (relative_isComplement hR hC hgen hd).QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe hC)

/-- The Levi projection, retaining the actual complement as its codomain. -/
@[expose] def relativeComplementProjection (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] : H →* C :=
  (relativeQuotientEquiv hR hC hgen hd).toMonoidHom.comp
    (QuotientGroup.mk' (R.subgroupOf H))

theorem relativeComplementProjection_surjective (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] :
    Function.Surjective (relativeComplementProjection hR hC hgen hd) :=
  (relativeQuotientEquiv hR hC hgen hd).surjective.comp (QuotientGroup.mk'_surjective _)

theorem relativeComplementProjection_ker (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] :
    (relativeComplementProjection hR hC hgen hd).ker = R.subgroupOf H := by
  rw [relativeComplementProjection, MonoidHom.ker_comp_of_injective _ _
    (relativeQuotientEquiv hR hC hgen hd).injective, QuotientGroup.ker_mk']

theorem relativeComplementProjection_inclusion (hR : R ≤ H) (hC : C ≤ H)
    (hgen : R ⊔ C = H) (hd : Disjoint R C) [(R.subgroupOf H).Normal] (c : C) :
    relativeComplementProjection hR hC hgen hd (Subgroup.inclusion hC c) = c := by
  let hcomp := relative_isComplement hR hC hgen hd
  let c' : C.subgroupOf H := ⟨Subgroup.inclusion hC c, c.property⟩
  have he : hcomp.QuotientMulEquiv (QuotientGroup.mk' (R.subgroupOf H) c'.val) = c' :=
    hcomp.QuotientMulEquiv.apply_symm_apply c'
  exact congrArg (Subgroup.subgroupOfEquivOfLe hC) he
end Subgroup
