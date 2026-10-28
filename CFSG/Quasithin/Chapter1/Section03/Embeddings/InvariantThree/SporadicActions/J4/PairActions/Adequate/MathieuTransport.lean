module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Adequate.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.MathieuAbsorption.Quotient

/-!
# Transporting max1 actors to the actual Mathieu quotient

The certified max1 kernel is its characteristic two-core. Thus each local
automorphism induces an automorphism of the actual M₂₄ quotient. Its
compatibility with the projection transfers preservation of a Sylow image
and the specified action on the odd complement to the pair automizer.

The complement equivalence uses only that it is a three-group, so it
retains both the elementary-nine and extraspecial order-27 source cases.
No reducibility or trio-placement theorem is assumed or asserted here.
This module supplies action transport for the separate max1 calculation.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511/PDF p.528.
The actual kernel and quotient comparison are certified in
`Janko4.Model.LocalStructure.Mathieu`.
-/

public section

open Subgroup
set_option backward.isDefEq.respectTransparency true

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
open MathieuAbsorption

attribute [local irreducible] Janko4.modelGroup Janko4.Cardinality.max1Subgroup

/-- Every three-subgroup injects across the actual binary max1 kernel. -/
noncomputable def oddComplementEquiv [Finite Janko4.Model]
    {R : Subgroup Janko4.Model} (hR : R ≤ Local) (h3 : IsPGroup 3 R) :
    R ≃* image R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.Coprime 3 (Nat.card projection.ker) := by
    rw [projection_ker, Janko4.Cardinality.localKernel_card]
    decide
  have hi : Function.Injective (projection.comp (R.subgroupOf Local).subtype) :=
    injective_comp_subtype_of_coprime_ker projection hc _ h3.comap_subtype
  exact (subgroupOfEquivOfLe hR).symm.trans
    (MulEquiv.ofBijective (projection.subgroupMap (R.subgroupOf Local))
      ⟨fun _ _ he => hi (congrArg Subtype.val he), projection.subgroupMap_surjective _⟩)

/-- The complement comparison is the actual restriction of the projection. -/
theorem oddComplementEquiv_coe [Finite Janko4.Model]
    {R : Subgroup Janko4.Model} (hR : R ≤ Local) (h3 : IsPGroup 3 R) (r : R) :
    (oddComplementEquiv hR h3 r : Sporadic.Mathieu.M24) = projection (inclusion hR r) := by rfl

/-- Local automorphisms descend because the certified kernel is characteristic. -/
theorem exists_quotientActor (c : MulAut Local) :
    ∃ d : MulAut Sporadic.Mathieu.M24, ∀ x : Local, projection (c x) = d (projection x) := by
  let N := Janko4.Cardinality.localKernel Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hN : N = pCore 2 Local := Janko4.LocalStructure.localKernel_eq_twoCore _ _
  let _ : N.Characteristic := by rw [hN]; infer_instance
  let e := Janko4.LocalStructure.localQuotientEquivM24
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  refine ⟨(e.symm.trans (quotientAut N c)).trans e, fun x => ?_⟩
  change e (QuotientGroup.mk' N (c x)) =
    e (quotientAut N c (e.symm (e (QuotientGroup.mk' N x))))
  rw [e.symm_apply_apply, quotientAut_apply_mk]

/-- The descended automorphism preserves the Sylow image and realizes the
transported action on the full odd complement. -/
theorem pairAutomizer_quotient_transport [Finite Janko4.Model]
    (S R : Subgroup Janko4.Model) (hR : R ≤ Local) (h3 : IsPGroup 3 R)
    (a : MulAut R) (c : MulAut Local)
    (hcS : ∀ x : Local, (c x : Janko4.Model) ∈ S ↔ (x : Janko4.Model) ∈ S)
    (hcR : ∀ r : R, inclusion hR (a r) = c (inclusion hR r)) :
    MulAut.congr (oddComplementEquiv hR h3) a ∈ pairAutomizer (image S) (image R) := by
  obtain ⟨d, hd⟩ := exists_quotientActor c
  refine ⟨d, ?_, ?_⟩
  · intro y
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨c.symm x, ?_, ?_⟩
      · exact (hcS (c.symm x)).mp (by
          rw [c.apply_symm_apply]
          exact hx)
      · apply d.injective
        rw [← hd, c.apply_symm_apply, he]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c x, (hcS x).mpr hx, hd x⟩
  · intro y
    obtain ⟨r, rfl⟩ := (oddComplementEquiv hR h3).surjective y
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [oddComplementEquiv_coe, oddComplementEquiv_coe, hcR, hd]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.Adequate
