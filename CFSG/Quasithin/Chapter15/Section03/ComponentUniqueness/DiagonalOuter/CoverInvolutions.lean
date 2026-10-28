module

public import Theory.GroupTheory.KleinFourKernelInvolutionFusion
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupAction.NormalizerFixedCentralizer
public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.JointCentralizer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FusionReduction

/-!
# Lifting the central-cover model facts into the diagonal-outer argument

Field-coset conjugacy lifts from the quotient through the Klein four kernel:
a nontrivial field action on that kernel removes the remaining difference
between two lifts. The conjugating element is retained in the actual `L`.
Perfectness also makes descent on automorphisms faithful, so the actual
centralizer action image has order dividing the quotient pointwise fixer.
Finally, the fixed-subgroup equivalence transports an intrinsic residual
model to the ambient joint-centralizer construction.

Source: Aschbacher--Smith 15.3.38, printed pp.1136--1137, combined manuscript
of 1 March 2004. These are conditional lifting results. The four-cover
involution classes, its three fixed-subgroup residual models, the projective
pointwise-fixer bound, and the odd core and Sylow three-subgroup of `C_I(τf)`
remain model proof obligations. The Sylow subgroup in that larger centralizer
is not the E₉ joint residual. Neither incompatible printed order assertion
is assumed here.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
open Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Quotient fusion lifts with its conjugator in the original cover subgroup. -/
theorem field_coset_conjugate_of_quotient
    (I L : Subgroup G) (hLI : L ≤ I) (q : I →* Q)
    [IsKleinFour q.ker] (hker : q.ker ≤ L.subgroupOf I)
    (f : I) (hf : f ^ 2 = 1)
    (hcenterAction : ∃ c : q.ker, f * (c : I) * f⁻¹ ≠ (c : I))
    (hquotient : ∀ y : Q, y ^ 2 = 1 → y * (q f)⁻¹ ∈ (L.subgroupOf I).map q →
      ∃ b ∈ (L.subgroupOf I).map q, b * q f * b⁻¹ = y)
    (x : G) (hx : orderOf x = 2) (hxL : x * (f : G)⁻¹ ∈ L) :
    ∃ n : L, (MulAut.conj (n : G)) (f : G) = x := by
  have hxI : x ∈ I := by
    have hh := I.mul_mem (hLI hxL) f.property
    simpa only [inv_mul_cancel_right] using hh
  let xI : I := ⟨x, hxI⟩
  have hx2 : xI ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [← hx]
    exact pow_orderOf_eq_one x
  obtain ⟨n, hn⟩ := involution_coset_conjugate_of_kleinFour_kernel q
    (L.subgroupOf I) hker f hf hcenterAction hquotient xI hx2 hxL
  refine ⟨⟨((n : I) : G), n.property⟩, ?_⟩
  exact congrArg Subtype.val hn

/-- The field-coset input in `field_fusion_of_transfer_geometry`. -/
theorem field_coset_fusion_of_quotient
    (I L : Subgroup G) (hLI : L ≤ I) (q : I →* Q)
    [IsKleinFour q.ker] (hker : q.ker ≤ L.subgroupOf I)
    (f : I) (hf : f ^ 2 = 1)
    (hcenterAction : ∃ c : q.ker, f * (c : I) * f⁻¹ ≠ (c : I))
    (hquotient : ∀ y : Q, y ^ 2 = 1 → y * (q f)⁻¹ ∈ (L.subgroupOf I).map q →
      ∃ b ∈ (L.subgroupOf I).map q, b * q f * b⁻¹ = y)
    (x : G) (hx : orderOf x = 2) (hxL : x * (f : G)⁻¹ ∈ L) :
    IsConj x (f : G) := by
  obtain ⟨n, hn⟩ := field_coset_conjugate_of_quotient I L hLI q hker f hf
    hcenterAction hquotient x hx hxL
  exact (isConj_iff.mpr ⟨(n : G), hn⟩).symm

/-- A projective pointwise-fixer bound supplies the exact TI action-image bound. -/
theorem centralizer_image_not_four_of_quotient
    (L F : Subgroup G) (c : Matrix.PSL3Four.FourCover L)
    (hsmall : ¬ 4 ∣ Nat.card (fixingSubgroup (MulAut Matrix.PSL3Four.PSL)
      ((F.subgroupOf L).map c.toMonoidHom : Set Matrix.PSL3Four.PSL))) :
    ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom) := by
  intro hfour
  exact hsmall (hfour.trans (c.toCover.card_centralizerImage_dvd_quotientFixer L F
    c.ker_eq_center))

/-- An intrinsic graph-field fixed-residual model feeds the ambient fusion construction. -/
theorem jointResidual_model_of_fixed_fusion [Finite G]
    (V L : Subgroup G) (w : normalizer (L : Set G))
    (hLC : L ≤ centralizer (V : Set G))
    (hindex : L.relIndex (centralizer (V : Set G)) = 2)
    {f : G} (hfusion : IsConj (w : G) f)
    (e : pResidual 2 (L.normalizerMonoidHom w).fixedSubgroup ≃* ElementaryNine) :
    ∃ g : G, (MulAut.conj g) (w : G) = f ∧
      Nonempty (jointResidual (V.map (MulAut.conj g).toMonoidHom) f ≃* ElementaryNine) := by
  exact jointResidual_model_of_fusion V L hLC hindex hfusion
    ((normalizerResidualEquivCentralizer L w 2).symm.trans e)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
