module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.Source

/-!
# The conditional quotient-module bound 15.3.64

For H in the genuine family H(T,M), 15.3.50 makes <V^H> abelian. Its
subgroup U_H=<Z_S^H> is therefore elementary abelian. We construct the
faithful action of H/O_2(H) on the literal additive group U_H/Z using
15.3.48(3). Lemma 15.3.49(3) removes the side condition on 15.3.48(1),
so every clause of F.9.1 is available. The proved 15.3.62(2) establishes
F.9.8(f), and restriction of 15.3.47 establishes F.9.8(g)(ii). The exact
F.9.16(3) offender witness then bounds the global quadratic ratio by two.
`bound_for_independent_action` transports this result to any separately
constructed action through `LocalQuotientAction.representation_eq`.

This is a conditional implication for the Section 15.3 assembly owner.
The remaining earlier inputs, all explicit in `lemma_15_3_64`, are:

* The elementary group V, its actual natural orthogonal action, the
  nonidentity singular z generating Z, M_c=C_G(Z), and M_c in H(T,M)
  (15.3.2--8 and the paragraph preceding 15.3.48).
* The fusion and totally singular intersection conclusions of 15.3.46
  used by the existing proof of 15.3.62(2), and the exact 15.3.47 dichotomy.
* `Earlier48Input` for each H, including all source F.9.1 clauses and the
  literal centralizer-kernel equality; O_2(Y)=C_Y(V) from 15.3.49(3).
* Abelianness of <V^H> for the outside family, from 15.3.50.
* `F9163Input` from the F.9 foundations/geometry owners.

The parent retains discharge of these witnesses and final source-theorem
assembly. No result about the generation parameter n(H) is used here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
printed pp.1151--1152, with F.9.1, F.9.8 and F.9.16(3).
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G]

/-- Extract the numerical bound from the actual F.9.16(3) subgroup witness.
The nontrivial image has positive rank, so division preserves its inequality. -/
theorem quadraticRatio_le_two_of_F9163 [Finite G]
    {T : Sylow 2 G} {Y V ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
    (h98 : SourceF98 T Y V ZS Z H) (hF : F9163Input T Y V ZS Z H)
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z) :
    quadraticRatio a.representation ≤ 2 := by
  obtain ⟨B, _, hB, hq, hr⟩ := hF inferInstance h98 a
  apply (iInf_le_of_le (B.map (QuotientGroup.mk' (pCore 2 H)))
    (iInf_le_of_le ⟨hB, hq⟩ le_rfl)).trans
  rw [actionRatio, ENNReal.div_le_iff (by exact_mod_cast (ne_of_gt hB.rank_pos)) (by simp)]
  exact_mod_cast hr

/-- Construct the faithful action and verify F.9.8 after 15.3.49(3)
discharges the side condition on 15.3.48. -/
theorem exists_bounded_action [Finite G]
    {T : Sylow 2 G} {Y V ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    (h48 : Earlier48Input T Y V ZS Z H)
    (h49 : Y.pCoreIn 2 = Y ⊓ centralizer (V : Set G))
    [IsMulCommutative (conjugateSpanBy V H)]
    (h62 : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (h47 : ∀ x ∈ centralizer (ZS : Set G),
      ⁅V, zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize V x)
    (hF : F9163Input T Y V ZS Z H) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H),
      letI := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy ZS H) Z,
        quadraticRatio a.representation ≤ 2 := by
  have h48out := h48 (Or.inl h49)
  have h91 := h48out.toSourceF91
  let hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H) := small_span_elementary h91.zs_le
  let a := localQuotientAction H (conjugateSpanBy ZS H) Z
    (h91.z_lt.le.trans (le_conjugateSpanBy ZS H))
    (conjugateSpanBy_le_self (h91.zs_le.trans (h91.v_le_sylow.trans
      (le_sup_right.trans h91.a_contains))))
    (le_normalizer_conjugateSpanBy ZS H)
    (h91.a_centralizes.trans (centralizer_le_normalizer (Z : Set G))) h48out.centralizer_kernel
  exact ⟨hU, a, quadraticRatio_le_two_of_F9163
    (sourceF98_of_intersection_and_47 h91 h62 h47) hF a⟩

/-- The bound also holds for an independently constructed quotient action,
using the representative-level uniqueness theorem from Basic. -/
theorem bound_for_independent_action {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z)
    (h : ∃ hU : IsElementaryAbelian 2 U, letI := hU
      ∃ b : LocalQuotientAction H U Z, quadraticRatio b.representation ≤ 2) :
    quadraticRatio a.representation ≤ 2 := by
  obtain ⟨_, b, hb⟩ := h
  rw [a.representation_eq b]
  exact hb

/-- The conditional implication 15.3.64 for H∈H(T,M). The intersection
commutator theorem is obtained from the proved 15.3.62(2), not assumed here.
All outstanding earlier results and the F.9.16 implication are explicit. -/
theorem lemma_15_3_64 [Finite G]
    {T : Sylow 2 G} {Y V M Mc ZS Z H : Subgroup G} [IsElementaryAbelian 2 V]
    {z : G} (d : OrthogonalFourBinary.NaturalAction V M)
    (hzV : z ∈ V) (hz : z ≠ 1) (hzs : d.singular ⟨z, hzV⟩)
    (hZ : Z = zpowers z) (hMc : Mc = centralizer (Z : Set G))
    (hMcFamily : Mc ∈ sylowOutsideFamily T M)
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ m ∈ M, MulAut.conj m z = MulAut.conj a z)
    (hsingular : ∀ g : G, g ∉ M →
      ∀ x : ↥(V ⊓ V.map (MulAut.conj g).toMonoidHom),
        d.singular ⟨x, x.property.1⟩)
    (h47 : ∀ x ∈ centralizer (ZS : Set G),
      ⁅V, zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize V x)
    (h48 : ∀ J ∈ sylowOutsideFamily T M, Earlier48Input T Y V ZS Z J)
    (h49 : Y.pCoreIn 2 = Y ⊓ centralizer (V : Set G))
    (h50 : ∀ J ∈ sylowOutsideFamily T M, IsMulCommutative (conjugateSpanBy V J))
    (hF : ∀ J ∈ sylowOutsideFamily T M, F9163Input T Y V ZS Z J)
    (hH : H ∈ sylowOutsideFamily T M) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy ZS H),
      letI := hU
      ∃ a : LocalQuotientAction H (conjugateSpanBy ZS H) Z,
        quadraticRatio a.representation ≤ 2 := by
  let := h50 Mc hMcFamily
  let := h50 H hH
  apply exists_bounded_action (h48 H hH) h49
  · exact lemma_15_3_62_2 d hzV hz hzs (by simpa only [hZ] using hMc) hfusion hsingular
  · exact h47
  · exact hF H hH

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
