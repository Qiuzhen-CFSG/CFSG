module
public import CFSG.Quasithin.ChapterF.Section09.CriticalEndpoints
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.ElementaryAbelian.Quotient
public import Theory.Representation.BinaryQuinticDisplacement
public import Theory.SpecificGroups.QuinticInvolutionCommutator
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Quintic critical modules escape the opposite core

The original F.9 kernel equality constructs a faithful action of H/O₂(H)
on the literal quotient U_H/V₁. If the same critical conjugate U_H^g
lay in O₂(H), then [U_H,U_H^g]≤V₁. Conjugating back gives displacement
at most one for each element of U_H^(g⁻¹) on U_H/V₁. An elementary
actor in D₁₀ or Sz(2) either acts trivially or moves at least two dimensions,
by its order-five commutator. Triviality contradicts criticality. Thus the
opposite module escapes the core and the existing endpoint reversal applies.

Source: Aschbacher--Smith F.9.13 and F.9.17, printed pp.322--324;
the quintic local quotient is the source case of14.2.21, printed p.988.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

/-- The original U_H/V1 carries the faithful H/O2(H) action with its literal quotient map. -/
theorem faithful_UH_section [IsElementaryAbelian 2 D.UH] :
    let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
    ∃ (σ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H)
        (Additive (D.UH ⧸ D.V₁.subgroupOf D.UH)))
      (c : Representation.BinaryConjugationSection D.H D.UH D.V₁
        (σ.comp (QuotientGroup.mk' (pCore 2 D.H)))),
      Function.Injective σ ∧
      ∀ u : D.UH, (c.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u) := by
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  apply Representation.BinaryConjugationSection.exists_faithful_quotient_actor
    D.H D.UH D.V₁ h.UH_le_H (h.point_lt.le.trans (le_conjugateSpanBy _ _))
    (le_normalizer_conjugateSpanBy _ _) (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    (QuotientGroup.mk' (pCore 2 D.H)) (QuotientGroup.mk'_surjective _)
  intro a
  rw [←MonoidHom.mem_ker,QuotientGroup.ker_mk']
  have ha : a ∈ pCore 2 D.H ↔ (a : G) ∈ h.kernel D.UH := by
    rw [h.kernel_UH_eq_QH]
    change a ∈ pCore 2 D.H ↔ (a : G) ∈ (pCore 2 D.H).map D.H.subtype
    exact (mem_map_iff_mem (f := D.H.subtype) D.H.subtype_injective).symm
  rw [ha,h.mem_kernel_iff h.UH_le_H,and_iff_right a.property]
  constructor
  · intro hh u hu
    simpa only [commutatorElement_inv] using D.V₁.inv_mem (hh u hu)
  · intro hh u hu
    simpa only [commutatorElement_inv] using D.V₁.inv_mem (hh u hu)

/-- For a quintic local quotient the elementary critical module escapes
 the opposite two-core. The same endpoint is retained. -/
theorem CriticalEndpoint.not_le_core_of_quintic
    [IsElementaryAbelian 2 D.UH]
    (hm : Nonempty ((D.H ⧸ pCore 2 D.H) ≃* DihedralGroup 5) ∨
      Nonempty ((D.H ⧸ pCore 2 D.H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hUV : D.UH = D.VH) (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) :
    ¬ i.conjugate D.UH ≤ D.QH := by
  intro hc
  let g := i.representative
  let A := D.UH.conjBy g⁻¹
  let B := D.V₁.conjBy g⁻¹
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (i.reverse_le hb)
    change (D.VH.conjBy g⁻¹) ≤ (D.H.conjBy g).conjBy g⁻¹ at hh
    rw [conjBy_inv] at hh
    simpa only [A,hUV] using hh
  have hAB : ⁅A,D.UH⁆ ≤ B := by
    have hh := (commutator_mono le_rfl hc).trans h.commutator_UH_QH_le_point
    have hh' := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hh
    rw [map_commutator] at hh'
    change ⁅A,(D.UH.conjBy g).conjBy g⁻¹⁆ ≤ B at hh'
    rwa [conjBy_inv] at hh'
  have hB : Nat.card B = 2 :=
    (card_map_of_injective (MulAut.conj g⁻¹).injective).trans h.point_card
  let : (D.V₁.subgroupOf D.UH).Normal := normal_of_isMulCommutative _
  obtain ⟨σ,c,hσ,_⟩ := h.faithful_UH_section
  have hw (t : D.H ⧸ pCore 2 D.H) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
      ∃ x, orderOf (t*x*t⁻¹*x⁻¹) = 5 :=
    Theory.SpecificGroups.exists_order_five_commutator_of_quintic_model hm t
      (orderOf_eq_prime ht2 ht)
  have hker := c.elementary_le_actor_kernel_of_commutator_card_two σ hσ
    (QuotientGroup.mk' (pCore 2 D.H)) hw A B hAH hAB hB.le
  rw [QuotientGroup.ker_mk'] at hker
  have hAQ : A ≤ D.QH := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hker ha,rfl⟩
  have hcomm : ⁅D.UH,A⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl hAQ).trans h.commutator_UH_QH_le_point
  have hcommg := map_mono (f := (MulAut.conj g).toMonoidHom) hcomm
  rw [map_commutator] at hcommg
  change ⁅i.conjugate D.UH,(D.UH.conjBy g⁻¹).conjBy g⁆ ≤ i.conjugate D.V₁ at hcommg
  rw [conjBy_inv'] at hcommg
  apply i.noncentral
  exact (commutator_mono le_rfl (show D.V ≤ D.UH by
    rw [hUV]; exact le_conjugateSpanBy _ _)).trans hcommg
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
