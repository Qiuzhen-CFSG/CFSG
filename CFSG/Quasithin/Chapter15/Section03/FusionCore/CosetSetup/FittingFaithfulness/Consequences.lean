module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness.Kernel

/-!
# Noncentrality and the commutator equality in 15.3.49(2)

Faithfulness after removal of the fixed core gives U not contained in
Z(Q), once the outside-family and Sylow assumptions exclude H = O₂(H).
Normal generation then makes [Z_S,Q] nontrivial, and its order-two bound
from 15.3.48(2) makes it equal to Z. No commutativity of U is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), p.1142.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

/-- The fixed core lies in the actual center of Q once U ≤ Q. -/
theorem fixedCore_le_center {G : Type*} [Group G] (A H : Subgroup G)
    (hUQ : localSpan A H ≤ H.pCoreIn 2) :
    fixedCore A H ≤ (center (H.pCoreIn 2)).map (H.pCoreIn 2).subtype := by
  intro c hc
  refine ⟨⟨c, hUQ hc.1⟩, mem_center_iff.mpr ?_, rfl⟩
  intro q
  exact Subtype.ext (hc.2 q q.property)

/-- The source outside-family and Sylow hypotheses exclude H = O₂(H). -/
theorem twoCore_ne_top_of_outside
    {G : Type*} [Group G] (M H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) (hTM : (T : Subgroup G) ≤ M)
    (hout : ¬ H ≤ M) : pCore 2 H ≠ ⊤ := by
  intro he
  have him : H.pCoreIn 2 = H := by rw [Subgroup.pCoreIn, he, ← MonoidHom.range_eq_map, range_subtype]
  have hp : IsPGroup 2 H := him ▸ isPGroup_pCoreIn 2 H
  exact hout ((T.is_maximal' hp hTH).le.trans hTM)

/-- Specialization to C_U(Q), in precisely the representative form used by
`DualAction.extraspecial_spans_of_omega_bound`. -/
theorem span_faithful_on_representatives
    {H : Type*} [Group H] [Finite H]
    (A Z : Subgroup H) [Z.Normal]
    (hUQ : localSpan A ⊤ ≤ pCore 2 H)
    (hsmall : centralizerModulo ⊤ (localSpan A ⊤) Z ≤ pCore 2 H)
    (hfit : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤
        centralizer ((localSpan A ⊤ ⊓ centralizer (pCore 2 H : Set H)) : Set H)) :
    ∀ h : H, (∀ u : localSpan A ⊤,
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤))
        ⟨h * u * h⁻¹, (inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h⟩ =
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤)) u) →
      h ∈ pCore 2 H := by
  let C := localSpan A ⊤ ⊓ centralizer (pCore 2 H : Set H)
  have hp : IsPGroup 2 C := pCore_isPGroup.to_le (inf_le_left.trans hUQ)
  intro h hh
  apply faithful_on_representatives (localSpan A ⊤) C Z hp hsmall hfit h
  intro u
  have hh' := QuotientGroup.eq_iff_div_mem.mp (hh u)
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact ⟨(localSpan A ⊤).div_mem
    ((inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h) u.property,
    hh'⟩

/-- Nontriviality of H/O₂(H) and faithfulness exclude U ≤ C_H(Q). -/
theorem span_not_le_centralizer_of_faithful
    {H : Type*} [Group H] (A : Subgroup H)
    (hne : pCore 2 H ≠ ⊤)
    (hfaith : ∀ h : H, (∀ u : localSpan A ⊤,
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤))
        ⟨h * u * h⁻¹, (inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h⟩ =
      QuotientGroup.mk' ((centralizer (pCore 2 H : Set H)).subgroupOf (localSpan A ⊤)) u) →
      h ∈ pCore 2 H) :
    ¬ localSpan A ⊤ ≤ centralizer (pCore 2 H : Set H) := by
  intro hc
  apply hne
  apply top_unique
  intro h _
  apply hfaith h
  intro u
  apply QuotientGroup.eq_iff_div_mem.mpr
  exact (centralizer (pCore 2 H : Set H)).div_mem
    (hc ((inferInstance : (localSpan A ⊤).Normal).conj_mem u u.property h)) (hc u.property)

/-- The one-dimensional commutator bound in 15.3.48(2) is an equality
once the faithful action excludes centralization of the span. -/
theorem generator_commutator_eq
    {H : Type*} [Group H] [Finite H]
    (A Z : Subgroup H) (hZ : Nat.card Z = 2)
    (hbound : ⁅A, pCore 2 H⁆ ≤ Z)
    (hnon : ¬ localSpan A ⊤ ≤ centralizer (pCore 2 H : Set H)) :
    ⁅A, pCore 2 H⁆ = Z := by
  have hne : ⁅A, pCore 2 H⁆ ≠ ⊥ := by
    intro hb
    apply hnon
    apply conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hb)
    rw [(centralizer (pCore 2 H : Set H)).normalizer_eq_top]
  apply eq_of_le_of_card_ge hbound
  rw [hZ]
  have := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  omega

/-- The faithful quotient action gives both source consequences, without
an abelianness assumption on the conjugate span. -/
theorem span_noncentral_and_commutator_eq
    {H : Type*} [Group H] [Finite H]
    (A Z : Subgroup H) [Z.Normal]
    (hUQ : localSpan A ⊤ ≤ pCore 2 H)
    (hsmall : centralizerModulo ⊤ (localSpan A ⊤) Z ≤ pCore 2 H)
    (hfit : (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤
        centralizer ((localSpan A ⊤ ⊓ centralizer (pCore 2 H : Set H)) : Set H))
    (hne : pCore 2 H ≠ ⊤) (hZ : Nat.card Z = 2)
    (hbound : ⁅A, pCore 2 H⁆ ≤ Z) :
    ¬ localSpan A ⊤ ≤ (center (pCore 2 H)).map (pCore 2 H).subtype ∧
      ⁅A, pCore 2 H⁆ = Z := by
  have hn := span_not_le_centralizer_of_faithful A hne
    (span_faithful_on_representatives A Z hUQ hsmall hfit)
  refine ⟨?_, generator_commutator_eq A Z hZ hbound hn⟩
  intro hc
  apply hn
  intro u hu
  obtain ⟨c, hc, rfl⟩ := hc hu
  intro q hq
  exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨q, hq⟩)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

end
