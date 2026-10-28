module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.Basic
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CentralizerModulo

/-!
# The literal quotient action for 15.3.64

An abelian conjugate span of an elementary abelian group is elementary
abelian: conjugation preserves squares, and closure induction preserves
exponent two inside an abelian group. Thus abelianness of V_H = <V^H>
from 15.3.50 makes U_H = <Z_S^H> elementary abelian when Z_S <= V.

We construct the conjugation action on U/(Z.subgroupOf U), identify its
linear kernel with the inverse image of C_(H/Z)(U/Z), and descend along
H -> H/O_2(H) using the actual centralizer equality of 15.3.48(3).
Both containment and the action on every representative are retained in
`LocalQuotientAction`. No representation or faithfulness is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.48 on printed pp.1141--1142 and 15.3.64 on p.1151.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
variable {G : Type*} [Group G]

/-- An abelian span of conjugates of V inherits its exponent two. -/
theorem span_elementary (V H : Subgroup G) [IsElementaryAbelian 2 V]
    [hcomm : IsMulCommutative (conjugateSpanBy V H)] :
    IsElementaryAbelian 2 (conjugateSpanBy V H) := by
  let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ z ∈ V, h * z * h⁻¹ = x}) := hcomm
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨h, _, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

/-- In particular, the actual smaller span U_H is elementary abelian. -/
theorem small_span_elementary {V A H : Subgroup G} [IsElementaryAbelian 2 V]
    [IsMulCommutative (conjugateSpanBy V H)] (hAV : A ≤ V) :
    IsElementaryAbelian 2 (conjugateSpanBy A H) := by
  let := span_elementary V H
  exact IsElementaryAbelian.of_le (conjugateSpanBy_mono hAV le_rfl)

private noncomputable def sectionAut (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G)) :
    H →* MulAut (U ⧸ Z.subgroupOf U) :=
  Classical.choose (exists_quotient_conjugation_action H U Z hHU hHZ inferInstance)

private theorem sectionAut_apply (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    (h : H) (u : U) :
    sectionAut H U Z hHU hHZ h (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(h : G) * u * (h : G)⁻¹, (hHU h.property u).mp u.property⟩ :=
  Classical.choose_spec (exists_quotient_conjugation_action H U Z hHU hHZ inferInstance) h u

/-- The binary linear action induced by conjugation on the literal section U/Z. -/
noncomputable def sectionRepresentation (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G)) :
    Representation (ZMod 2) H (Additive (U ⧸ Z.subgroupOf U)) where
  toFun h := (sectionAut H U Z hHU hHZ h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (sectionAut H U Z hHU hHZ 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' h k := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul (sectionAut H U Z hHU hHZ (h * k) u.toMul) = _
    rw [map_mul]
    rfl

/-- The section action on every quotient representative. -/
theorem sectionRepresentation_apply (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    (h : H) (u : U) :
    sectionRepresentation H U Z hHU hHZ h
        (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) =
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
        ⟨(h : G) * u * (h : G)⁻¹, (hHU h.property u).mp u.property⟩) :=
  congrArg Additive.ofMul (sectionAut_apply H U Z hHU hHZ h u)

/-- Kernel membership means precisely that all action commutators lie in Z. -/
theorem sectionRepresentation_ker_iff (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G)) (h : H) :
    h ∈ (sectionRepresentation H U Z hHU hHZ).ker ↔
      ∀ u ∈ U, ⁅(h : G), u⁆ ∈ Z := by
  constructor
  · intro hh u hu
    have he := congrArg (fun f => f (Additive.ofMul
      (QuotientGroup.mk' (Z.subgroupOf U) ⟨u, hu⟩))) hh
    rw [sectionRepresentation_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he)
    change (h : G) * u * (h : G)⁻¹ / u ∈ Z at hm
    simpa only [div_eq_mul_inv, commutatorElement_def] using hm
  · intro hh
    apply LinearMap.ext
    intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf U) w.toMul
    have he : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u) = w :=
      congrArg Additive.ofMul hu
    rw [← he, sectionRepresentation_apply]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (h : G) * (u : G) * (h : G)⁻¹ / (u : G) ∈ Z
    simpa only [div_eq_mul_inv, commutatorElement_def] using hh u u.property

/-- The linear kernel is the relative centralizer of U/Z inside H/Z, pulled
back to H. Normality of Z is required only inside H. -/
theorem sectionRepresentation_ker_eq_centralizerModulo
    (H U Z : Subgroup G) [IsElementaryAbelian 2 U] (hUH : U ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G)) :
    letI := normal_subgroupOf_of_le_normalizer hHZ
    (sectionRepresentation H U Z hHU hHZ).ker =
      centralizerModulo (⊤ : Subgroup H) (U.subgroupOf H) (Z.subgroupOf H) := by
  let := normal_subgroupOf_of_le_normalizer hHZ
  ext h
  rw [sectionRepresentation_ker_iff, mem_centralizerModulo_iff]
  simp only [mem_top, true_and]
  constructor
  · intro hh u hu
    change ⁅(u : G), (h : G)⁆ ∈ Z
    simpa only [commutatorElement_inv] using Z.inv_mem (hh u hu)
  · intro hh u hu
    have hc := hh ⟨u, hUH hu⟩ hu
    change ⁅u, (h : G)⁆ ∈ Z at hc
    simpa only [commutatorElement_inv] using Z.inv_mem hc

/-- Descend the section action to H/O₂(H). Its exact centralizer kernel proves
faithfulness and gives the shared representative-level interface. -/
noncomputable def localQuotientAction (H U Z : Subgroup G) [IsElementaryAbelian 2 U]
    (hZU : Z ≤ U) (hUH : U ≤ H)
    (hHU : H ≤ normalizer (U : Set G)) (hHZ : H ≤ normalizer (Z : Set G))
    (hker : letI := normal_subgroupOf_of_le_normalizer hHZ
      centralizerModulo (⊤ : Subgroup H) (U.subgroupOf H) (Z.subgroupOf H) = pCore 2 H) :
    LocalQuotientAction H U Z := by
  let ρ := sectionRepresentation H U Z hHU hHZ
  have hk : ρ.ker = pCore 2 H :=
    (sectionRepresentation_ker_eq_centralizerModulo H U Z hUH hHU hHZ).trans hker
  let σ := QuotientGroup.lift (pCore 2 H) ρ hk.ge
  refine ⟨hZU, hUH, hHU, σ, ?_, ?_⟩
  · intro h u
    exact sectionRepresentation_apply H U Z hHU hHZ h u
  · apply σ.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro q hq
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) q
    have hh : h ∈ ρ.ker := hq
    exact (QuotientGroup.eq_one_iff h).mpr (hk ▸ hh)


end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.ModuleBound
