module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CentralizerModulo
public import Theory.Representation.BinaryOffender.Ratio

/-!
# Literal quotients in the terminal A₅ argument

We construct conjugation on U_H/V₁, where U_H is the H-conjugate span of
V₃. Its linear kernel is identified both as the ambient commutator preimage
and as the inverse image of the centralizer in H/V₁. The F.9.2(3) identity
then gives a faithful representation of the actual H/O₂(H), with uniqueness
from its action on representatives. The natural map U_H/V₁ → H/V₁ is
constructed and proved injective; all normality is relative to these groups.

The representative-level proof follows the existing generic quotient-action
argument in Chapter15/.../ModuleBound/QuotientAction, using its lower-level
conjugation construction directly and keeping the §13.6 imports narrow.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.2(3),
Notation 13.5.8, and the last paragraph of §13.6, printed pp.318,918,935.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
open Section08
variable {G : Type*} [Group G]

/-- The literal additive carrier of U_H/V₁. -/
abbrev Space (H V₃ V₁ : Subgroup G) := Additive (Source.Utilde H V₃ V₁)

/-- The seed containment places its full H-conjugate span inside H. -/
theorem UH_le {H V₃ : Subgroup G} (h : V₃ ≤ H) : Source.UH H V₃ ≤ H :=
  conjugateSpanBy_le_self h

section Action
variable (H V₃ V₁ : Subgroup G) [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hz : H ≤ normalizer (V₁ : Set G))

noncomputable def quotientAction : H →* MulAut (Source.Utilde H V₃ V₁) :=
  (exists_quotient_conjugation_action H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hz inferInstance).choose

private theorem quotientAction_apply (h : H) (u : Source.UH H V₃) :
    quotientAction H V₃ V₁ hz h (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) =
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        ⟨h.val * u.val * h.val⁻¹,
          le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
            u.val u.property⟩ :=
  (exists_quotient_conjugation_action H (Source.UH H V₃) V₁
    (le_normalizer_conjugateSpanBy V₃ H) hz inferInstance).choose_spec h u

/-- Conjugation by H on the actual section, before dividing out its kernel. -/
noncomputable def representation : Representation (ZMod 2) H (Space H V₃ V₁) where
  toFun h := (quotientAction H V₃ V₁ hz h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext u
    change Additive.ofMul (quotientAction H V₃ V₁ hz 1 u.toMul) = u
    rw [map_one]
    rfl
  map_mul' h k := by
    ext u
    change Additive.ofMul (quotientAction H V₃ V₁ hz (h * k) u.toMul) = _
    rw [map_mul]
    rfl

/-- Conjugation is retained on every representative of U_H/V₁. -/
theorem representation_apply (h : H) (u : Source.UH H V₃) :
    representation H V₃ V₁ hz h
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
    Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      ⟨h.val * u.val * h.val⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
          u.val u.property⟩) :=
  congrArg Additive.ofMul (quotientAction_apply H V₃ V₁ hz h u)

/-- The linear kernel consists exactly of elements centralizing U_H modulo V₁. -/
theorem mem_ker_iff (h : H) :
    h ∈ (representation H V₃ V₁ hz).ker ↔
      ∀ u ∈ Source.UH H V₃, ⁅(h : G), u⁆ ∈ V₁ := by
  constructor
  · intro hh u hu
    have he := congrArg (fun f => f (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) ⟨u, hu⟩))) hh
    rw [representation_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he)
    simpa only [mem_subgroupOf, coe_div, coe_mul, coe_inv, div_eq_mul_inv, commutatorElement_def] using hm
  · intro hh
    apply LinearMap.ext
    intro w
    obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) w.toMul
    have he : Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) = w :=
      congrArg Additive.ofMul hu
    rw [← he, representation_apply]
    apply congrArg Additive.ofMul
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa only [mem_subgroupOf, coe_div, coe_mul, coe_inv, div_eq_mul_inv, commutatorElement_def] using hh u u.property

/-- The ambient image of the kernel matches the source's commutator-preimage convention. -/
theorem map_ker : (representation H V₃ V₁ hz).ker.map H.subtype =
    commutatorPreimage H (Source.UH H V₃) V₁ := by
  apply le_antisymm
  · apply le_commutatorPreimage (map_subtype_le _)
    apply commutator_le.mpr
    rintro x ⟨h, hh, rfl⟩ u hu
    exact (mem_ker_iff H V₃ V₁ hz h).mp hh u hu
  · intro x hx
    refine ⟨⟨x, commutatorPreimage_le _ _ _ hx⟩, ?_, rfl⟩
    apply (mem_ker_iff H V₃ V₁ hz _).mpr
    exact commutator_le.mp (commutator_commutatorPreimage_le _ _ _ hz) x hx

/-- The same kernel in the literal H/V₁ centralizer convention of F.9.2(3). -/
theorem ker_eq_centralizerModulo (hV₃H : V₃ ≤ H) :
    let := normal_subgroupOf_of_le_normalizer hz
    (representation H V₃ V₁ hz).ker =
      centralizerModulo (⊤ : Subgroup H) ((Source.UH H V₃).subgroupOf H)
        (V₁.subgroupOf H) := by
  let := normal_subgroupOf_of_le_normalizer hz
  ext h
  rw [mem_ker_iff, mem_centralizerModulo_iff]
  simp only [mem_top, true_and]
  constructor
  · intro hh u hu
    change ⁅(u : G), (h : G)⁆ ∈ V₁
    simpa only [commutatorElement_inv] using V₁.inv_mem (hh u hu)
  · intro hh u hu
    have hc := hh ⟨u, conjugateSpanBy_le_self hV₃H hu⟩ hu
    change ⁅u, (h : G)⁆ ∈ V₁ at hc
    simpa only [commutatorElement_inv] using V₁.inv_mem hc

/-- F.9.2(3) identifies the entire linear kernel with the actual two-core. -/
theorem ker_eq_pCore
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    (representation H V₃ V₁ hz).ker = pCore 2 H :=
  map_injective H.subtype_injective ((map_ker H V₃ V₁ hz).trans hk)

/-- The source H* representation, constructed by dividing out the computed kernel. -/
noncomputable def starRepresentation
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁) :=
  QuotientGroup.lift (pCore 2 H) (representation H V₃ V₁ hz)
    (ker_eq_pCore H V₃ V₁ hz hk).ge

theorem starRepresentation_mk
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) (h : H) :
    starRepresentation H V₃ V₁ hz hk (QuotientGroup.mk' (pCore 2 H) h) =
      representation H V₃ V₁ hz h := QuotientGroup.lift_mk _ _ h

/-- Faithfulness is a consequence of the source centralizer identity. -/
theorem starRepresentation_injective
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H) :
    Function.Injective (starRepresentation H V₃ V₁ hz hk) :=
  (QuotientGroup.injective_lift_iff _ _ _).mpr (ker_eq_pCore H V₃ V₁ hz hk).symm

/-- Representative compatibility specifies the source action uniquely. -/
theorem starRepresentation_unique
    (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Space H V₃ V₁))
    (hρ : ∀ (h : H) (u : Source.UH H V₃),
      ρ (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
      representation H V₃ V₁ hz h
        (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))) :
    ρ = starRepresentation H V₃ V₁ hz hk := by
  apply MonoidHom.ext
  intro q
  apply LinearMap.ext
  intro w
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) q
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) w.toMul
  have he : Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) = w :=
    congrArg Additive.ofMul hu
  rw [← he, starRepresentation_mk]
  exact hρ h u

/-- The other source quotient, H̃ = H/V₁. -/
abbrev Htilde := H ⧸ V₁.subgroupOf H

/-- The inclusion U_H ≤ H induces the literal inclusion of central sections. -/
def tildeMap (hV₃H : V₃ ≤ H) :
    letI := normal_subgroupOf_of_le_normalizer hz
    Source.Utilde H V₃ V₁ →* Htilde H V₁ := by
  let := normal_subgroupOf_of_le_normalizer hz
  exact QuotientGroup.map (V₁.subgroupOf (Source.UH H V₃)) (V₁.subgroupOf H)
    (inclusion (UH_le hV₃H)) (fun _ hu => hu)

/-- No extra elements are killed when U_H/V₁ is placed in H/V₁. -/
theorem tildeMap_injective (hV₃H : V₃ ≤ H) :
    letI := normal_subgroupOf_of_le_normalizer hz
    Function.Injective (tildeMap H V₃ V₁ hz hV₃H) := by
  let := normal_subgroupOf_of_le_normalizer hz
  apply (tildeMap H V₃ V₁ hz hV₃H).ker_eq_bot_iff.mp
  ext q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) q
  change QuotientGroup.mk' (V₁.subgroupOf H)
    (inclusion (UH_le hV₃H) u) = 1 ↔
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u = 1
  constructor
  · intro hu
    have hm := (QuotientGroup.eq_one_iff (N := V₁.subgroupOf H)
      (inclusion (UH_le hV₃H) u)).mp hu
    exact (QuotientGroup.eq_one_iff u).mpr hm
  · intro hu
    exact (QuotientGroup.eq_one_iff _).mpr ((QuotientGroup.eq_one_iff u).mp hu)

/-- Both quotient maps use the same source representative. -/
theorem tildeMap_mk (hV₃H : V₃ ≤ H) (u : Source.UH H V₃) :
    letI := normal_subgroupOf_of_le_normalizer hz
    tildeMap H V₃ V₁ hz hV₃H
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) =
        QuotientGroup.mk' (V₁.subgroupOf H)
          (inclusion (UH_le hV₃H) u) := rfl
end Action
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Ratio
end
