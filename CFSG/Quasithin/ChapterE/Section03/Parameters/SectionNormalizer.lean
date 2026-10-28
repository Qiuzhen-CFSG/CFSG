module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.BinaryConjugationSection.Descent
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.Representation.BinaryConjugationSection.ActionKernel

/-!
# The full local automizer on a literal binary section

Extend the marked component action through the original subgroup quotient.
Every element of M normalizing the section numerator is retained. If its
kernel on the quotient is exactly the centralizer of the numerator, this
full induced automizer embeds in the linear normalizer of the component
image. Both the coordinate map and every conjugation formula are preserved.
Source application: Aschbacher–Smith, 10.2.12, printed pp.754–755.
-/

@[expose] public noncomputable section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE
variable {G J V : Type*} [Group G] [Group J]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The original local normalizer maps onto its full induced automizer. -/
def localNormalizerAction (W M : Subgroup G) :
    (M ⊓ normalizer (W : Set G) : Subgroup G) →* inducedAutomizer W M where
  toFun n := ⟨W.normalizerMonoidHom.rangeRestrict ⟨n,n.property.2⟩,
    ⟨⟨n,n.property.2⟩,n.property.1,rfl⟩⟩
  map_one' := by apply Subtype.ext; exact map_one W.normalizerMonoidHom.rangeRestrict
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul W.normalizerMonoidHom.rangeRestrict ⟨a,a.property.2⟩ ⟨b,b.property.2⟩

theorem localNormalizerAction_surjective (W M : Subgroup G) :
    Function.Surjective (localNormalizerAction W M) := by
  rintro ⟨a,n,hn,rfl⟩
  exact ⟨⟨n,hn,n.property⟩,rfl⟩

theorem localNormalizerAction_eq_one_iff (W M : Subgroup G)
    (n : (M ⊓ normalizer (W : Set G) : Subgroup G)) :
    localNormalizerAction W M n = 1 ↔ (n : G) ∈ centralizer (W : Set G) := by
  constructor
  · intro hn w hw
    have hh := congrArg (fun a : inducedAutomizer W M => ((a.val.val) ⟨w,hw⟩ : G)) hn
    change (n : G)*w*(n : G)⁻¹=w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hn
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    change (n : G)*(w : G)*(n : G)⁻¹=w
    rw [←hn w w.property,mul_inv_cancel_right]

/-- Extend the actual section action to its full local automizer and embed it
in the full normalizer of the marked component action. -/
theorem exists_local_section_normalizer
    (H W Z M : Subgroup G) [IsElementaryAbelian 2 W]
    (σ : Representation (ZMod 2) J V) (q : H →* J) (hq : Function.Surjective q)
    (c : Representation.BinaryConjugationSection H W Z (σ.comp q))
    (hHM : H ≤ M)
    (hNH : M ⊓ normalizer (W : Set G) ≤ normalizer (H : Set G))
    (hNZ : M ⊓ normalizer (W : Set G) ≤ normalizer (Z : Set G))
    (hker : commutatorPreimage (M ⊓ normalizer (W : Set G)) W Z ≤
      centralizer (W : Set G)) :
    ∃ (τ : Representation (ZMod 2) (inducedAutomizer W M) V)
      (f : inducedAutomizer W M →* linearNormalizer σ),
      Function.Injective f ∧
      (∀ a v, normalizerRepresentation σ (f a) v = τ a v) ∧
      (∀ (n : (M ⊓ normalizer (W : Set G) : Subgroup G)) (w : W),
        τ (localNormalizerAction W M n) (c.coordinates w).toAdd =
          (c.coordinates ⟨(n : G)*w*(n : G)⁻¹,
            (mem_normalizer_iff.mp n.property.2 w).mp w.property⟩).toAdd) := by
  let N := M ⊓ normalizer (W : Set G)
  let A := inducedAutomizer W M
  let α := localNormalizerAction W M
  have hα : Function.Surjective α := localNormalizerAction_surjective W M
  have hWN : W ≤ N := le_inf (c.section_le.trans hHM) W.le_normalizer
  have hHN : H ≤ N := le_inf hHM c.normalized
  let : (Z.subgroupOf W).Normal := c.kernel_normal
  obtain ⟨τ₀,d,hd⟩ := Representation.BinaryConjugationSection.exists_descended_actor
    N W Z hWN c.kernel_le inf_le_right hNZ α hα (by
      intro n hn w hw
      have hh := (localNormalizerAction_eq_one_iff W M n).mp hn
      rw [(commutatorElement_eq_one_iff_mul_comm).mpr (hh w hw).symm]
      exact Z.one_mem)
  let E : Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective (c.quotientEquiv.toMonoidHom.toAdditiveLeft.toZModLinearMap 2)
      c.quotientEquiv.bijective
  have hE (w : W) : E (d.coordinates w).toAdd = (c.coordinates w).toAdd := by
    rw [hd]
    exact congrArg Multiplicative.toAdd (c.quotientEquiv_mk w)
  let τ : Representation (ZMod 2) A V := E.conjRingEquiv.toMonoidHom.comp τ₀
  have hact (n : N) (w : W) : τ (α n) (c.coordinates w).toAdd =
      (c.coordinates ⟨(n : G)*w*(n : G)⁻¹,
        (mem_normalizer_iff.mp n.property.2 w).mp w.property⟩).toAdd := by
    rw [←hE w]
    change E (τ₀ (α n) (E.symm (E (d.coordinates w).toAdd))) = _
    rw [E.symm_apply_apply]
    exact (congrArg E (d.equivariant n w).symm).trans (hE _)
  have htinj : Function.Injective τ := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    obtain ⟨n,rfl⟩ := hα a
    apply (localNormalizerAction_eq_one_iff W M n).mpr
    apply hker
    have hn : n ∈ (τ₀.comp α).ker := by
      apply LinearMap.ext
      intro v
      apply E.injective
      have hh := congrArg (fun f : Module.End (ZMod 2) V => f (E v)) ha
      change E (τ₀ (α n) (E.symm (E v))) = E v at hh
      change E (τ₀ (α n) v) = E v
      simpa only [E.symm_apply_apply] using hh
    have hm := mem_map_of_mem N.subtype hn
    rw [d.action_kernel_map hNZ] at hm
    exact hm
  let ρ : Representation (ZMod 2) N V := τ.comp α
  let K := H.subgroupOf N
  let : K.Normal := (normal_subgroupOf_iff_le_normalizer hHN).mpr hNH
  have hmark (h : H) : ρ (inclusion hHN h) = σ (q h) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    exact (hact (inclusion hHN h) w).trans (c.equivariant h w)
  have him : actionImage (ρ.comp K.subtype) = actionImage σ := by
    ext u
    constructor
    · rintro ⟨k,rfl⟩
      refine ⟨q ⟨k,k.property⟩,?_⟩
      apply Units.ext
      exact (hmark ⟨k,k.property⟩).symm
    · rintro ⟨j,rfl⟩
      obtain ⟨h,rfl⟩ := hq j
      refine ⟨⟨inclusion hHN h,h.property⟩,?_⟩
      apply Units.ext
      exact hmark h
  have hnorm (a : A) : τ.asGroupHom a ∈ linearNormalizer σ := by
    obtain ⟨n,rfl⟩ := hα a
    have hh := actionImage_le_linearNormalizer ρ K (show ρ.asGroupHom n ∈ actionImage ρ from ⟨n,rfl⟩)
    change ρ.asGroupHom n ∈ normalizer (actionImage (ρ.comp K.subtype) : Set _) at hh
    rw [him] at hh
    change τ.asGroupHom (α n) ∈ normalizer (actionImage σ : Set _)
    convert hh using 1
    exact Units.ext rfl
  let f : A →* linearNormalizer σ := τ.asGroupHom.codRestrict _ hnorm
  refine ⟨τ,f,?_,fun _ _ => rfl,hact⟩
  intro a b hab
  exact htinj (congrArg (fun u : linearNormalizer σ => u.val.val) hab)
end CFSG.Quasithin.ChapterE
