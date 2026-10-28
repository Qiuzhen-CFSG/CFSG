module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The literal simple image of an internal elementary core

If L/O₂(L) is simple and L moves its elementary core W nontrivially, the
kernel of the original conjugation action is exactly W. Its image inside
any given normalizer action is the same specified simple quotient.
-/

namespace Representation.BinaryInternalFixedSpaceCodimension
open Subgroup BinaryOffender
open scoped IsMulCommutative
variable {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]

private theorem ker_eq_of_simple_quotient {X Y : Type*} [Group X] [Group Y]
    (Q : Subgroup X) [Q.Normal] (e : (X⧸Q)≃*S)
    (f : X→*Y) (hQ : Q≤f.ker) (hne : f.ker≠⊤) : f.ker=Q := by
  let : IsSimpleGroup (X⧸Q) := e.isSimpleGroup
  let π := QuotientGroup.mk' Q
  let : (f.ker.map π).Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective Q)
  rcases (inferInstance : (f.ker.map π).Normal).eq_bot_or_eq_top with hb | ht
  · exact le_antisymm (by simpa only [π,QuotientGroup.ker_mk'] using (map_eq_bot_iff f.ker).mp hb) hQ
  · exfalso
    apply hne
    have hh := congrArg (Subgroup.comap π) ht
    simpa only [comap_map_eq,π,QuotientGroup.ker_mk',comap_top,sup_of_le_left hQ] using hh

/-- The actual L-image in the given ambient normalizer action is the original
simple quotient. No assertion about the full normalizer's action kernel is used. -/
public theorem simple_core_action_image
    (W I L : Subgroup G) [IsElementaryAbelian 2 W]
    (hI : I≤normalizer (W : Set G)) (hLI : L≤I)
    (hcore : L.pCoreIn 2=W) (hcomm : ⁅W,L⁆=W) (hW : W≠⊥)
    (e : (L⧸pCore 2 L)≃*S) :
    let ρ := representation W I hI
    ((actionHom ρ).comp (inclusion hLI)).ker=pCore 2 L ∧
      Nonempty ((actionSubgroup ρ (L.subgroupOf I))≃*S) := by
  let ρ := representation W I hI
  let f : L→*actionImage ρ := (actionHom ρ).comp (inclusion hLI)
  have hQ : pCore 2 L≤f.ker := by
    intro x hx
    have hxW : (x:G)∈W := hcore ▸ mem_map_of_mem L.subtype hx
    apply (actionHom_eq_one_iff ρ (inclusion hLI x)).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x:G)*(w.toMul:G)*(x:G)⁻¹=(w.toMul:G)
    have he : (x:G)*(w.toMul:G)=(w.toMul:G)*(x:G) :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := W)).comm ⟨x,hxW⟩ w.toMul)
    rw [he,mul_inv_cancel_right]
  have hne : f.ker≠⊤ := by
    intro htop
    have hLC : L≤centralizer (W : Set G) := by
      intro l hl w hw
      have hf : f ⟨l,hl⟩=1 := by
        change (⟨l,hl⟩:L)∈f.ker
        rw [htop]
        exact mem_top _
      have hh := (actionHom_eq_one_iff ρ (inclusion hLI ⟨l,hl⟩)).mp hf
        (Additive.ofMul (⟨w,hw⟩:W))
      have he := congrArg (fun v : Additive W => (v.toMul:G)) hh
      change l*w*l⁻¹=w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    apply hW
    rw [←hcomm,commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hLC
  have hk := ker_eq_of_simple_quotient (pCore 2 L) e f hQ hne
  have hr : f.range=actionSubgroup ρ (L.subgroupOf I) := by
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion hLI l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  exact ⟨hk,⟨((MulEquiv.subgroupCongr hr).symm.trans
    (QuotientGroup.quotientKerEquivRange f).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans e)⟩⟩

end Representation.BinaryInternalFixedSpaceCodimension
