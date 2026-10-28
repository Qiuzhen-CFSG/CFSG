module
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeSource
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.BinaryOffender.ConjugationImage

/-!
# The original M22 point commutator

The full point-residual map with two-group kernel sends its two-core onto
that of the native inner hexad stabilizer. Whole-code equivariance then
identifies the literal commutator V_z=[V,O₂(L_z)] with the native rank-five
code subspace, giving |V_z|=32 without a separate core-image premise.

Source: Aschbacher--Smith, 8.2.11 and H.16.3, refs/quasithin.pdf.
The canonical hexad marking and its full kernel are retained as explicit
inputs for the original point-row assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE
variable {G : Type*} [Group G]
set_option backward.isDefEq.respectTransparency false

private theorem kernel_commutator :
    subspaceCommutator m22OuterCodeRepresentation ⊤ ChiefFlag.Kernel =
      codeCommutator ChiefFlag.Kernel := by
  unfold subspaceCommutator codeCommutator Coinvariants.ker
  congr 1
  ext v
  constructor
  · rintro ⟨g,hg,w,_,rfl⟩
    exact ⟨(⟨g,hg⟩,w),rfl⟩
  · rintro ⟨⟨g,w⟩,rfl⟩
    exact ⟨g,g.property,w,Submodule.mem_top,rfl⟩

/-- The actual core action identifies the original commutator with the
native five-space, retaining the original whole-code coordinates. -/
theorem m22_point_commutator_coordinates
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (q : X →* MathieuCode.m22PairStabilizer)
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) =
        m22OuterCodeRepresentation (q x) (e v))
    (hq : q.range = ChiefFlag.Kernel) :
    ∀ v : Additive V, (v.toMul : G) ∈ ⁅V,X⁆ ↔ e v ∈ codeCommutator ChiefFlag.Kernel := by
  let f := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hXV)
  let ρ := (automizerRepresentation V).comp f
  have hact (x : X) (v : V) :
      ρ x (Additive.ofMul v) = Additive.ofMul
        (⟨(x : G)*(v : G)*(x : G)⁻¹,le_normalizer_iff.mp hXV x x.property v v.property⟩ : V) := rfl
  have hcomm := commutator_image_eq ρ V V X hXV le_rfl (MonoidHom.id X)
    (MonoidHom.id V) (fun x v => hact x v) ⊤ (by ext v; simp [binarySubgroup])
  have hC : (⁅V,X⁆).subgroupOf V = binarySubgroup (subspaceCommutator ρ ⊤ (⊤ : Subgroup X)) := by
    simpa only [map_id,(MonoidHom.id X).range_eq_top_of_surjective (fun x => ⟨x,rfl⟩)] using hcomm
  have he' (x : X) (w : M22Code) :
      ρ x (e.symm w) = e.symm (m22OuterCodeRepresentation (q x) w) := by
    apply e.injective
    exact (he x (e.symm w)).trans (by rw [e.apply_symm_apply,e.apply_symm_apply])
  have hm := subspaceCommutator_map_embedding ρ m22OuterCodeRepresentation q
    e.symm.toLinearMap he' (⊤ : Subgroup X) (⊤ : Submodule (ZMod 2) M22Code)
  have hM : subspaceCommutator ρ ⊤ (⊤ : Subgroup X) =
      (codeCommutator ChiefFlag.Kernel).map e.symm.toLinearMap := by
    simpa only [Submodule.map_top,LinearEquiv.range,←MonoidHom.range_eq_map,hq,
      kernel_commutator] using hm
  intro v
  change v.toMul ∈ (⁅V,X⁆).subgroupOf V ↔ _
  rw [hC,hM]
  change v ∈ (codeCommutator ChiefFlag.Kernel).map e.symm.toLinearMap ↔ _
  constructor
  · rintro ⟨w,hw,rfl⟩
    simpa using hw
  · intro hv
    exact ⟨e v,hv,e.symm_apply_apply v⟩

/-- The native five-space gives order 32 for the literal original commutator. -/
theorem m22_point_commutator_card
    (V X : Subgroup G) [IsElementaryAbelian 2 V]
    (hXV : X ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code) (q : X →* MathieuCode.m22PairStabilizer)
    (he : ∀ x v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hXV x)) v) =
        m22OuterCodeRepresentation (q x) (e v))
    (hq : q.range = ChiefFlag.Kernel) : Nat.card (⁅V,X⁆ : Subgroup G) = 32 := by
  have hWV : ⁅V,X⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp hXV
  let j : (⁅V,X⁆ : Subgroup G) ≃ codeCommutator ChiefFlag.Kernel := {
    toFun w := ⟨e (Additive.ofMul (inclusion hWV w)),
      (m22_point_commutator_coordinates V X hXV e q he hq _).mp w.property⟩
    invFun w := ⟨(e.symm w).toMul,
      (m22_point_commutator_coordinates V X hXV e q he hq _).mpr
        (by rw [e.apply_symm_apply]; exact w.property)⟩
    left_inv w := by apply Subtype.ext; exact congrArg (fun v : Additive V => (v.toMul : G)) (e.symm_apply_apply _)
    right_inv w := by apply Subtype.ext; exact e.apply_symm_apply _ }
  rw [Nat.card_congr j,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    ChapterH.Section13To16.M22Local.Hexad.NativeSource.commutator_finrank]
  decide

variable [Finite G]

/-- The residual's full two-group kernel determines the complete native
hexad-core image, with the original subgroup inclusion retained. -/
theorem m22_point_core_range
    (L : Subgroup G) (z : G)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    ((m22ToPairStabilizer.comp M22ChapterH.Hexad.Action.Inner.subtype).comp
      (f.comp (inclusion (Centralizer.localTwoCore_le L z)))).range = ChiefFlag.Kernel := by
  let R := Centralizer.localResidual L z
  let X := Centralizer.localTwoCore L z
  have hi : (inclusion (Centralizer.localTwoCore_le L z)).range = pCore 2 R := by
    ext r
    constructor
    · rintro ⟨x,rfl⟩
      obtain ⟨a,ha,he⟩ := x.property
      exact (show a = inclusion (Centralizer.localTwoCore_le L z) x from Subtype.ext he) ▸ ha
    · intro hr
      exact ⟨⟨r,mem_map_of_mem R.subtype hr⟩,rfl⟩
  have hm : (pCore 2 R).map f = pCore 2 M22ChapterH.Hexad.Action.Inner := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self_of_surjective hf]
  rw [MonoidHom.range_comp,MonoidHom.range_comp,hi,hm,←Subgroup.map_map]
  exact M22ChapterH.Hexad.inner_kernel_map_pair

/-- Source 8.2.11 computes the original V_z, starting from the literal
point-residual map and its whole kernel, with no core-image premise. -/
theorem m22_point_residual_commutator_card
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : G)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22OuterCodeRepresentation (m22ToPairStabilizer (f r).val) (e v)) :
    Nat.card (Centralizer.commutatorSpace L V z) = 32 := by
  exact m22_point_commutator_card V (Centralizer.localTwoCore L z)
    (((Centralizer.localTwoCore_le L z).trans
      ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLN) e
    ((m22ToPairStabilizer.comp M22ChapterH.Hexad.Action.Inner.subtype).comp
      (f.comp (inclusion (Centralizer.localTwoCore_le L z))))
    (fun x v => he (inclusion (Centralizer.localTwoCore_le L z) x) v)
    (m22_point_core_range L z f hf hk)

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
