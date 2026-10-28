module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalLinearQuotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The full original cubic endpoint as a semidirect product

The actual opposite factor and outer involution form the order-48 Levi
subgroup. Restricting the previously proved linear quotient to this subgroup
is bijective, giving an actual GL₂(3) marking. Pulling conjugation back along
that equivalence produces the full action on the original order-243 core.
The resulting semidirect product is isomorphic to the whole cubic normalizer;
its two coordinate inclusions and linear quotient have their literal formulas.
Its whole Borel is the preimage of the corresponding linear Borel.

The kernel of full-core conjugation is exactly the original core center.
This advances the endpoint comparison in Aschbacher–Smith I.4.5, printed
p.417, using the marked splitting of Fong–Wong §3B, Nagoya Math. J.36
(1969), p.156. Identification of this action with the Atlas action and
compatibility of the two endpoints still require proof.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

theorem cubicCore_le_normalizer : cubicOddCore c t.x ≤ cubicNormalizer c t.x := by
  rw [t.left_ambient_normalizer]
  exact le_sup_left.trans le_sup_left

theorem cubicLevi_le_normalizer : t.leftCubicLevi ≤ cubicNormalizer c t.x := by
  rw [cubic_normalizer_of_local_inverter c t.x t.x_order t.n t.invert_left]
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

/-- Conjugation on the whole original core. -/
def cubicCoreAction : cubicNormalizer c t.x →* MulAut (cubicOddCore c t.x) :=
  (cubicOddCore c t.x).normalizerMonoidHom.comp (inclusion t.cubic_core_normalized)

/-- Full-core conjugation has precisely the original center as kernel. -/
theorem cubicCoreAction_kernel (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.cubicCoreAction.ker=(centerIn (cubicOddCore c t.x)).subgroupOf (cubicNormalizer c t.x) := by
  ext a
  constructor
  · intro ha
    have hq : a ∈ t.cubicCentralQuotientAction.ker := by
      change quotientAut _ (t.cubicCoreAction a)=1
      rw [show t.cubicCoreAction a=1 from ha,map_one]
    rw [t.cubicCentralQuotientAction_kernel hc] at hq
    refine ⟨hq,?_⟩
    intro v hv
    have h := congrArg (fun f : MulAut (cubicOddCore c t.x) => (f ⟨v,hv⟩:G)) ha
    change (a:G)*v*(a:G)⁻¹=v at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · rintro ⟨ha,haz⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (a:G)*(v:G)*(a:G)⁻¹=(v:G)
    have hz : (v:G)*(a:G)=(a:G)*(v:G) := haz v v.property
    rw [←hz,mul_inv_cancel_right]

noncomputable def cubicLeviLinearHom (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicLevi →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  (t.cubicLinearAction hc).comp (inclusion t.cubicLevi_le_normalizer)

theorem cubicLeviLinearHom_injective (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Injective (t.cubicLeviLinearHom hc) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  have h : inclusion t.cubicLevi_le_normalizer a ∈ (t.cubicLinearAction hc).ker := ha
  rw [t.cubicLinearAction_kernel hc] at h
  have hz := (disjoint_iff.mp (t.maximal_left_cubic_levi_split hc).2).le
    (show (a:G)∈cubicOddCore c t.x ⊓ t.leftCubicLevi from ⟨h,a.property⟩)
  exact Subtype.ext hz

/-- The existing linear quotient identifies the literal actor, not just its order. -/
noncomputable def cubicLeviLinearEquiv (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicLevi ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  MulEquiv.ofBijective (t.cubicLeviLinearHom hc)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨t.cubicLeviLinearHom_injective hc,by
        rw [t.leftCubicLevi_card,Matrix.card_GL_field]; decide⟩)

@[simp] theorem cubicLeviLinearEquiv_apply (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : t.leftCubicLevi) :
    t.cubicLeviLinearEquiv hc a=t.cubicLinearAction hc (inclusion t.cubicLevi_le_normalizer a) := rfl

/-- The full action of GL₂(3) on the original core, with the actor marked by the linear quotient. -/
noncomputable def cubicGLCoreAction (hc : Nat.card (cubicOddCore c t.x)=243) :
    Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) →* MulAut (cubicOddCore c t.x) :=
  t.cubicCoreAction.comp ((inclusion t.cubicLevi_le_normalizer).comp
    (t.cubicLeviLinearEquiv hc).symm.toMonoidHom)

/-- The central quotient of the full action is exactly the prescribed GL₂(3) matrix. -/
theorem cubicGLCoreAction_central_quotient (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    t.cubicCentralQuotientCoordinates hc (quotientAut _ (t.cubicGLCoreAction hc a))=a :=
  (t.cubicLeviLinearEquiv hc).apply_symm_apply a

theorem cubicGLCoreAction_injective (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Injective (t.cubicGLCoreAction hc) := by
  intro a b h
  have hh := congrArg (fun f => t.cubicCentralQuotientCoordinates hc (quotientAut _ f)) h
  simpa only [t.cubicGLCoreAction_central_quotient hc] using hh

noncomputable def cubicSplitHom (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x) ⋊[t.cubicGLCoreAction hc]
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) →* cubicNormalizer c t.x :=
  SemidirectProduct.lift (inclusion t.cubicCore_le_normalizer)
    ((inclusion t.cubicLevi_le_normalizer).comp (t.cubicLeviLinearEquiv hc).symm.toMonoidHom)
    (by intro a; ext v; rfl)

theorem cubicSplitHom_linear (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : (cubicOddCore c t.x) ⋊[t.cubicGLCoreAction hc]
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    t.cubicLinearAction hc (t.cubicSplitHom hc a)=a.right := by
  change t.cubicLinearAction hc
    (inclusion t.cubicCore_le_normalizer a.left *
      inclusion t.cubicLevi_le_normalizer ((t.cubicLeviLinearEquiv hc).symm a.right))=a.right
  rw [map_mul]
  have hzero : t.cubicLinearAction hc (inclusion t.cubicCore_le_normalizer a.left)=1 := by
    rw [←MonoidHom.mem_ker,t.cubicLinearAction_kernel hc]
    exact a.left.property
  rw [hzero,one_mul]
  exact (t.cubicLeviLinearEquiv hc).apply_symm_apply _

theorem cubicSplitHom_bijective (hc : Nat.card (cubicOddCore c t.x)=243) :
    Function.Bijective (t.cubicSplitHom hc) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b h
    have hr : a.right=b.right := by
      simpa only [t.cubicSplitHom_linear hc] using congrArg (t.cubicLinearAction hc) h
    have hl := congrArg Subtype.val h
    change (a.left:G)*((t.cubicLeviLinearEquiv hc).symm a.right:G)=
      (b.left:G)*((t.cubicLeviLinearEquiv hc).symm b.right:G) at hl
    rw [hr] at hl
    exact SemidirectProduct.ext (Subtype.ext (mul_right_cancel hl)) hr
  · rw [SemidirectProduct.card,t.left_ambient_normalizer_card,Matrix.card_GL_field]
    norm_num

/-- An actual equivalence for the whole original endpoint, with its full core action. -/
noncomputable def cubicSplitEquiv (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicOddCore c t.x) ⋊[t.cubicGLCoreAction hc]
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) ≃* cubicNormalizer c t.x :=
  MulEquiv.ofBijective (t.cubicSplitHom hc) (t.cubicSplitHom_bijective hc)

@[simp] theorem cubicSplitEquiv_inl (hc : Nat.card (cubicOddCore c t.x)=243)
    (v : cubicOddCore c t.x) :
    (t.cubicSplitEquiv hc (SemidirectProduct.inl v):G)=v := by
  change (t.cubicSplitHom hc (SemidirectProduct.inl v):G)=v
  rw [cubicSplitHom,SemidirectProduct.lift_inl]
  rfl

@[simp] theorem cubicSplitEquiv_inr (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (t.cubicSplitEquiv hc (SemidirectProduct.inr a):G)=
      ((t.cubicLeviLinearEquiv hc).symm a:G) := by
  change (t.cubicSplitHom hc (SemidirectProduct.inr a):G)=_
  rw [cubicSplitHom,SemidirectProduct.lift_inr]
  rfl

theorem cubicSplitEquiv_linear (hc : Nat.card (cubicOddCore c t.x)=243)
    (a : (cubicOddCore c t.x) ⋊[t.cubicGLCoreAction hc]
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))) :
    t.cubicLinearAction hc (t.cubicSplitEquiv hc a)=a.right := t.cubicSplitHom_linear hc a


/-- The entire original Borel is the inverse image of its linear Borel under the split coordinates. -/
theorem cubicSplitEquiv_borel (hc : Nat.card (cubicOddCore c t.x)=243) :
    (t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x)).comap
        (t.cubicSplitEquiv hc).toMonoidHom =
      (normalizer (((t.leftCoreExtension.subgroupOf (cubicNormalizer c t.x)).map
        (t.cubicLinearAction hc)):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))).comap
          SemidirectProduct.rightHom := by
  rw [←t.cubicLinearAction_borel_image hc]
  have hk : (t.cubicLinearAction hc).ker≤
      t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x) := by
    rw [t.cubicLinearAction_kernel hc]
    exact fun _ h=>mem_sup_left (mem_sup_left h)
  have hh := comap_map_eq_self hk
  ext a
  change t.cubicSplitEquiv hc a∈t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x) ↔
    a.right∈(t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x)).map (t.cubicLinearAction hc)
  rw [←t.cubicSplitEquiv_linear hc a]
  exact (SetLike.ext_iff.mp hh (t.cubicSplitEquiv hc a)).symm

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
