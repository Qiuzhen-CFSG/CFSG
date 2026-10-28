module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer
public import Theory.GroupTheory.PGroup.NormalSupplementKernel

/-!
# The actual action kernel inside the original KT

The kernel on K is exactly its two-core under the prescribed module chart.
The quotient KT/K is a two-group, so the whole action kernel inside KT
is a normal two-group. It therefore lies in the original Sylow T.
The full ambient centralizer is not restricted.

Source: the kernel-normalization argument of G.2.3 used after
Aschbacher--Smith12.7.18, printed pp.333 and845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The literal KT action kernel lies in its two-core and the original Sylow. -/
theorem original_tripleSix_action_kernel
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    (K ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ≤
      (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    (K ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ≤ (T : Subgroup G) := by
  let M := K ⊔ (T : Subgroup G)
  let A := K.subgroupOf M
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hMN : M ≤ normalizer (U : Set G) := sup_le D.normalizes hTN
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMN)
  obtain ⟨f0,_,hfk,_,_⟩ := original_tripleSix_full_automizer h structural D a
  let f := f0.comp α
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  have hgen : A ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ M from le_sup_left)
      (show (T : Subgroup G) ≤ M from le_sup_right)]
    exact subgroupOf_self M
  have hk : IsPGroup 2 (f.comp A.subtype).ker := by
    let e : (f.comp A.subtype).ker →* pCore 2 K :=
      { toFun := fun x => ⟨⟨x.val.val.val,x.val.property⟩,by
          apply (QuotientGroup.eq_one_iff _).mp
          apply a.groupEquiv.injective
          apply Subtype.ext
          have he := hfk (⟨x.val.val.val,x.val.property⟩ : K)
          exact he.symm.trans (x.property.trans
            (congrArg Subtype.val (map_one a.groupEquiv)).symm)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply (show IsPGroup 2 (pCore 2 K) from pCore_isPGroup).of_injective e
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 K => (x.val : G)) he
  have hp := f.kernel_isPGroup_of_normal_supplement A
    ((T : Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype hgen hk
  have hkc : f.ker ≤ pCore 2 M := le_sSup ⟨inferInstance,hp⟩
  have hC : M ⊓ centralizer (U : Set G) ≤ M.pCoreIn 2 := by
    rintro x ⟨hx,hxc⟩
    let m : M := ⟨x,hx⟩
    have hα : α m = 1 := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro u
      apply Subtype.ext
      change x * u.val * x⁻¹ = u.val
      rw [← mem_centralizer_iff.mp hxc u.val u.property,mul_inv_cancel_right]
    have hfm : m ∈ f.ker := by
      change f0 (α m) = 1
      rw [hα,map_one]
    exact mem_map_of_mem M.subtype (hkc hfm)
  refine ⟨hC,hC.trans ?_⟩
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right)] using
    pCoreIn_le_sylow M (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))

end CFSG.Quasithin.Chapter12.Section07
