module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCentralizer
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.GroupDeductions

/-!
# The original Mathieu plane residual is a local component

The intrinsic C-component condition on L makes its faithful M24 action
kernel solvable. The native plane-fixer calculation then proves solvability
of C_L(U), retaining that original kernel. The full GL3(2) action of N_L(U)
has exactly this relative centralizer as kernel. Lifting the simple perfect
quotient through its solvable kernel makes N_L(U)^∞ a C-component, first
intrinsically and then in N_{N_G(L)}(U).

NonFFSourceMathieuM24Component applies these theorems to the original
Sylow-positioned offender and its compatible canonical pair, and constructs
a containing normal component of N_G(U). NonFFSourceMathieuM24Recognition
proves quasisimplicity of that component's two-core quotient and its equality
with this same residual.
Source: Aschbacher--Smith H.15.6(2), 8.2.6 and the following paragraph,
printed pp.401,717, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open PairOvergroups PairOvergroups.QuotientConstruction
open MathieuCode MathieuCode.TrioCalculation
open scoped Pointwise MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
public noncomputable section
variable {G : Type*} [Group G] [Finite G]

/-- Solvability of the original relative centralizer, retaining the full
component action kernel and the marked plane. -/
theorem plane_centralizer_solvable
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hLW : L ≤ normalizer (W : Set G)) (_hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) := by
  let C := L ⊓ centralizer (U : Set G)
  have hproper : q.ker ≠ ⊤ := by
    let := m24_isSimpleGroup
    obtain ⟨y,hy⟩ := exists_ne (1 : M24)
    obtain ⟨l,rfl⟩ := hq y
    intro he
    exact hy (show l ∈ q.ker from he.symm ▸ mem_top l)
  have hker := kernel_le_solvableRadical_of_top_isCComponent hL q hproper
  let : Group.IsSolvable q.ker :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
  let f := q.comp (inclusion (show C ≤ L from inf_le_left))
  let k : f.ker →* q.ker :=
    ((inclusion (show C ≤ L from inf_le_left)).comp f.ker.subtype).codRestrict _
      (fun x => x.property)
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => z.val.val) he))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hk
  have hfix (x : f.range) (v : Vector) :
      cocodeRepresentation x.val (standardPlaneMap v) = standardPlaneMap v := by
    obtain ⟨l,hl⟩ := x.property
    obtain ⟨w,hw⟩ := F.surjective (standardPlaneMap v)
    have hwU : (w.toMul : G) ∈ U := (hplane w.toMul).mpr
      (hw.symm ▸ LinearMap.mem_range_self standardPlaneMap v)
    have hcomm : W.normalizerMonoidHom ⟨l.val,hLW l.property.1⟩ w.toMul = w.toMul := by
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul).mpr (l.property.2 _ hwU).symm
    change cocodeRepresentation x.val (standardPlaneMap v) = _
    rw [←hl,←hw]
    exact (hF ⟨l.val,l.property.1⟩ w.toMul).symm.trans
      (congrArg (fun z : W => F (Additive.ofMul z)) hcomm)
  let : Group.IsSolvable f.range := plane_fixer_solvable _ hfix
  let : Group.IsSolvable f.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  exact Group.isSolvable_of_ker_le_range f.rangeRestrict.ker.subtype f.rangeRestrict (by simp)

/-- The actual intrinsic residual of N_L(U) is a C-component. -/
theorem plane_normalizer_residual_component
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).IsCComponent := by
  let N := L ⊓ normalizer (U : Set G)
  let C := L ⊓ centralizer (U : Set G)
  let : Group.IsSolvable C := plane_centralizer_solvable W L U hL hLW hUW q hq F hF hplane
  obtain ⟨e,π,hπ,hker,_⟩ := plane_normalizer_action W L U hLW hUW q hq F hF hplane
  let k : π.ker →* C :=
    { toFun := fun x => ⟨x.val.val,x.val.property.1,by
        exact hker.le x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hk : Function.Injective k := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => (z : G)) he))
  let : Group.IsSolvable π.ker := Group.isSolvable_of_isSolvable_injective hk
  let : Finite (BinaryLinear.GL Vector) := Finite.of_surjective π hπ
  let : Group.IsPerfect (BinaryLinear.GL Vector) := BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (BinaryLinear.GL Vector) :=
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.isSimpleGroup
  apply residual_isCComponent_of_surjective π hπ
  rw [solvableResidual_eq_top]
  let : IsSimpleGroup (⊤ : Subgroup (BinaryLinear.GL Vector)) := topEquiv.isSimpleGroup
  exact isCComponent_of_isSimpleGroup_of_isPerfect .top

/-- Relative componenthood in N_{N_G(L)}(U), on the literal embedded residual. -/
theorem plane_residual_relative_component
    (W L U : Subgroup G) [IsElementaryAbelian 2 W]
    (hL : (⊤ : Subgroup L).IsCComponent)
    (hLW : L ≤ normalizer (W : Set G)) (hUW : U ≤ W)
    (q : L →* M24) (hq : Function.Surjective q)
    (F : Additive W ≃ₗ[ZMod 2] Cocode)
    (hF : ∀ (l : L) (w : W),
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,hLW l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)))
    (hplane : ∀ w : W, (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range) :
    ((Chapter8.Section02.Normalizer.localResidual L U).subgroupOf
      (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent := by
  let H := L ⊓ normalizer (U : Set G)
  let M := normalizer (L : Set G) ⊓ normalizer (U : Set G)
  have hHM : H ≤ M := inf_le_inf_right _ L.le_normalizer
  have hMH : M ≤ normalizer (H : Set G) :=
    (le_inf inf_le_left (inf_le_right.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let : (H.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer hMH
  let eH := (subgroupOfEquivOfLe hHM).symm
  have hR := plane_normalizer_residual_component W L U hL hLW hUW q hq F hF hplane
  have hm := (hR.map_equiv eH).map_subtype (inferInstance : (H.subgroupOf M).Normal).isSubnormal
  have heq : ((solvableResidual H).map eH.toMonoidHom).map (H.subgroupOf M).subtype =
      ((solvableResidual H).map H.subtype).subgroupOf M := by
    ext x
    constructor
    · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact mem_map_of_mem H.subtype hz
    · rintro ⟨z,hz,hzx⟩
      refine ⟨eH z,mem_map_of_mem eH.toMonoidHom hz,?_⟩
      exact Subtype.ext hzx
  rwa [heq] at hm
end
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
