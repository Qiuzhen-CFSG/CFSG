module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.DualOffender.Faithfulness
public import Theory.Representation.QuadraticDuality
public import Theory.GroupTheory.ConjugateSpanSylow
/-!
# The moved dual has no full fixed vectors

An invariant functional on I=[V,L] kills [I,L]. The literal source span
L is perfect, so its action on the elementary V is idempotent: [I,L]=I.
Consequently the full fixed space on I's inverse dual is zero. The proof
uses the actual subgroup inclusion and the original centralizer quotient;
it preserves all central layers of I and asserts no irreducibility.
This supplies the fixed-space hypothesis in the C.5.13 conjugate-generation
bounds. Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
variable {G : Type*} [Group G] (V K : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
/-- An invariant functional vanishes on a commutator-generated moved subgroup. -/
theorem moved_dual_fixed_of_commutator_eq (hc : ⁅⁅V,normalClosure (K : Set G)⁆,normalClosure (K : Set G)⁆ =
    ⁅V,normalClosure (K : Set G)⁆) :
    fixedSpace (movedRepresentation V K).dual ⊤ = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  let I := ⁅V,normalClosure (K : Set G)⁆
  let M := (movedSpace V K).toSubmodule
  let j : Multiplicative M →* G :=
    { toFun := fun w => (w.toAdd.val.toMul : G)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    apply Additive.toMul.injective
    exact Subtype.ext hab
  let D := ((LinearMap.ker f).toAddSubgroup.toSubgroup').map j
  have hID : ⁅I,normalClosure (K : Set G)⁆ ≤ D := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro k hk i hi
    have hiV : i ∈ V := (commutator_le_left _ _) hi
    let w : M := ⟨Additive.ofMul ⟨i,hiV⟩,hi⟩
    let qk : closureImage V K :=
      ⟨QuotientGroup.mk' (centralizer (V : Set G)) k,mem_map_of_mem _ hk⟩
    have hfix : f (movedRepresentation V K qk w) = f w := by
      have he := congrArg (fun z : Module.Dual (ZMod 2) M => z w)
        (hf ⟨qk⁻¹,Subgroup.mem_top _⟩)
      change f (movedRepresentation V K (qk⁻¹)⁻¹ w) = f w at he
      simpa only [inv_inv] using he
    refine ⟨Multiplicative.ofAdd (movedRepresentation V K qk w - w),?_,?_⟩
    · change f (movedRepresentation V K qk w - w) = 0
      rw [map_sub,hfix,sub_self]
    · change ((centralizerQuotient V (QuotientGroup.mk' (centralizer (V : Set G)) k)
          w.val - w.val).toMul : G) = ⁅k,i⁆
      rw [toMul_sub,Subgroup.coe_div,centralizerQuotient_apply,div_eq_mul_inv]
      rfl
  have hiD : I ≤ D := by
    change ⁅I,normalClosure (K : Set G)⁆=I at hc
    rwa [hc] at hID
  apply LinearMap.ext
  intro w
  obtain ⟨a,ha,he⟩ := hiD w.property
  have hw : a = Multiplicative.ofAdd w := hj he
  subst a
  exact ha


private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (A ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (A ⧸ H) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective H)
  let : Group.IsNilpotent (A ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ H) inferInstance

variable [Finite G]
open ConjugateSource.RankOne
/-- The original noncubic source supplies the required commutator idempotence. -/
theorem noncubic_source_moved_dual_fixed (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    fixedSpace (movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual ⊤ = ⊥ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect (noncubic_mem_local_family K T hK h3 hTK P hP)
  let : Group.IsPerfect L := conjugateSpanBy_isPerfect K N
  have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
    (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have hLN : L ≤ N := conjugateSpanBy_le_self hKN
  have hc := commutator_isPPerfect_idempotent L V perfect_twoPerfect hs.1.isPGroup
    (hLN.trans hs.2.2.1)
  apply moved_dual_fixed_of_commutator_eq
  apply map_injective N.subtype_injective
  change (⁅⁅V.subgroupOf N,normalClosure (K.subgroupOf N : Set N)⁆,
    normalClosure (K.subgroupOf N : Set N)⁆).map N.subtype =
    (⁅V.subgroupOf N,normalClosure (K.subgroupOf N : Set N)⁆).map N.subtype
  simp only [map_commutator]
  rw [map_subgroupOf_eq_of_le (show V ≤ N from hs.2.1),source_closure_map K N hKN]
  exact hc
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.DualOffender
