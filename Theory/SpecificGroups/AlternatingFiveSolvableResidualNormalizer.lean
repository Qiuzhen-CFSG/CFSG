module
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Solvable two-perfect normalizer actors on A₅

A two-perfect actor induces only inner automorphisms on A₅. If a Sylow
four-group normalizes that solvable actor, it normalizes its inner image.
Their product is a solvable Sylow overgroup in A₅ and therefore normalizes
the four-group. Pulling back the inner action proves the original actor
normalizes the embedded Sylow subgroup. The ambient centralizer need not
be trivial.

Source application: the fixed-vector obstruction in Aschbacher–Smith
10.2.1, printed p.743.
-/
public noncomputable section
open Subgroup
namespace Theory.SpecificGroups
variable {G : Type*} [Group G] [Finite G]

theorem alternatingFive_solvable_residual_normalizes_sylow (A : Subgroup G) (e : A ≃* alternatingGroup (Fin 5))
    (P : Sylow 2 A) (Y : Subgroup G) [Group.IsSolvable Y]
    (hp : IsPPerfect 2 Y) (hYA : Y ≤ normalizer (A:Set G))
    (hPY : (P:Subgroup A).map A.subtype ≤ normalizer (Y:Set G)) :
    Y ≤ normalizer ((P:Subgroup A).map A.subtype : Set G) := by
  let a : Y →* MulAut A := A.normalizerMonoidHom.comp (inclusion hYA)
  obtain ⟨f,hf⟩ := AlternatingFiveProjection.exists_inner_lift hp a e
  have hc (y : Y) : MulAut.conj (f y) = a y := DFunLike.congr_fun hf y
  have hconj (y : Y) (x : A) :
      ((f y : A):G)*x*((f y:A):G)⁻¹ = (y:G)*x*(y:G)⁻¹ :=
    congrArg Subtype.val (MulEquiv.congr_fun (hc y) x)
  have hcinj : Function.Injective (MulAut.conj : A →* MulAut A) := by
    intro x y he
    apply e.injective
    apply MulAut.conj_injective_of_center_eq_bot
      (alternatingGroup.center_eq_bot (by simp))
    have hh := congrArg (MulAut.congr e) he
    simpa only [MulAut.congr_conj] using hh
  have hn : (P:Subgroup A) ≤ normalizer (f.range:Set A) := by
    apply le_normalizer_iff.mpr
    rintro p hp _ ⟨y,rfl⟩
    let z : Y := ⟨(p:G)*y*(p:G)⁻¹,
      le_normalizer_iff.mp hPY (p:G) (mem_map_of_mem A.subtype hp) y y.property⟩
    refine ⟨z,?_⟩
    apply hcinj
    simp only [map_mul,map_inv,hc]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    change (p:G)*(y:G)*(p:G)⁻¹*(x:G)*((p:G)*(y:G)*(p:G)⁻¹)⁻¹ = _
    change _ = (p:G)*((y:G)*((p:G)⁻¹*(x:G)*(p:G))*(y:G)⁻¹)*(p:G)⁻¹
    group
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  let : Group.IsNilpotent (P:Subgroup A) := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (P:Subgroup A) := inferInstance
  let : Group.IsSolvable (f.range ⊔ (P:Subgroup A) : Subgroup A) :=
    Group.isSolvable_sup_of_normalizes f.range (P:Subgroup A) hn
  have hnorm := alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv
    e P (f.range ⊔ (P:Subgroup A)) le_sup_right
  apply le_normalizer_iff.mpr
  rintro y hy _ ⟨p,hp,rfl⟩
  refine ⟨f ⟨y,hy⟩*p*(f ⟨y,hy⟩)⁻¹,
    le_normalizer_iff.mp hnorm _
      (show f ⟨y,hy⟩ ∈ f.range ⊔ (P:Subgroup A) from (le_sup_left : f.range ≤ f.range ⊔ (P:Subgroup A)) ⟨⟨y,hy⟩,rfl⟩) p hp,?_⟩
  exact hconj ⟨y,hy⟩ p
end Theory.SpecificGroups
