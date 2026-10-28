module
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normal residuals of centralizers in a normal component

The element centralizer in a normal subgroup is normal in the full
centralizer. Its characteristic solvable residual is therefore normal
through the original inclusion. Separately, an ordinary component
centralizes the two-core; Cauchy's theorem supplies an involution there
whenever that core is nontrivial.

Source: standard component and characteristic-subgroup calculus, used in
Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The residual of an element centralizer in a normal subgroup is normal
in the full element centralizer, through the literal inclusion. -/
theorem centralizer_residual_normal (K : Subgroup G) [K.Normal] (x : K) :
    ((solvableResidual (centralizer ({x} : Set K))).map
      (K.subtype.elementCentralizerMap x)).Normal := by
  let C := centralizer ({(x : G)} : Set G)
  let D := centralizer ({x} : Set K)
  let f : D →* C := K.subtype.elementCentralizerMap x
  have hi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun y : C => (y : G)) hab))
  have hr : f.range = K.subgroupOf C := by
    ext y
    constructor
    · rintro ⟨d,rfl⟩
      exact d.val.property
    · intro hy
      refine ⟨⟨⟨y.val,hy⟩,?_⟩,Subtype.ext rfl⟩
      exact mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp y.property))
  let : f.range.Normal := hr.symm ▸ (inferInstance : (K.subgroupOf C).Normal)
  let e : D ≃* f.range := MonoidHom.ofInjective hi
  have he : (solvableResidual f.range).map f.range.subtype =
      (solvableResidual D).map f := by
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    rfl
  change ((solvableResidual D).map f).Normal
  rw [←he,←normalizer_eq_top_iff]
  apply top_unique
  simpa only [normalizer_eq_top] using
    normalizer_le_normalizer_characteristic_image f.range (solvableResidual f.range)

/-- A nontrivial two-core supplies an involution centralizing every element
of the specified ordinary component. -/
theorem component_core_involution (H : Subgroup G) (hne : H.pCoreIn 2 ≠ ⊥)
    (K : Subgroup H) (hK : IsComponent H K) :
    ∃ r : H.pCoreIn 2, orderOf r = 2 ∧
      K.map H.subtype ≤ centralizer ({(r : G)} : Set G) := by
  let P := H.pCoreIn 2
  let : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hne
  have hp : IsPGroup 2 P := isPGroup_pCoreIn 2 H
  have hd : 2 ∣ Nat.card P := hp.card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' 2 hd
  refine ⟨r,hr,?_⟩
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hc := hK.le_centralizer_of_solvable_normal (pCore 2 H)
  obtain ⟨s,hs,hsr⟩ := r.property
  rintro k ⟨k,hk,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  rw [←hsr]
  exact (congrArg H.subtype (hc hk s hs)).symm


end Theory.GroupTheory
