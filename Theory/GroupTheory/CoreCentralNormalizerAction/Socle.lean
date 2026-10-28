module
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleSolvableImage

/-!
# The actual simple subgroup in a component action image

The image of K on its core-central quotient is precisely its inner
automorphism subgroup. Any actor containing K therefore contains that
inner subgroup. When K/O₂(K) is quasisimple, this subgroup is simple,
normal and self-centralizing, so it is the full generalized Fitting
subgroup of the actual action image.

Source application: the effective component action in Aschbacher--Smith
6.1.4 and A.3.15, printed pp.665 and 50--51.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

private theorem core_projection_surjective (K : Subgroup G) :
    Function.Surjective (coreCentralProjection K) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

private theorem core_action_inner (K : Subgroup G) (k : K) :
    normalizerCoreCentralAction K ⟨k,K.le_normalizer k.property⟩ =
      MulAut.conj (coreCentralProjection K k) := by
  ext y
  obtain ⟨x,rfl⟩ := core_projection_surjective K y
  rw [normalizerCoreCentralAction_apply,MulAut.conj_apply,←map_inv,←map_mul,←map_mul]
  rfl

/-- The image of the original K is exactly the inner subgroup on its
literal core-central quotient. -/
theorem coreCentralActorImage_self (K : Subgroup G) :
    coreCentralActorImage K K = MulAut.innerSubgroup (coreCentralQuotient K) := by
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    exact ⟨coreCentralProjection K ⟨k,hk⟩,(core_action_inner K ⟨k,hk⟩).symm⟩
  · rintro _ ⟨x,rfl⟩
    obtain ⟨k,rfl⟩ := core_projection_surjective K x
    exact ⟨⟨k,K.le_normalizer k.property⟩,k.property,core_action_inner K k⟩

private theorem fitting_of_inner_le {C : Type*} [Group C] [Finite C] [IsQuasisimple C]
    (A : Subgroup (MulAut C)) (hIA : MulAut.innerSubgroup C ≤ A) :
    (generalizedFitting A).map A.subtype = MulAut.innerSubgroup C := by
  let I := MulAut.innerSubgroup C
  let D := I.subgroupOf A
  let e : D ≃* I := subgroupOfEquivOfLe hIA
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : IsSimpleGroup I := (innerEquivCentralQuotient (H := C)).isSimpleGroup
  let : IsQuasisimple I := IsQuasisimple.of_surjective
    (MulAut.conj : C →* MulAut C).rangeRestrict (MulAut.conj : C →* MulAut C).rangeRestrict_surjective
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have hC : centralizer (D : Set A) = ⊥ := by
    apply bot_unique
    intro a ha
    apply Subtype.ext
    apply (centralizer_inner_eq_bot_of_perfect (H := C)).le
    intro i hi
    exact congrArg Subtype.val (ha ⟨i,hIA hi⟩ hi)
  rw [generalizedFitting_eq_of_quasisimple_centralizer_le D (hC.le.trans bot_le),
    map_subgroupOf_eq_of_le hIA]

/-- The original action image has the actual inner simple subgroup as F*.
This makes no quasithinness assertion about an arbitrary quotient kernel. -/
theorem coreCentralActorImage_generalizedFitting [Finite G]
    (K H : Subgroup G) (hKH : K ≤ H) [IsQuasisimple (K ⧸ pCore 2 K)] :
    (generalizedFitting (coreCentralActorImage K H)).map (coreCentralActorImage K H).subtype =
      MulAut.innerSubgroup (coreCentralQuotient K) := by
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  let : IsQuasisimple (coreCentralQuotient K) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center (K ⧸ pCore 2 K))) (QuotientGroup.mk'_surjective _)
  apply fitting_of_inner_le
  rw [←coreCentralActorImage_self K]
  exact map_mono (subgroupOf_mono _ hKH)

end Theory.GroupTheory
