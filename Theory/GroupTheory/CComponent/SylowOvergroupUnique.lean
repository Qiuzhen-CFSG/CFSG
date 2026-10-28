module

public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.Sylow

/-!
# Uniqueness of C-components in Sylow overgroups

The property considered here says that every overgroup of a full Sylow
two-subgroup has at most one C-component. It lifts through solvable kernels:
map the overgroup and its components, then use the injectivity of the
solvable-quotient correspondence for components. A unique component is
characteristic, including under automorphisms induced from outside the group.

This is the model calculation used in the moved-component restriction of
Aschbacher--Smith, A.3.12 and 1.2.8(1), printed pp.47--48 and 506.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Every overgroup of a full Sylow two-subgroup has at most one C-component. -/
@[expose] def SylowOvergroupComponentUnique (G : Type*) [Group G] : Prop :=
  ∀ (S : Sylow 2 G) (P : Subgroup G), (S : Subgroup G) ≤ P →
    ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C

namespace SylowOvergroupComponentUnique

private theorem component_map_injective [Finite G]
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    {B C : Subgroup G} (hB : B.IsCComponent) (hC : C.IsCComponent)
    (he : B.map f = C.map f) : B = C := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  apply hB.eq_of_map_quotient_eq hC f.ker
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_map, map_map]
  have hc : e.toMonoidHom.comp (QuotientGroup.mk' f.ker) = f := by
    ext x
    rfl
  rw [hc]
  exact he

/-- Solvable kernels preserve uniqueness in the direction needed for covers. -/
theorem of_surjective [Finite G] (f : G →* H) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] (h : SylowOvergroupComponentUnique H) :
    SylowOvergroupComponentUnique G := by
  intro S P hSP B C hB hC
  let g := f.subgroupMap P
  let : Group.IsSolvable g.ker := by
    rw [show g = f.subgroupMap P from rfl, ker_subgroupMap]
    exact Group.isSolvable_of_isSolvable_injective
      (f := P.subtype.subgroupComap f.ker) (fun a b he =>
        Subtype.ext (Subtype.ext (congrArg (fun x : f.ker => (x : G)) he)))
  apply component_map_injective g (f.subgroupMap_surjective P) hB hC
  exact h (S.mapSurjective hf) (P.map f) (map_mono hSP) _ _
    (cComponent_map_of_solvable_ker hB g (f.subgroupMap_surjective P))
    (cComponent_map_of_solvable_ker hC g (f.subgroupMap_surjective P))

/-- Transport from the actual model, including changes of subgroup coordinates. -/
theorem of_equiv [Finite G] (e : G ≃* H) (h : SylowOvergroupComponentUnique H) :
    SylowOvergroupComponentUnique G := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact of_surjective e.toMonoidHom e.surjective h

/-- Uniqueness makes a component characteristic, rather than merely normal. -/
theorem characteristic (h : SylowOvergroupComponentUnique G)
    (S : Sylow 2 G) (P : Subgroup G) (hSP : (S : Subgroup G) ≤ P)
    {B : Subgroup P} (hB : B.IsCComponent) : B.Characteristic := by
  apply characteristic_iff_map_eq.mpr
  intro e
  exact h S P hSP _ _ (hB.map_equiv e) hB

/-- In a nonabelian simple group only proper overgroups need to be checked. -/
theorem of_proper_overgroups [IsSimpleGroup G] [Group.IsPerfect G]
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G),
      (S : Subgroup G) ≤ P → P ≠ ⊤ →
      ∀ B C : Subgroup P, B.IsCComponent → C.IsCComponent → B = C) :
    SylowOvergroupComponentUnique G := by
  intro S P hSP B C hB hC
  by_cases ht : P = ⊤
  · subst P
    let : IsSimpleGroup (⊤ : Subgroup G) := (topEquiv (G := G)).isSimpleGroup
    let : Group.IsPerfect (⊤ : Subgroup G) :=
      Group.IsPerfect.ofSurjective (f := (topEquiv (G := G)).symm.toMonoidHom)
        (topEquiv (G := G)).symm.surjective
    have htop : (⊤ : Subgroup G).IsCComponent :=
      isCComponent_of_isSimpleGroup_of_isPerfect .top
    exact (htop.eq_top_of_isCComponent hB).trans
      (htop.eq_top_of_isCComponent hC).symm
  · exact h S P hSP ht B C hB hC

/-- Rank-one models with solvable proper Sylow overgroups supply the property. -/
theorem of_solvable_proper_overgroups [IsSimpleGroup G] [Group.IsPerfect G]
    (h : ∀ (S : Sylow 2 G) (P : Subgroup G),
      (S : Subgroup G) ≤ P → P ≠ ⊤ → Group.IsSolvable P) :
    SylowOvergroupComponentUnique G := by
  apply of_proper_overgroups
  intro S P hSP ht B C hB _hC
  let := h S P hSP ht
  exact (hB.not_isSolvable inferInstance).elim

/-- An ambient Sylow normalizing the containing subnormal subgroup fixes
its local component when the intrinsic Sylow overgroups have unique components.
The intersection with the containing subgroup is the original full Sylow. -/
theorem normalizes_local_component [Finite G]
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : (B.subgroupOf (B ⊔ (T : Subgroup G))).IsCComponent)
    (hK : K.IsSubnormal) (hBK : B ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (h : SylowOvergroupComponentUnique K) :
    (T : Subgroup G) ≤ normalizer (B : Set G) := by
  let J := B ⊔ (T : Subgroup G)
  let P := J ⊓ K
  have hBP : B ≤ P := le_inf le_sup_left hBK
  have hPK : P ≤ K := inf_le_right
  have hBJ : (B.subgroupOf P).IsCComponent := hB.subgroupOf_of_le hBP inf_le_left
  obtain ⟨S,hS⟩ := T.exists_subgroupOf_eq_of_subnormal K hK
  have hSP : (S : Subgroup K) ≤ P.subgroupOf K := by
    rw [hS]
    intro s hs
    exact ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hs,s.property⟩
  let e : P ≃* P.subgroupOf K := (subgroupOfEquivOfLe hPK).symm
  have hu (D : Subgroup P) (hD : D.IsCComponent) : D = B.subgroupOf P := by
    apply map_injective (f := e.toMonoidHom) e.injective
    exact h S (P.subgroupOf K) hSP _ _ (hD.map_equiv e) (hBJ.map_equiv e)
  let : (B.subgroupOf P).Characteristic := characteristic_iff_map_eq.mpr
    (fun a => hu _ (hBJ.map_equiv a))
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf ((show (T : Subgroup G) ≤ J from le_sup_right).trans J.le_normalizer)
      hTK).trans inf_normalizer_le_normalizer_inf
  have hn := hTP.trans (normalizer_le_normalizer_characteristic_image P (B.subgroupOf P))
  simpa only [map_subgroupOf_eq_of_le hBP] using hn

end SylowOvergroupComponentUnique
end Theory.GroupTheory
