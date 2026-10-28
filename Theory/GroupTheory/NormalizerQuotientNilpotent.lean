module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.PerfectCentralQuotient
public import Mathlib.GroupTheory.Nilpotent

/-!
# Nilpotence of normalizer quotients

The normalizer quotient N_G(U)/U maps to Out(U). If C_G(U) is central
in G, the kernel of this map is central. A finite two-group outer group
therefore makes the normalizer quotient nilpotent. Mapping through a group
homomorphism preserves this conclusion whenever its kernel lies in U.

The central-quotient action also embeds Out(A) in Out(A/Z(A)) for perfect A.
These results use the actual relative normal subgroup U inside N_G(U).
Source application: Aschbacher--Smith, A.3.6(4), pp.43--45, and 11.4.3, p.778.
-/

public noncomputable section
open Subgroup
namespace Subgroup.NormalizerOuterQuotient

variable {G : Type*} [Group G]

abbrev Quotient (U : Subgroup G) := normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))

def outerAction (U : Subgroup G) : Quotient U →* MulAut.Outer U :=
  QuotientGroup.lift (U.subgroupOf (normalizer (U : Set G)))
    ((QuotientGroup.mk' (MulAut.innerSubgroup U)).comp U.normalizerMonoidHom) (by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨⟨x, hx⟩, by ext; rfl⟩)

theorem outerAction_ker_le_center (U : Subgroup G)
    (hC : centralizer (U : Set G) ≤ center G) :
    (outerAction U).ker ≤ center (Quotient U) := by
  intro x hx
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (normalizer (U : Set G))) x
  have hinner : U.normalizerMonoidHom n ∈ MulAut.innerSubgroup U :=
    (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨u, hu⟩ := hinner
  let c : normalizer (U : Set G) := n * (inclusion U.le_normalizer u)⁻¹
  have hc : (c : G) ∈ centralizer (U : Set G) := by
    have he : U.normalizerMonoidHom c = 1 := by
      change U.normalizerMonoidHom (n * (inclusion U.le_normalizer u)⁻¹) = 1
      rw [map_mul, map_inv, ← hu]
      have he : U.normalizerMonoidHom (inclusion U.le_normalizer u) = MulAut.conj u := by
        ext; rfl
      rw [he, mul_inv_cancel]
    have hk : c ∈ U.normalizerMonoidHom.ker := he
    rwa [normalizerMonoidHom_ker] at hk
  have hcN : c ∈ center (normalizer (U : Set G)) := by
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hC hc) y)
  let q := QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G)))
  have hqc : q c = q n := by
    change q (n * (inclusion U.le_normalizer u)⁻¹) = q n
    have huq : q (inclusion U.le_normalizer u) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr u.property
    rw [map_mul, map_inv, huq, inv_one, mul_one]
  rw [← hqc]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
  simpa only [map_mul] using congrArg q (mem_center_iff.mp hcN y)

theorem nilpotent_of_centralizer_le_center [Finite G] (U : Subgroup G)
    (hC : centralizer (U : Set G) ≤ center G)
    (ho : IsPGroup 2 (MulAut.Outer U)) : Group.IsNilpotent (Quotient U) := by
  let := ho.isNilpotent
  exact Subgroup.isNilpotent_of_ker_le_center (outerAction U)
    (outerAction_ker_le_center U hC)

def centralOuterMap (A : Type*) [Group A] : MulAut.Outer A →* MulAut.Outer (A ⧸ center A) :=
  QuotientGroup.lift (MulAut.innerSubgroup A)
    ((QuotientGroup.mk' (MulAut.innerSubgroup (A ⧸ center A))).comp
      (MulAut.centralQuotientAction (MulEquiv.refl _))) (by
      rintro a ⟨x, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨QuotientGroup.mk' (center A) x,
        (MulAut.centralQuotientAction_conj (MulEquiv.refl _) x).symm⟩)

theorem centralOuterMap_injective (A : Type*) [Group A] [Group.IsPerfect A] :
    Function.Injective (centralOuterMap A) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  have hinner : MulAut.centralQuotientAction (MulEquiv.refl _) a ∈
      MulAut.innerSubgroup (A ⧸ center A) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨b, hb⟩ := hinner
  obtain ⟨g, hg⟩ := (MulAut.centralQuotientAction_inner_iff (MulEquiv.refl _) a).mp
    ⟨b, hb.symm⟩
  exact (QuotientGroup.eq_one_iff _).mpr ⟨g, hg.symm⟩

theorem nilpotent_of_map {D : Type*} [Group D]
    (f : G →* D) (U : Subgroup G) (hk : f.ker ≤ U)
    (hn : Group.IsNilpotent (Quotient (U.map f))) : Group.IsNilpotent (Quotient U) := by
  let fN : normalizer (U : Set G) →* normalizer (U.map f : Set D) :=
    (f.comp (normalizer (U : Set G)).subtype).codRestrict _ (by
      intro x
      exact U.le_normalizer_map f (mem_map_of_mem f x.property))
  let q := QuotientGroup.mk' ((U.map f).subgroupOf (normalizer (U.map f : Set D)))
  let g : Quotient U →* Quotient (U.map f) := QuotientGroup.lift _ (q.comp fN) (by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact mem_map_of_mem f hx)
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hm' : fN n ∈ (U.map f).subgroupOf (normalizer (U.map f : Set D)) :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hm : f n.val ∈ U.map f := hm'
    have he := U.comap_map_eq_self hk
    have hnmem : n.val ∈ U := by
      exact he.le hm
    exact (QuotientGroup.eq_one_iff _).mpr hnmem
  let := hn
  exact Subgroup.isNilpotent_of_ker_le_center g
    (by rw [(MonoidHom.ker_eq_bot_iff g).mpr hg]; exact bot_le)


/-- A normal-subgroup quotient embeds in the normalizer quotient of its image. -/
theorem nilpotent_quotient_of_map
    {A D : Type*} [Group A] [Group D]
    (N : Subgroup A) [N.Normal] (f : A →* D) (hk : f.ker ≤ N)
    (hn : Group.IsNilpotent (NormalizerOuterQuotient.Quotient (N.map f))) :
    Group.IsNilpotent (A ⧸ N) := by
  let U := N.map f
  let fN : A →* normalizer (U : Set D) := f.codRestrict _ (by
    intro x
    exact N.le_normalizer_map f (mem_map_of_mem f
      (show x ∈ normalizer (N : Set A) by rw [normalizer_eq_top N]; trivial)))
  let q := QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set D)))
  let g : A ⧸ N →* NormalizerOuterQuotient.Quotient U :=
    QuotientGroup.lift N (q.comp fN) (by
      intro x hx
      apply (QuotientGroup.eq_one_iff _).mpr
      exact mem_map_of_mem f hx)
  have hg : Function.Injective g := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hm' : fN n ∈ U.subgroupOf (normalizer (U : Set D)) :=
      (QuotientGroup.eq_one_iff _).mp hx
    have hm : f n ∈ N.map f := hm'
    have hnmem : n ∈ N := (N.comap_map_eq_self hk).le hm
    exact (QuotientGroup.eq_one_iff _).mpr hnmem
  let := hn
  exact Subgroup.isNilpotent_of_ker_le_center g
    (by rw [(MonoidHom.ker_eq_bot_iff g).mpr hg]; exact bot_le)

end Subgroup.NormalizerOuterQuotient
