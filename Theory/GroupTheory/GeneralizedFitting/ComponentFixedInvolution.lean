module
public import Theory.GroupTheory.GeneralizedFitting.NormalCentralizerResidual
public import Theory.GroupAction.SubgroupCentralizerCongruence

/-!
# Fixed core involutions and centralizer residuals

A two-subgroup normalizing a nontrivial two-core fixes an involution in it.
Every ordinary component centralizes this involution. Separately, an
injectively embedded element-centralizer residual is normalized by the
intersection of the image normalizer and the element centralizer. The
proof transports the characteristic solvable residual through the literal
centralizer isomorphism.

These give the fixed involution and simultaneous-centralizer normality
used in Aschbacher--Smith 4.2.13, printed p.612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative

namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem component_core_involution_fixed_by_twoSubgroup
    (H : Subgroup G) (hne : H.pCoreIn 2 ≠ ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (S : Subgroup G) (hS : IsPGroup 2 S) (hSH : S ≤ H) :
    ∃ r : H.pCoreIn 2, orderOf r = 2 ∧
      K.map H.subtype ≤ centralizer ({(r : G)} : Set G) ∧
      S ≤ centralizer ({(r : G)} : Set G) := by
  let Q := H.pCoreIn 2
  let : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hne
  have hd : 2 ∣ Nat.card Q :=
    (isPGroup_pCoreIn 2 H).card_eq_or_dvd.resolve_left Finite.one_lt_card.ne'
  have hn : S ≤ normalizer (Q : Set G) := hSH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hcong := card_modEq_card_inf_centralizer S Q hS hn
  have hdf : 2 ∣ Nat.card (Q ⊓ centralizer (S : Set G) : Subgroup G) :=
    Nat.modEq_zero_iff_dvd.mp (hcong.symm.trans hd.modEq_zero_nat)
  obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' 2 hdf
  let rQ : Q := ⟨r,r.property.1⟩
  have hrG : orderOf (r : G) = 2 := (orderOf_coe r).trans hr
  refine ⟨rQ,(orderOf_coe rQ).symm.trans hrG,?_,?_⟩
  · let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    have hc := hK.le_centralizer_of_solvable_normal (pCore 2 H)
    obtain ⟨q,hq,hqr⟩ := rQ.property
    rintro k ⟨k,hk,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←hqr]
    exact (congrArg H.subtype (hc hk q hq)).symm
  · intro s hs
    exact mem_centralizer_singleton_iff.mpr (r.property.2 s hs)

end Theory.GroupTheory

namespace Theory.GroupTheory
open Subgroup
variable {G K : Type*} [Group G] [Group K] [Finite K]

theorem centralizer_residual_image_normalized
    (f : K →* G) (hf : Function.Injective f) (x : K) :
    normalizer (f.range : Set G) ⊓ centralizer ({f x} : Set G) ≤
      normalizer (((solvableResidual (centralizer ({x} : Set K))).map
        (f.comp (centralizer ({x} : Set K)).subtype)) : Set G) := by
  let D := centralizer ({x} : Set K)
  let C := f.range ⊓ centralizer ({f x} : Set G)
  let g := f.comp D.subtype
  have hg : Function.Injective g := hf.comp D.subtype_injective
  have hr : g.range = C := by
    ext y
    constructor
    · rintro ⟨d,rfl⟩
      refine ⟨⟨d,rfl⟩,mem_centralizer_singleton_iff.mpr ?_⟩
      exact (map_mul f (d : K) x).symm.trans ((congrArg f
        (mem_centralizer_singleton_iff.mp d.property)).trans (map_mul f x (d : K)))
    · rintro ⟨⟨k,rfl⟩,hk⟩
      refine ⟨⟨k,mem_centralizer_singleton_iff.mpr (hf ?_)⟩,rfl⟩
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hk
  let e : D ≃* C := (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hr)
  have he : (solvableResidual D).map g = (solvableResidual C).map C.subtype := by
    rw [←map_solvableResidual_eq e.toMonoidHom e.surjective,map_map]
    rfl
  have hn : normalizer (f.range : Set G) ⊓ centralizer ({f x} : Set G) ≤
      normalizer (C : Set G) := by
    apply le_normalizer_iff.mpr
    intro a ha y hy
    exact ⟨(mem_normalizer_iff.mp ha.1 y).mp hy.1,
      (centralizer ({f x} : Set G)).mul_mem
        ((centralizer ({f x} : Set G)).mul_mem ha.2 hy.2)
        ((centralizer ({f x} : Set G)).inv_mem ha.2)⟩
  change _ ≤ normalizer ((solvableResidual D).map g : Set G)
  rw [he]
  exact hn.trans (normalizer_le_normalizer_characteristic_image C (solvableResidual C))

end Theory.GroupTheory
