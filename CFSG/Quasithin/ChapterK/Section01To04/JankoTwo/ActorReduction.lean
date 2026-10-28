module

public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.AmbientActors
public import CFSG.Quasithin.ChapterK.Section01To04.JankoTwo.CarrierActors

/-!
# Classification of small actors on the marked J₂ module

The actual involution fusion supplies the minimum displacement bound. An
outer actor meets the marked inner subgroup nontrivially; the semilinear
fixed-space estimate then contradicts its rank-three bound. Transporting an
inner actor through the literal carrier equivalence permits the root-fixer
rank-two exclusion and the noncentral-centralizer calculation. Every actor
with fixed codimension at most twice its rank consequently has rank four,
codimension eight, and a nonquadratic action.

Only the genuine module marking and the universal B.4.6 root facts remain
inputs; no actor placement, dimension conclusion, or ratio is assumed.
Source: Aschbacher–Smith, K.4.5, printed p.460 / PDF p.471.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open Sporadic.LeechRelated.J2
namespace CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
open NaturalLocalAction
variable {K G V : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
  [FiniteDimensional (ZMod 2) K] [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (D : MarkedModule (K := K) ρ)
include D

omit [FiniteDimensional (ZMod 2) K] [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem source_carrier_fixedCodim (A : Subgroup Carrier) :
    fixedCodim D.carrierAction A = fixedCodim ρ (A.map D.carrierMap) := by
  unfold fixedCodim
  rw [fixedSpace_comp_map]

omit [FiniteDimensional (ZMod 2) K] [Finite G] in
private theorem inner_involution_displacement
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (x : D.inner) (hx : orderOf x = 2) :
    4 ≤ fixedCodim (naturalAction K) (zpowers (D.embedding x)) := by
  have hc := D.carrier_involution_displacement h hV (D.carrierEquiv x)
    ((orderOf_injective D.carrierEquiv.toMonoidHom D.carrierEquiv.injective x).trans hx)
  rw [D.source_carrier_fixedCodim, MonoidHom.map_zpowers] at hc
  have he : D.carrierMap (D.carrierEquiv x) = (x : G) := by
    simp [carrierMap]
  rwa [he,D.inner_fixedCodim] at hc

omit [Finite G] in
/-- The involution displacement lower bound follows from the two actual inner
fusion classes and the compatible outer field action. -/
theorem moduleM_ge_four_of_B46
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K) :
    4 ≤ ChapterE.moduleM ρ := by
  apply le_csInf ⟨_, Set.mem_insert (Module.finrank (ZMod 2) V) _⟩
  rintro n (rfl | ⟨i,hi,rfl⟩)
  · rw [D.finrank]
    decide
  · by_cases hm : i ∈ D.inner
    · let x : D.inner := ⟨i,hm⟩
      have hx : orderOf x = 2 :=
        (orderOf_injective _ D.inner.subtype_injective x).symm.trans hi
      have hd := D.inner_involution_displacement h hV x hx
      rwa [← D.inner_fixedCodim] at hd
    · rw [(D.outer_dimensions i hm hi).1]
      decide

/-- Outer actors cannot satisfy the source small-ratio inequality. The inner
involution is obtained from the proved index bound, rather than assumed. -/
theorem small_actor_le_inner
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hs : fixedCodim ρ A ≤ 2 * rank A) : A ≤ D.inner := by
  have hm := D.moduleM_ge_four_of_B46 h hV
  have hr : 1 < rank A := ChapterK.one_lt_rank_of_small_ratio ρ hA (by omega) hs
  let := hA.2
  intro i hi
  by_contra ho
  obtain ⟨x,hx,hne⟩ := D.exists_nontrivial_inner A hr
  have hxne : (x : G) ≠ 1 := fun he => hne (Subtype.ext he)
  have hx2 : orderOf x = 2 :=
    (orderOf_injective _ D.inner.subtype_injective x).symm.trans
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (x : G) hx) hxne)
  have hi2 : orderOf i = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian i hi)
    (fun he => ho (he ▸ D.inner.one_mem))
  have he := D.outer_actor_exclusion A (D.outer_actor_rank A hA i hi ho)
    i ho hi2 hi x hx (D.inner_involution_displacement h hV x hx2)
  omega

omit [FiniteDimensional (ZMod 2) K] [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem exists_carrier_actor (A : Subgroup G) (hA : IsElementaryTwo A)
    (hAi : A ≤ D.inner) :
    ∃ B : Subgroup Carrier, IsElementaryTwo B ∧ B.map D.carrierMap = A := by
  let := hA.2
  let B := (A.subgroupOf D.inner).map D.carrierEquiv.toMonoidHom
  have hmap : B.map D.carrierMap = A := by
    rw [show B = (A.subgroupOf D.inner).map D.carrierEquiv.toMonoidHom from rfl,
      map_map]
    have he : D.carrierMap.comp D.carrierEquiv.toMonoidHom = D.inner.subtype := by
      ext x
      simp [carrierMap]
    rw [he,map_subgroupOf_eq_of_le hAi]
  have : IsElementaryAbelian 2 (A.subgroupOf D.inner) :=
    IsElementaryAbelian.subgroupOf hAi
  refine ⟨B,⟨?_,IsElementaryAbelian.map _⟩,hmap⟩
  intro hb
  apply hA.1
  rw [← hmap,hb,Subgroup.map_bot]

/-- Every elementary actor satisfying (**) in K.4.5 has rank four,
codimension eight, and a nonquadratic action. Cubicity is not assumed. -/
theorem small_actor_calculation
    (h : InvolutionImages.B46RootFacts K) (hV : B46LongRootModuleFacts K)
    (A : Subgroup G) (hA : IsElementaryTwo A)
    (hs : fixedCodim ρ A ≤ 2 * rank A) :
    A ≤ D.inner ∧ rank A = 4 ∧ fixedCodim ρ A = 8 ∧ ¬ IsQuadratic ρ A := by
  have hAi := D.small_actor_le_inner h hV A hA hs
  obtain ⟨B,hB,hmap⟩ := D.exists_carrier_actor A hA hAi
  have hr : rank B = rank A := by rw [← hmap,rank_map_injective _ D.carrierMap_injective]
  have hd : fixedCodim D.carrierAction B = fixedCodim ρ A := by
    rw [D.source_carrier_fixedCodim,hmap]
  have hm := D.moduleM_ge_four_of_B46 h hV
  have hr1 : 1 < rank B := by
    rw [hr]
    exact ChapterK.one_lt_rank_of_small_ratio ρ hA (by omega) hs
  have hr3 : 3 ≤ rank B := by
    by_contra! hn
    have hr2 : rank B = 2 := by omega
    have he := D.carrier_small_rank_two_impossible h hV B hB hr2
    rw [hr,hd] at he
    omega
  obtain ⟨hbound,hcodim,hquad⟩ := D.carrier_large_actor_calculation h B hB hr3
  rw [hr] at hbound
  rw [hd] at hcodim
  refine ⟨hAi,by omega,hcodim,?_⟩
  intro hq
  apply hquad
  intro x hx y hy v
  exact hq _ (hmap ▸ mem_map_of_mem _ hx) _ (hmap ▸ mem_map_of_mem _ hy) v
end CFSG.Quasithin.ChapterK.JankoTwo.MarkedModule
