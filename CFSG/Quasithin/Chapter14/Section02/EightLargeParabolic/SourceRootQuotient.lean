module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootLiftConjugacy
public import Theory.SpecificGroups.SL2.SylowConsequences

/-!
# The original common Sylow preserves the marked quotient root

The full original Sylow maps to a two-subgroup of the prescribed SL2(8)
quotient, hence to an abelian unipotent group. Conjugation by this same
original Sylow therefore fixes every root image contained in it. This
retains the literal quotient map used for the changed six-path roots.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootQuotient

private theorem binary_linear_two_image_commutative {E : Type*} [Group E]
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (f : E →* SL(2,k)) (hf : Function.Injective f) (hp : IsPGroup 2 E) :
    IsMulCommutative E := by
  obtain ⟨U,hU⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let j : E →* U := f.codRestrict U (fun x => hU ⟨x,rfl⟩)
  let q := (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.toMonoidHom.comp j
  have hq : Function.Injective q :=
    (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 U).symm.injective.comp
      (fun _ _ he => hf (congrArg Subtype.val he))
  exact isMulCommutative_iff.mpr fun x y => hq (by rw [map_mul,map_mul,mul_comm])

private theorem map_conjugate_eq_of_commutative_image {E Q : Type*} [Group E] [Group Q]
    (q : E →* Q) (U R : Subgroup E) [IsMulCommutative (U.map q)]
    (hR : R≤U) (u:E) (hu:u∈U) :
    (R.map (MulAut.conj u).toMonoidHom).map q=R.map q := by
  have he (r:E) (hr:r∈R) : q ((MulAut.conj u) r)=q r := by
    have hc : q u*q r=q r*q u := congrArg Subtype.val
      (mul_comm (⟨q u,mem_map_of_mem q hu⟩:U.map q)
        (⟨q r,mem_map_of_mem q (hR hr)⟩:U.map q))
    change q (u*r*u⁻¹)=q r
    rw [map_mul,map_mul,map_inv,hc,mul_inv_cancel_right]
  ext x
  constructor
  · rintro ⟨y,⟨r,hr,rfl⟩,rfl⟩
    exact ⟨r,hr,(he r hr).symm⟩
  · rintro ⟨r,hr,rfl⟩
    exact ⟨(MulAut.conj u) r,mem_map_of_mem _ hr,he r hr⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR

/-- The same original Sylow acts trivially on its literal full-core quotient
image, so all of its conjugations preserve every contained root image. -/
theorem source_sylow_root_quotient :
    IsMulCommutative (((T:Subgroup G).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ∧
    ∀ (R : Subgroup H), R≤(T:Subgroup G).subgroupOf H →
      ∀ u:H, (u:G)∈T →
        (R.map (MulAut.conj u).toMonoidHom).map (QuotientGroup.mk' (pCore 2 H))=
          R.map (QuotientGroup.mk' (pCore 2 H)) := by
  let U := (T:Subgroup G).subgroupOf H
  let π := QuotientGroup.mk' (pCore 2 H)
  let ε := (sourceFirstCoreQuotientEquiv hG T hempty hM hu hmany hcard e H hH eR).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 3)).symm
  let f := ε.toMonoidHom.comp (U.map π).subtype
  let hcomm : IsMulCommutative (U.map π) :=
    binary_linear_two_image_commutative f (ε.injective.comp (U.map π).subtype_injective)
      (T.isPGroup'.comap_subtype.map π)
  exact ⟨hcomm,fun R hR u hu => map_conjugate_eq_of_commutative_image π U R hR u hu⟩

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootQuotient
