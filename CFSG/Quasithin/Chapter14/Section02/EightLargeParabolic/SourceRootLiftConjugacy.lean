module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootCartanComplement

/-!
# Conjugacy of the original root lifts with the same quotient line

The original degree-eight core module places a prescribed seven-normalized
root in a complement conjugated by the seven-fixed part of the full core.
The quotient is faithful on that complement. Consequently equality of the
prescribed quotient root images gives equality of the literal root lifts
through the same core conjugator.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootLiftConjugacy

private theorem root_eq_conjugate_of_same_image {E Q : Type*} [Group E] [Group Q]
    (q : E →* Q) (K R S : Subgroup E) (hK : Disjoint K q.ker)
    (hR : R≤K) (v : E) (hv : v∈q.ker)
    (hS : S≤K.map (MulAut.conj v).toMonoidHom) (he : S.map q=R.map q) :
    S=R.map (MulAut.conj v).toMonoidHom := by
  let f := (MulAut.conj v).toMonoidHom
  have hq (x:E) : q (f x)=q x := by
    change q (v*x*v⁻¹)=q x
    rw [map_mul,map_mul,map_inv,show q v=1 from hv,one_mul,inv_one,mul_one]
  have hdis : Disjoint (K.map f) q.ker := by
    apply disjoint_def.mpr
    rintro _ ⟨x,hx,rfl⟩ hqx
    have hxq : x∈q.ker := (hq x).symm.trans hqx
    rw [hK.le_bot ⟨hx,hxq⟩,map_one]
  have hinj : ∀ {x y:E},x∈K.map f → y∈K.map f → q x=q y → x=y := by
    intro x y hx hy hxy
    have hdiv : x/y∈K.map f⊓q.ker :=
      ⟨(K.map f).div_mem hx hy,by change q (x/y)=1;rw [map_div,hxy,div_self']⟩
    exact div_eq_one.mp (hdis.le_bot hdiv)
  have hrmap : (R.map f).map q=R.map q := by
    rw [Subgroup.map_map]
    have hf : q.comp f=q := by ext x;exact hq x
    rw [hf]
  have him : S.map q=(R.map f).map q := he.trans hrmap.symm
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := him ▸ mem_map_of_mem q hx
    exact (hinj ((map_mono hR) hy) (hS hx) hxy) ▸ hy
  · intro x hx
    obtain ⟨y,hy,hxy⟩ := him.symm ▸ mem_map_of_mem q hx
    exact (hinj (hS hy) ((map_mono hR) hx) hxy) ▸ hy

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

/-- Actual seven-normalized eight-roots with the same original quotient image
are conjugate by an element of the full original core fixing that seven-group. -/
theorem source_same_image_root_conjugacy
    (K : Subgroup H) (hK : (pCore 2 H).IsComplement' K)
    (A R S : Subgroup H) (hAK : A≤K) (hA7 : Nat.card A=7) (hRK : R≤K)
    (hS : IsPGroup 2 S) (hS8 : Nat.card S=8)
    (hkS : Disjoint S (pCore 2 H)) (hAS : A≤normalizer (S:Set H))
    (he : S.map (QuotientGroup.mk' (pCore 2 H))=R.map (QuotientGroup.mk' (pCore 2 H))) :
    ∃ v∈pCore 2 H⊓centralizer (A:Set H), S=R.map (MulAut.conj v).toMonoidHom := by
  obtain ⟨v,hv,hSv⟩ := SourceRootCartanComplement.source_seven_root_conjugator
    hG T hempty hM hu hmany hcard e H hH eR K hK A S hAK hA7 hS hS8 hkS hAS
  refine ⟨v,hv,root_eq_conjugate_of_same_image (QuotientGroup.mk' (pCore 2 H)) K R S ?_ hRK v ?_ hSv he⟩
  · rw [QuotientGroup.ker_mk']
    exact hK.disjoint.symm
  · exact (QuotientGroup.eq_one_iff v).mpr hv.1

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceRootLiftConjugacy
