module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.KernelParabolic
public import Theory.Mathieu.M24.ChapterHStabilizers.Involutions

/-!
# Marked symmetric-four transport through an actual native embedding

An order3072 embedded group centralizing its marked involution contains a
full native Sylow group. The involution is therefore native2A. The original
extraspecial128 subgroup with that center is the native kernel, so restriction
of the native quotient gives a surjection onto S4 with exactly that subgroup
as kernel. Normality of the candidate is a conclusion of this construction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
variable {H : Type*} [Group H] [Finite H]

/-- Retain the original subgroup as the full kernel of the S4 quotient. -/
theorem embedded_symmetricFour_quotient (f : H→*M24) (hf : Function.Injective f)
    (hH : Nat.card H=3072) (P : Subgroup H) [IsExtraspecial 2 P]
    (hP : Nat.card P=128) (z : H) (hz : orderOf z=2) (hzc : z∈center H)
    (hZP : (center P).map P.subtype=zpowers z) :
    ∃ q : H→*Equiv.Perm (Fin 4), Function.Surjective q ∧ q.ker=P := by
  let Z := zpowers z
  have hZc : Z≤center H := zpowers_le.mpr hzc
  let : Z.Normal := ⟨fun n hn g => by
    rw [mem_center_iff.mp (hZc hn) g,mul_inv_cancel_right]
    exact hn⟩
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by
    rw [show Z=zpowers z from rfl,Nat.card_zpowers,hz]; rfl)
  let R : Sylow 2 H := Classical.choice inferInstance
  have hzR : z∈R := hZtwo.le_sylow_of_normal R (mem_zpowers z)
  let S₀ := (R : Subgroup H).map f
  have hSc : Nat.card S₀=1024 := by
    rw [card_map_of_injective hf,R.card_eq_multiplicity,hH]
    decide +kernel
  let S : Sylow 2 M24 := Sylow.ofCard S₀ (by rw [hSc,m24_order]; decide +kernel)
  have hzf : IsSylowCentralInvolution (f z) := by
    refine ⟨(orderOf_injective f hf z).trans hz,S,mem_map_of_mem f hzR,?_⟩
    rintro y ⟨x,_,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←map_mul,←map_mul]
    exact congrArg f (mem_center_iff.mp hzc x)
  obtain ⟨g,hg⟩ := isConj_iff.mp (M24ChapterHStabilizers.sylowCentral_class2A hzf).symm
  let c := MulAut.conj g
  let f' := c.toMonoidHom.comp f
  have hf' : Function.Injective f' := c.injective.comp hf
  have hz' : f' z=involution2A := hg
  have hc (x : H) : f' x∈centralizer2A := by
    apply mem_centralizer_singleton_iff.mpr
    rw [←hz',←map_mul,←map_mul]
    exact congrArg f' (mem_center_iff.mp hzc x)
  let j := f'.codRestrict centralizer2A hc
  have hj : Function.Injective j := fun x y he => hf' (congrArg Subtype.val he)
  let A := P.map j
  let eP := P.equivMapOfInjective j hj
  let : IsExtraspecial 2 A := IsExtraspecial.of_mulEquiv eP inferInstance
  have hAc : Nat.card A=128 := (Nat.card_congr eP.symm.toEquiv).trans hP
  have hAz : (center A).map A.subtype=zpowers
      (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
    rw [show A=P.map j from rfl,←map_embeddedCenter P j hj,hZP,MonoidHom.map_zpowers]
    apply congrArg zpowers
    exact Subtype.ext hz'
  have hAK : A=kernel := KernelComparison.extraspecial_eq_kernel A hAc hAz
  have hKJ : kernel≤j.range := hAK ▸ map_le_range j P
  have hJc : Nat.card j.range=3072 :=
    (Nat.card_congr (MonoidHom.ofInjective hj).symm.toEquiv).trans hH
  obtain ⟨q,hq,hqker⟩ := parabolic_symmetricFour_quotient j.range hKJ hJc
  let r := q.comp j.rangeRestrict
  refine ⟨r,hq.comp j.rangeRestrict_surjective,?_⟩
  ext x
  change q (j.rangeRestrict x)=1 ↔ x∈P
  change j.rangeRestrict x∈q.ker ↔ x∈P
  rw [hqker]
  change j x∈kernel ↔ x∈P
  rw [←hAK]
  exact mem_map_iff_mem hj

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
