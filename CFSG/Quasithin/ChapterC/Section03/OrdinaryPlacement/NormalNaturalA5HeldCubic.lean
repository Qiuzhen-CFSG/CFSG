module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.CoreKernel.KernelUpperBound.CheckSupport
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# The native Held cubic acts without fixed points on its actual two-core

The cubic word in the kernel of the six-point action has zero norm on
each of the seven published core generators. Their pairwise commutativity
extends the norm identity to the entire literal core. A fixed element then
has cube one in a two-group, hence is the identity. The checks use the
previously proved faithful four-point action, not an assumed module shape.

This is a native ingredient for the ordinary Held inspection in12.7.5,
printed p.840, and C.3.5, printed p.150. The ATLAS Held words and tables
retain their attribution in Theory/SpecificGroups/Held and LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldCubic
open Held Held.TwoLocalCandidates Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel.KernelUpperBound

private theorem core_commutative (i : Bool) : IsMulCommutative (wordCore i) := by
  have hh (r : Fin 3) (hr : r ≠ 2) : IsMulCommutative (Cores.core r) := by
    apply isMulCommutative_closure
    rintro _ ⟨j,rfl⟩ _ ⟨k,rfl⟩
    have hc (j k : Fin 7) (hjk : j < k) :
        Cores.coreGenerator r k * Cores.coreGenerator r j =
          Cores.coreGenerator r j * Cores.coreGenerator r k := by
      have he := Cores.internalConjugation r k j hjk
      simp only [Cores.commutatorBit,beq_eq_false_iff_ne.mpr hr,Bool.false_and,
        Bool.false_eq_true,ite_false,pow_zero,one_mul] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · exact (hc j k hjk).symm
    · rfl
    · exact hc k j hkj
  cases i
  · exact hh 0 (by decide)
  · exact hh 1 (by decide)

private theorem generator_norm (i : Bool) (k : Fin 7) :
    coreGenerator i k *
      (kernelThird i * coreGenerator i k * (kernelThird i)⁻¹) *
      ((kernelThird i)^2 * coreGenerator i k * ((kernelThird i)^2)⁻¹) = 1 := by
  apply Subtype.ext
  apply Held.eq_of_four_point_images
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,Subgroup.coe_pow,map_mul,map_inv,map_pow,
    representation_coreGenerator,representation_third,Subgroup.coe_one,map_one]
  cases i <;> fin_cases k <;> decide +kernel

/-- The literal cubic kernel word fixes no nonidentity element of either
native max3/max4 two-core. -/
theorem fixed_eq_one (i : Bool) (x : localOvergroup i)
    (hx : x ∈ pCore 2 (localOvergroup i)) (hc : Commute x (kernelThird i)) : x = 1 := by
  let W := wordCore i
  let : W.Normal := wordCore_normal i
  let : IsMulCommutative W := core_commutative i
  let a : MulAut W := MulAut.conjNormal (kernelThird i)
  let n : W →* W := MonoidHom.id W * a.toMonoidHom * (a.toMonoidHom.comp a.toMonoidHom)
  have hgen (k : Fin 7) : (⟨coreGenerator i k,coreGenerator_mem i k⟩ : W) ∈ n.ker := by
    apply Subtype.ext
    change coreGenerator i k *
      (kernelThird i * coreGenerator i k * (kernelThird i)⁻¹) *
      (kernelThird i * (kernelThird i * coreGenerator i k * (kernelThird i)⁻¹) *
        (kernelThird i)⁻¹) = 1
    convert generator_norm i k using 1
    group
  have hall : W ≤ n.ker.map W.subtype := by
    apply (show W = closure (Set.range (coreGenerator i)) from wordCore_eq_closure i).le.trans
    apply (closure_le _).mpr
    rintro _ ⟨k,rfl⟩
    exact ⟨⟨coreGenerator i k,coreGenerator_mem i k⟩,hgen k,rfl⟩
  have hxW : x ∈ W := (wordCore_eq_pCore i).ge hx
  let y : W := ⟨x,hxW⟩
  have hn : n y = 1 := by
    exact (mem_map_iff_mem W.subtype_injective).mp (hall hxW)
  have ha : a y = y := by
    apply Subtype.ext
    change kernelThird i * x * (kernelThird i)⁻¹ = x
    rw [←hc.eq,mul_inv_cancel_right]
  have hy : y ^ 3 = 1 := by
    change y * a y * a (a y) = 1 at hn
    simpa only [ha,pow_succ,pow_zero,one_mul] using hn
  have he : y = 1 := (wordCore_isPGroup i).powEquiv (n := 3) (by decide) |>.injective
    (by simpa only [IsPGroup.powEquiv_apply,one_pow] using hy)
  exact congrArg Subtype.val he

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldCubic
