module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.UFixer
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Involutions


/-!
# The two reflection classes of the marked quaternion-core fixer

The tail-coordinate automorphisms fix the translation factor. For an elementary
abelian subgroup in the point centralizer outside that factor, involution
displacement puts every vector coordinate in the point hyperplane; hence the
actual diagonal transposition `beta` fixes this second factor. A tail times
`beta` has square one precisely when its two tail coordinates agree. Such a
tail fixes the whole point centralizer. Thus every involution in the canonical
dihedral fixer fixes one of these two actual factors pointwise.

Source: Aschbacher–Smith 14.3.22, printed p.998, the two reflection exclusions;
the displacement calculation is the natural A₆-module calculation in 14.3.21(3).
-/

public noncomputable section

open Subgroup SemidirectProduct
namespace BinaryPermutation.SixNaturalSplit
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing

private theorem vector_inv' (a : Vector) : a⁻¹=a := by
  apply inv_eq_of_mul_eq_one_right
  apply Multiplicative.toAdd.injective
  change a.toAdd+a.toAdd=0
  rw [←two_nsmul,←Nat.cast_smul_eq_nsmul (ZMod 2) 2]
  exact zero_smul (ZMod 2) _

/-- A nontranslation involution in the point centralizer has hyperplane vector part. -/
theorem involution_left_mem_hyperplane (x : Model) (hx : x^2=1)
    (hr : x.right≠1) (hp : x∈pointCentralizer) :
    x.left.toAdd∈PointAction.Hyperplane := by
  have hg2 : x.right^2=1 := congrArg SemidirectProduct.right hx
  have hgo : orderOf x.right=2 := orderOf_eq_prime hg2 hr
  have hv : x.left * action x.right x.left=1 := by
    simpa only [pow_two,mul_left,one_left] using congrArg SemidirectProduct.left hx
  have hf : action x.right x.left=x.left :=
    (eq_inv_of_mul_eq_one_right hv).trans (vector_inv' _)
  obtain ⟨b,hb⟩ := involution_fixed_displacement x.right hgo x.left hf
  apply (mem_hyperplane_iff _).mpr
  rw [←hb]
  change form (pairVector 4 5) (b.toAdd + naturalRepresentation (Fin 6) x.right.val b.toAdd)=0
  rw [map_add,point_functional_invariant x.right hp]
  exact CharTwo.add_self_eq_zero _

/-- The second reflection fixes each elementary abelian factor through the point
which is not contained in the translation factor. -/
theorem beta_fixes_elementary (B : Subgroup Model)
    (hp : B≤pointCentralizer) (hexp : ∀x∈B,x^2=1) (hout : ¬ B≤translations) :
    beta∈fixingSubgroup (MulAut Model) (B:Set Model) := by
  have hright (x : Model) (hx : x.right=1) : x∈translations := by
    refine ⟨x.left,?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact hx.symm
  obtain ⟨b,hb,hbout⟩ := Set.not_subset.mp hout
  have hbr : b.right≠1 := fun h=>hbout (hright b h)
  have hbv := involution_left_mem_hyperplane b (hexp b hb) hbr (hp hb)
  rw [mem_fixingSubgroup_iff]
  intro x hx
  have hxv : x.left.toAdd∈PointAction.Hyperplane := by
    by_cases hr : x.right=1
    · have hxr : (x*b).right≠1 := by simpa [hr] using hbr
      have hh := involution_left_mem_hyperplane (x*b) (hexp _ (B.mul_mem hx hb)) hxr
        (hp (B.mul_mem hx hb))
      have he : (x*b).left.toAdd=x.left.toAdd+b.left.toAdd := by
        simp [mul_left,hr]
      rw [he] at hh
      have := PointAction.Hyperplane.sub_mem hh hbv
      simpa only [add_sub_cancel_right] using this
    · exact involution_left_mem_hyperplane x (hexp x hx) hr (hp hx)
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    exact swap45_fixes_hyperplane x.left.toAdd hxv
  · apply Subtype.ext
    change swap45*x.right.val*swap45⁻¹=x.right.val
    have hc : x.right.val*swap45=swap45*x.right.val := by
      rcases mem_H1_cases (show x.right.val∈L1 from hp hx).1 with ⟨h4,h5⟩|⟨h4,h5⟩
      · simpa only [swap45,h4,h5] using Equiv.mul_swap_eq_swap_mul x.right.val 4 5
      · have hh := Equiv.mul_swap_eq_swap_mul x.right.val 4 5
        rw [h4,h5,Equiv.swap_comm 5 4] at hh
        exact hh
    rw [←hc,mul_inv_cancel_right]

/-- Equal tail coordinates fix the distinguished point centralizer pointwise. -/
theorem symmetric_tail_fixes_pointCentralizer (c : Multiplicative (Fin 2 → ZMod 2))
    (hc : c.toAdd 0=c.toAdd 1) :
    tailKernel c∈fixingSubgroup (MulAut Model) (pointCentralizer:Set Model) := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  change (kernelEquiv (Multiplicative.ofAdd (tailDeleted c.toAdd))).val x=x
  rw [kernelEquiv_apply]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change x.left.toAdd+(SixNaturalCocycles.deletedEquiv (tailDeleted c.toAdd)).val x.right=x.left.toAdd
    have he : representation (Fin 6) x.right.val (tailFull c.toAdd)=tailFull c.toAdd := by
      rcases mem_H1_cases (show x.right.val∈L1 from hx).1 with ⟨h4,h5⟩|⟨h4,h5⟩
      · ext i
        simp only [representation_apply,tailFull,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,Pi.single_apply]
        have h4i : x.right.val.symm i=4 ↔ i=4 := by rw [Equiv.symm_apply_eq,h4]
        have h5i : x.right.val.symm i=5 ↔ i=5 := by rw [Equiv.symm_apply_eq,h5]
        simp only [h4i,h5i]
      · ext i
        simp only [representation_apply,tailFull,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,Pi.single_apply]
        have h4i : x.right.val.symm i=4 ↔ i=5 := by rw [Equiv.symm_apply_eq,h4]
        have h5i : x.right.val.symm i=5 ↔ i=4 := by rw [Equiv.symm_apply_eq,h5]
        simp only [h4i,h5i,hc,add_comm]
    have hz : (SixNaturalCocycles.deletedEquiv (tailDeleted c.toAdd)).val x.right=0 := by
      rw [tailDeleted,LinearMap.comp_apply,SixNaturalCocycles.deletedEquiv_mk]
      apply Subtype.ext
      change (constants (Fin 6)).mkQ (representation (Fin 6) x.right.val (tailFull c.toAdd)-tailFull c.toAdd)=0
      rw [he,sub_self,map_zero]
    rw [hz,add_zero]
  · rfl

theorem tail_beta_square_one_iff (c : Multiplicative (Fin 2 → ZMod 2)) :
    (tailKernel c*beta)^2=1 ↔ c.toAdd 0=c.toAdd 1 := by
  have hb : beta*beta=1 := by simpa only [pow_two] using beta_square
  have hs : (tailKernel c*beta)^2=
      tailKernel (c*Multiplicative.ofAdd (fun i=>c.toAdd (Equiv.swap 0 1 i))) := by
    rw [pow_two,mul_assoc,←mul_assoc beta,beta_tailKernel]
    rw [mul_assoc _ beta beta,hb,mul_one,←map_mul]
  rw [hs,←tailKernel.map_one,tailKernel_injective.eq_iff]
  constructor
  · intro h
    have hh := congrFun (congrArg Multiplicative.toAdd h) 0
    change c.toAdd 0+c.toAdd 1=0 at hh
    simpa only [CharTwo.neg_eq] using add_eq_zero_iff_eq_neg.mp hh
  · intro h
    apply Multiplicative.toAdd.injective
    ext i
    fin_cases i <;> simp [Equiv.swap_apply_def,h,CharTwo.add_self_eq_zero]

/-- Both reflection classes, with their actual fixed elementary factors. -/
theorem canonicalFixer_square_one_fixes_factor
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range)
    (B : Subgroup Model) (hp : B≤pointCentralizer)
    (hexp : ∀x∈B,x^2=1) (hout : ¬ B≤translations)
    (a : MulAut Model) (ha : a∈canonicalFixer) (hs : a^2=1) :
    a∈fixingSubgroup (MulAut Model) (translations:Set Model) ∨
    a∈fixingSubgroup (MulAut Model) (B:Set Model) := by
  obtain ⟨c,rfl|rfl⟩ := canonicalFixer_decomposition hN a ha
  · left
    change (kernelEquiv (Multiplicative.ofAdd (tailDeleted c.toAdd))).val ∈ _
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨v,rfl⟩
    exact (kernelEquiv _).property v
  · right
    change (tailKernel c*beta)^2=1 at hs
    have ht := symmetric_tail_fixes_pointCentralizer c ((tail_beta_square_one_iff c).mp hs)
    have hb := beta_fixes_elementary B hp hexp hout
    apply (fixingSubgroup (MulAut Model) (B:Set Model)).mul_mem _ hb
    rw [mem_fixingSubgroup_iff] at ht ⊢
    exact fun x hx=>ht x (hp hx)

end BinaryPermutation.SixNaturalSplit
