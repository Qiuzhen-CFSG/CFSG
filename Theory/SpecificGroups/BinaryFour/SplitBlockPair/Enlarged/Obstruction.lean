module
public import Theory.SpecificGroups.BinaryFour.SplitBlockPair.Enlarged.Parameterization
/-!
# Excluding the enlarged rotating-cubic action

The 24 coordinate changes preserve the marked point and conjugate the
parabolic cubic to itself or its inverse. The complete parameterization of
an oriented rotating cubic therefore transports one of the three checked
point-fixing words of order seven into the actual actor group. Inverting the
cubic covers the other orientation. This contradicts the source stabilizer
bound of 4608, without assuming that the central plane is trivial.

Source: Aschbacher–Smith, the split-block exclusion in 14.4.4, printed p.1007.
-/
namespace BinarySixSplitPair.Census
private def inverseIndex : Fin 24 → Fin 24 := ![0,1,2,3,4,5,6,7,8,9,10,11,16,17,18,19,12,13,14,15,20,21,22,23]
private theorem change_left : ∀ k : Fin 24, ∀ x : Fin 64,
    change (inverseIndex k) (change k x)=x := by decide +kernel
private theorem change_right : ∀ k : Fin 24, ∀ x : Fin 64,
    change k (change (inverseIndex k) x)=x := by decide +kernel
def changePerm (k : Fin 24) : Equiv.Perm (Fin 64) where
  toFun := change k
  invFun := change (inverseIndex k)
  left_inv := change_left k
  right_inv := change_right k

theorem change_point : ∀ k : Fin 24, changePerm k 2=2 := by decide +kernel

theorem change_cubic (k : Fin 24) :
    changePerm k * EnlargedSwappingTable.p * (changePerm k)⁻¹ = EnlargedSwappingTable.p ∨
    changePerm k * EnlargedSwappingTable.p * (changePerm k)⁻¹ = EnlargedSwappingTable.p⁻¹ := by
  have h : ∀ k : Fin 24,
      (∀ x, change k (EnlargedSwappingTable.p x)=EnlargedSwappingTable.p (change k x)) ∨
      (∀ x, change k (EnlargedSwappingTable.p x)=EnlargedSwappingTable.p⁻¹ (change k x)) := by
    decide +kernel
  rcases h k with h | h
  · exact Or.inl (mul_inv_eq_iff_eq_mul.mpr (Equiv.ext h))
  · exact Or.inr (mul_inv_eq_iff_eq_mul.mpr (Equiv.ext h))

end BinarySixSplitPair.Census
namespace BinarySixSplitPair
open Subgroup

private theorem rotating_inv (f : MulAut E) (hf : RotatingCubic f) : RotatingCubic f⁻¹ := by
  have moved (P : Subgroup E) (hP : P.map f.toMonoidHom ≠ P) :
      P.map f⁻¹.toMonoidHom ≠ P := by
    intro he
    apply hP
    have hh := congrArg (fun S : Subgroup E => S.map f.toMonoidHom) he
    rw [map_map,show f.toMonoidHom.comp f⁻¹.toMonoidHom = MonoidHom.id E from by
      apply MonoidHom.ext
      intro x
      exact f.apply_symm_apply x,map_id] at hh
    exact hh.symm
  refine ⟨?_,?_,(normalizer _).inv_mem hf.2.2.1,?_,
    moved _ hf.2.2.2.2.1,moved _ hf.2.2.2.2.2⟩
  · rw [inv_pow,hf.1,inv_one]
  · apply f.injective
    simpa only [MulAut.inv_apply,MulEquiv.apply_symm_apply] using hf.2.1.symm
  · intro hh
    apply hf.2.2.2.1
    simpa only [inv_inv] using (centralizer (overlap : Set (MulAut E))).inv_mem hh

private theorem inverse_orientation (f : MulAut E)
    (hr : f*r*f⁻¹=r*c) (hc : f*c*f⁻¹=r) :
    f⁻¹*r*(f⁻¹)⁻¹=c ∧ f⁻¹*c*(f⁻¹)⁻¹=r*c := by
  have hrc : f*(r*c)*f⁻¹=c := by
    calc
      _ = (f*r*f⁻¹)*(f*c*f⁻¹) := by group
      _ = (r*c)*r := by rw [hr,hc]
      _ = c := by
        change extend BinaryFourSplitPair.row * extend BinaryFourSplitPair.column *
          extend BinaryFourSplitPair.row = extend BinaryFourSplitPair.column
        rw [←map_mul,←map_mul,BinaryFourSplitPair.row_column_commute,mul_assoc,
          BinaryFourSplitPair.row_sq,mul_one]
  constructor
  · rw [inv_inv,←hc]
    group
  · calc
      _ = f⁻¹*(f*(r*c)*f⁻¹)*f := by rw [hrc,inv_inv]
      _ = r*c := by group

private theorem no_oriented (J : Subgroup (MulAut E)) (f : MulAut E)
    (hp : parabolic ≤ J) (hm : f ∈ J) (hf : RotatingCubic f)
    (hr : f*r*f⁻¹=c) (hc : f*c*f⁻¹=r*c)
    (hb : ∀ w ∈ J, w point=point → orderOf w ∣ 4608) : False := by
  obtain ⟨j,k,hk⟩ := oriented_census f hf hr hc
  let K := J.map permAction
  let d := Census.changePerm k
  let cD := MulAut.conj d
  let K' := K.map cD.toMonoidHom
  have hd : d 2=2 := Census.change_point k
  have hpK : EnlargedSwappingTable.p ∈ K := by
    rw [←EnlargedSwappingTable.parabolic_cubic_label]
    refine ⟨_,hp ?_,rfl⟩
    exact ⟨BinaryFourSplitPair.columnCubic,subset_closure (by simp),rfl⟩
  have hp' : EnlargedSwappingTable.p ∈ K' := by
    have hh : d*EnlargedSwappingTable.p*d⁻¹ ∈ K' := ⟨_,hpK,rfl⟩
    rcases Census.change_cubic k with he | he
    · exact he ▸ hh
    · have hhi := K'.inv_mem (he ▸ hh)
      simpa only [inv_inv] using hhi
  have hf' : Census.rep j ∈ K' := by
    have hh : d*permAction f*d⁻¹ ∈ K' := ⟨_,⟨_,hm,rfl⟩,rfl⟩
    have he : d*permAction f*d⁻¹=Census.rep j :=
      mul_inv_eq_iff_eq_mul.mpr (Equiv.ext hk)
    exact he ▸ hh
  have hbound : ∀ w ∈ K', w 2=2 → orderOf w ∣ 4608 := by
    rintro _ ⟨w,hw,rfl⟩ hfix
    change orderOf (cD w) ∣ 4608
    rw [cD.orderOf_eq]
    have hdi : d⁻¹ 2=2 := by
      apply d.injective
      change d (d.symm 2)=d 2
      rw [d.apply_symm_apply]
      exact hd.symm
    have hwfix : w 2=2 := by
      have hh : d (w (d⁻¹ 2))=2 := hfix
      rw [hdi] at hh
      exact d.injective (hh.trans hd.symm)
    obtain ⟨a,ha,rfl⟩ := hw
    rw [orderOf_injective permAction permAction_injective]
    apply hb a ha
    apply labels.injective
    rw [←permAction_apply,labels_point]
    exact hwfix
  obtain ⟨h1,h2,h3⟩ := EnlargedSwappingTable.no_representative K' hp' hbound
  fin_cases j
  · exact h1 hf'
  · exact h2 hf'
  · exact h3 hf'

/-- An enlarged rotating cubic is incompatible with the actual source
point-stabilizer order bound. Both orientations and all moving-factor
parameters are included. -/
public theorem no_rotating_cubic (J : Subgroup (MulAut E)) (f : MulAut E)
    (hp : parabolic ≤ J) (hm : f ∈ J) (hf : RotatingCubic f)
    (hb : ∀ w ∈ J, w point=point → orderOf w ∣ 4608) : False := by
  rcases rotating_cubic_orientation f hf with ⟨hr,hc⟩ | ⟨hr,hc⟩
  · exact no_oriented J f hp hm hf hr hc hb
  · obtain ⟨hr',hc'⟩ := inverse_orientation f hr hc
    exact no_oriented J f⁻¹ hp (J.inv_mem hm) (rotating_inv f hf) hr' hc' hb
end BinarySixSplitPair
