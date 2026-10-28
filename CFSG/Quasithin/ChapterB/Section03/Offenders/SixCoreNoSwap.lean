module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePoint
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Stellmacher.CentralizerQuotientRepresentation
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Augmentation point radicals without transpositions

Every offender in the image of a maximal elementary subgroup contains
a best offender. After the even point-orbit transport, the six-letter
classification puts a transposition in that best offender. Hence a point
radical whose image has no transposition has its entire elementary Thompson
subgroup in the module centralizer. The kernel may contain odd elements;
only normality is used to bound the image of the point radical.

The Chapter 13 covered augmentation comparison applies this to the literal
five-dimensional chosen module and the actual L₁T radical.
Source: Aschbacher–Smith B.2.3, B.3.4 and 13.2.2(8), printed pp.75,84–85,877.
-/

public noncomputable section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

private theorem core_best_contains_swap {A : Subgroup S}
    (hA : A ≤ ChapterC.NaturalSixControl.Model.E)
    (hb : IsBestOffender rho A) : pairSwap 6 2 ∈ A := by
  apply ChapterC.NaturalSixControl.Model.best_contains_swap hA
  rw [Six.isBestOffender_natural_iff,←Six.isBestOffender_core_iff]
  exact hb

/-- With no transposition in the point radical image, every maximal elementary
subgroup centralizes the original augmentation module. The action kernel may
have odd order. -/
theorem pointRadical_thompson_centralizes_of_no_swap
    {H : Type*} [Group H] [Finite H]
    (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (q : H →* S) (e : V ≃* Multiplicative W)
    (he : ∀ g v, (e (MulAut.conjNormal g v)).toAdd = rho (q g) (e v).toAdd)
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (z : V)
    (hz : ¬ ∀ a : alternatingGroup (Fin 6), alternatingCoreRepresentation (Fin 6) a (e z).toAdd = (e z).toAdd)
    (hs : ∀ x ∈ (centralizer ({z.val} : Set H)).pCoreIn 2, ¬ (q x).IsSwap) :
    elementaryAbelianMaxJ ((centralizer ({z.val} : Set H)).pCoreIn 2) ≤
      centralizer (V : Set H) := by
  let C := centralizer ({z.val} : Set H)
  let R := C.pCoreIn 2
  have hVR : V ≤ R := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (by
      intro v hv
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mul_comm (⟨v,hv⟩ : V) ⟨z.val,z.property⟩))
    le_normalizer_of_normal
  have hRim : R.map q ≤ (BinaryPermutation.SixCorePoint.stabilizer (e z).toAdd ⊓ q.range).pCoreIn 2 := by
    rw [←point_image V q e he z]
    exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 C).map q)
      (map_mono (pCoreIn_le 2 C))
      ((map_mono (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))).trans
          (R.le_normalizer_map q))
  obtain ⟨a,ha⟩ := BinaryPermutation.SixCorePoint.exists_point_core_bound q.range hY (e z).toAdd hz
  have hk := kernel_centralizer V q e he
  let qr := q.rangeRestrict
  have hkr : qr.ker = centralizer (V : Set H) := q.ker_rangeRestrict.trans hk
  let r := Representation.NormalElementaryQuotient.representation V qr q.rangeRestrict_surjective hkr
  let ec : Additive V ≃+ W := e.toAdditive.trans (AddEquiv.additiveMultiplicative _)
  let f : Additive V ≃ₗ[ZMod 2] W := { ec with map_smul' := ZMod.map_smul ec }
  have hf (g : q.range) (v : Additive V) : f (r g v) = rho g.val (f v) := by
    obtain ⟨g,rfl⟩ := q.rangeRestrict_surjective g
    have hr := Representation.NormalElementaryQuotient.representation_apply V qr
      q.rangeRestrict_surjective hkr g v
    have hh : (r (qr g) v).toMul = MulAut.conjNormal g v.toMul := Subtype.ext hr
    change (e ((r (qr g) v).toMul)).toAdd = _
    rw [hh]
    exact he g v.toMul
  apply sSup_le
  intro A hA
  by_contra hn
  have hoff := Representation.NormalElementaryQuotient.maxElementary_isOffender V qr
    q.rangeRestrict_surjective hkr R A hVR hA (by rwa [hkr])
  have ht := hoff.map_equivariant r rho q.range.subtype q.range.subtype_injective f hf
  have ht' : IsOffender rho (A.map q) := by
    rw [map_map] at ht
    exact ht
  have hc : IsOffender rho ((A.map q).map (MulAut.conj a.val⁻¹).toMonoidHom) :=
    ⟨ht'.1.map_conj _,by rw [fixedCodim_map_conj,rank_map_conj]; exact ht'.2⟩
  obtain ⟨B,hBA,hB⟩ := hc.exists_bestOffender _
  have hbound : (A.map q).map (MulAut.conj a.val⁻¹).toMonoidHom ≤ pointCore := by
    rintro _ ⟨b,hb,rfl⟩
    obtain ⟨c,hc,hcb⟩ := ha (hRim ((map_mono hA.1) hb))
    change a.val⁻¹ * b * (a.val⁻¹)⁻¹ ∈ pointCore
    rw [←hcb]
    change c ∈ pointCore at hc
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
      inv_mul_cancel_left,inv_mul_cancel,mul_one] using hc
  have hE : B ≤ ChapterC.NaturalSixControl.Model.E := by
    rw [←ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional]
    exact hBA.trans hbound
  obtain ⟨b,hb,heq⟩ := hBA (core_best_contains_swap hE hB)
  obtain ⟨x,hx,rfl⟩ := hb
  apply hs x (hA.1 hx)
  have heq' : q x = a.val * pairSwap 6 2 * a.val⁻¹ := by
    have hh := congrArg (fun t : S => a.val*t*a.val⁻¹) heq
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
      mul_inv_cancel_left,mul_inv_cancel,mul_one] using hh
  rw [heq']
  have hh : a.val * pairSwap 6 2 * a.val⁻¹ = Equiv.swap (a.val 4) (a.val 5) := by
    change a.val * Equiv.swap 4 5 * a.val⁻¹ = _
    exact (Equiv.swap_apply_apply a.val 4 5).symm
  exact ⟨_,_,a.val.injective.ne (by decide),hh⟩
end CFSG.Quasithin.ChapterB.Offenders.SixCorePoint
