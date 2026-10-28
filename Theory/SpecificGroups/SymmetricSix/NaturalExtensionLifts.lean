module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Involution lifts in the marked natural A₆ extension

An involution of A₆ has equal fixed and norm spaces on the actual polar
four-space. The canonical double transposition is checked on the fifteen
duads; involution conjugacy transports the result. Consequently the square
of any lift can be removed by multiplying by an element of its original
kernel. The quotient homomorphism and its polar action marking are retained.
No section, splitting, or cohomology premise is used.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
open scoped Matrix

private def doubleSwap : A6 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide +kernel⟩

private def doubleDuad (d : Duad) : Duad :=
  ![0, 6, 5, 7, 8, 2, 1, 3, 4, 9, 12, 13, 10, 11, 14] d

private theorem doubleDuad_smul (d : Duad) :
    doubleSwap.val • d = doubleDuad d := by
  apply duadSet_injective
  rw [duadSet_smul]
  revert d
  decide +kernel

private theorem doubleSwap_norm (v : NaturalModule)
    (hv : polarAction doubleSwap.val v = v) :
    ∃ w : NaturalModule, w + polarAction doubleSwap.val w = v := by
  by_cases hz : v = 0
  · exact ⟨0, by simp [hz]⟩
  obtain ⟨d, hd⟩ := polarVector_bijective.2 ⟨v, hz⟩
  have hdv : (polarVector d).val = v := congrArg Subtype.val hd
  rw [← hdv, polarAction_vector, doubleDuad_smul] at hv
  have hdd : doubleDuad d = d := polarVector_injective (Subtype.ext hv)
  have cert : ∀ d : Duad, doubleDuad d = d → ∃ e : Duad,
      (polarVector e).val + (polarVector (doubleDuad e)).val = (polarVector d).val := by
    decide +kernel
  obtain ⟨e, he⟩ := cert d hdd
  exact ⟨(polarVector e).val, by rw [polarAction_vector, doubleDuad_smul, he, hdv]⟩

private theorem doubleSwap_order : orderOf doubleSwap = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem fixed_is_norm (a : A6) (ha : orderOf a = 2)
    (v : NaturalModule) (hv : polarAction a.val v = v) :
    ∃ w : NaturalModule, w + polarAction a.val w = v := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (AlternatingSix.ShadowLocal.involutions_isConj a doubleSwap ha doubleSwap_order)
  have hgs : g.val * a.val * g.val⁻¹ = doubleSwap.val := congrArg Subtype.val hg
  have hfix : polarAction doubleSwap.val (polarAction g.val v) = polarAction g.val v := by
    rw [← hgs, ← polarAction_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one, polarAction_mul, hv]
  obtain ⟨w, hw⟩ := doubleSwap_norm _ hfix
  have hmove : a.val * g.val⁻¹ = g.val⁻¹ * doubleSwap.val := by
    rw [← hgs]
    group
  refine ⟨polarAction g.val⁻¹ w, ?_⟩
  calc
    polarAction g.val⁻¹ w + polarAction a.val (polarAction g.val⁻¹ w) =
        polarAction g.val⁻¹ (w + polarAction doubleSwap.val w) := by
      rw [← polarAction_mul, hmove, polarAction_mul, polarAction_add]
    _ = v := by rw [hw, ← polarAction_mul, inv_mul_cancel, polarAction_one]

/-- The fixed vectors of an A₆ involution are exactly the image of its norm
on the literal matrix polar module. -/
theorem polar_involution_fixed_iff_norm (a : A6) (ha : orderOf a = 2)
    (v : NaturalModule) :
    (polarRepresentation a.val).val *ᵥ v = v ↔
      ∃ w : NaturalModule, w + (polarRepresentation a.val).val *ᵥ w = v := by
  simp only [polarRepresentation_apply]
  refine ⟨fixed_is_norm a ha v, ?_⟩
  rintro ⟨w, rfl⟩
  have haa : a.val * a.val = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one a)
    simpa only [ha, pow_two, Subgroup.coe_mul, Subgroup.coe_one] using h
  rw [polarAction_add, ← polarAction_mul, haa, polarAction_one, add_comm]

/-- Correct any lift of an A₆ involution in its original marked kernel.
The correcting multiplier and the unchanged quotient image are explicit. -/
theorem correct_involution_lift {G : Type*} [Group G] (q : G →* A6)
    (e : q.ker ≃* Multiplicative NaturalModule)
    (he : ∀ (g : G) (v : q.ker), e (MulAut.conjNormal g v) =
      Multiplicative.ofAdd ((polarRepresentation (q g).val).val *ᵥ (e v).toAdd))
    (x : G) (hx : orderOf (q x) = 2) :
    ∃ p : q.ker, ((p : G) * x) ^ 2 = 1 ∧ q ((p : G) * x) = q x := by
  let s : q.ker := ⟨x ^ 2, by
    change q (x ^ 2) = 1
    rw [map_pow, ← hx, pow_orderOf_eq_one]⟩
  have hs : MulAut.conjNormal x s = s := by
    apply Subtype.ext
    change x * x ^ 2 * x⁻¹ = x ^ 2
    group
  have hsf := congrArg e hs
  rw [he] at hsf
  obtain ⟨w, hw⟩ := (polar_involution_fixed_iff_norm (q x) hx (e s).toAdd).mp
    (congrArg Multiplicative.toAdd hsf)
  let p := e.symm (Multiplicative.ofAdd w)
  have hep : e p = Multiplicative.ofAdd w := e.apply_symm_apply _
  have hk : p * MulAut.conjNormal x p * s = 1 := by
    apply e.injective
    rw [map_mul, map_mul, he, hep, map_one]
    change w + (polarRepresentation (q x).val).val *ᵥ w + (e s).toAdd = 0
    rw [hw]
    funext i
    exact CharTwo.add_self_eq_zero _
  refine ⟨p, ?_, ?_⟩
  · have hh := congrArg Subtype.val hk
    change (p : G) * (x * (p : G) * x⁻¹) * x ^ 2 = 1 at hh
    calc
      ((p : G) * x) ^ 2 = (p : G) * (x * (p : G) * x⁻¹) * x ^ 2 := by
        simp only [pow_two]
        group
      _ = 1 := hh
  · rw [map_mul, show q (p : G) = 1 from p.property, one_mul]

end Theory.SpecificGroups.SymmetricSix.NaturalExtensionLifts
