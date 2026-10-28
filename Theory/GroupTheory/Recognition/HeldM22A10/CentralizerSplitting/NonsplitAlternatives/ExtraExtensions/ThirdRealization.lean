module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.FactorSets
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitModels
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.ThirdRealization.Realization

/-!
# Nonsplitting of the third binary extension

Two disjoint transpositions in S4 are commuting involutions. Their involutory
lifts in the exact third permutation group are enumerated by the certificate,
and every pair fails to commute at point zero. Consequently no homomorphic
section exists. Correcting a coboundary factor set would give such a section.

This realizes the third candidate needed by the independent extension argument
for Huppert--Blackburn III, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
open LocalModelDichotomy NonsplitModels
namespace ThirdRealization

public theorem lifts_not_commute (a b : Third)
    (ha : a * a = 1) (hb : b * b = 1)
    (hqa : projection a = Equiv.swap (0 : Fin 4) 1)
    (hqb : projection b = Equiv.swap (2 : Fin 4) 3) : a * b ≠ b * a := by
  obtain ⟨i, rfl⟩ := rowElement_surjective a
  obtain ⟨j, rfl⟩ := rowElement_surjective b
  have hi := involution_lifts_left i (fun x => by
    have h := congrArg (fun g : Third => g.val x) ha
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, rowElement, rowPerm_apply,
      Subgroup.coe_one, Equiv.Perm.one_apply] using h) (fun x => by
    have h := congrArg (fun s : SymmetricFour => s x) hqa
    simpa only [projection_apply, rowElement, rowPerm_apply] using h)
  have hj := involution_lifts_right j (fun x => by
    have h := congrArg (fun g : Third => g.val x) hb
    simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, rowElement, rowPerm_apply,
      Subgroup.coe_one, Equiv.Perm.one_apply] using h) (fun x => by
    have h := congrArg (fun s : SymmetricFour => s x) hqb
    simpa only [projection_apply, rowElement, rowPerm_apply] using h)
  have hi' : ∃ k : Fin 4, i = ![270, 287, 302, 309] k := by
    rcases hi with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  have hj' : ∃ k : Fin 4, j = ![265, 278, 307, 379] k := by
    rcases hj with h | h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
  obtain ⟨k, rfl⟩ := hi'
  obtain ⟨l, rfl⟩ := hj'
  intro hab
  apply lifts_do_not_commute k l
  have h := congrArg (fun g : Third => g.val 0) hab
  simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, rowElement, rowPerm_apply] using h

/-- The actual quotient has no homomorphic section. -/
public theorem no_section (σ : SymmetricFour →* Third)
    (hσ : ∀ s, projection (σ s) = s) : False := by
  let s : SymmetricFour := Equiv.swap 0 1
  let t : SymmetricFour := Equiv.swap 2 3
  have hs : s * s = 1 := by decide +kernel
  have ht : t * t = 1 := by decide +kernel
  have hst : s * t = t * s := by decide +kernel
  apply lifts_not_commute (σ s) (σ t) (by rw [← map_mul, hs, map_one])
    (by rw [← map_mul, ht, map_one]) (hσ s) (hσ t)
  rw [← map_mul, ← map_mul, hst]

/-- The factor set of this exact realization is not a coboundary. -/
public theorem factorSet_not_isCoboundary : ¬ extension.factorSet.IsCoboundary := by
  rintro ⟨b, hb, hbc⟩
  let σ : SymmetricFour →* Third :=
    { toFun := fun s => extension.normalForm ((b s)⁻¹, s)
      map_one' := by simp [ActionExtension.normalForm_apply, hb]
      map_mul' := by
        intro s t
        rw [← extension.normalForm_mul]
        apply congrArg extension.normalForm
        refine Prod.ext ?_ rfl
        have hcst : extension.factorSet.value s t =
            b s * sixOrbitAction s (b t) * (b (s * t))⁻¹ := by
          apply eq_mul_inv_iff_mul_eq.mpr
          simpa only [FactorSet.trivial, mul_one] using hbc s t
        simp only [map_inv, hcst]
        simp [mul_assoc, mul_left_comm, mul_comm] }
  apply no_section σ
  intro s
  change extension.rightHom (extension.inl ((b s)⁻¹) * extension.normalizedSection s) = s
  rw [map_mul, extension.rightHom_inl, extension.projection_section, one_mul]

end ThirdRealization

/-- The specified third permutation model realizes a nonsplit six-orbit extension. -/
public theorem third_nonsplit_realization :
    ∃ E : ActionExtension sixOrbitAction Third, ¬ E.factorSet.IsCoboundary :=
  ⟨ThirdRealization.extension, ThirdRealization.factorSet_not_isCoboundary⟩

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
