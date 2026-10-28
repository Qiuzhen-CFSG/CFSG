module
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Source

/-!
# The small Schur field in H.4.7

The actual word models give a component endomorphism field of order two
or four. Restricting intertwiners injects the endomorphism field of the
whole actor into that component field. Its binary dimension therefore
shows that it too has order two or four. This supplies the order-seven
multiplicity argument on the original actor, without changing carriers.

Source: Aschbacher–Smith H.4.7, printed pp.382–383, used in 5.1.17, p.641
(refs/quasithin.pdf).
-/

public noncomputable section
open Module Representation
open scoped MonoidAlgebra MatrixGroups
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField
set_option backward.isDefEq.respectTransparency false
variable {k D M V : Type*} [Field k] [Finite k] [Group D] [Group M]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem end_card_le_comp (σ : Representation k M V) (π : D →* M) :
    Nat.card (Module.End k[M] σ.asModule) ≤
      Nat.card (Module.End k[D] (Representation.asModule (σ.comp π))) := by
  let f : IntertwiningMap σ σ → IntertwiningMap (σ.comp π) (σ.comp π) :=
    fun q => ⟨q.toLinearMap,fun d => q.isIntertwining' (π d)⟩
  have hf : Function.Injective f := fun q r h =>
    IntertwiningMap.ext (congrArg (fun q : IntertwiningMap (σ.comp π) (σ.comp π) => q.toLinearMap) h)
  rw [← Nat.card_congr (IntertwiningMap.equivAlgEnd σ).toEquiv,
    ← Nat.card_congr (IntertwiningMap.equivAlgEnd (σ.comp π)).toEquiv]
  let : Finite (IntertwiningMap (σ.comp π) (σ.comp π)) :=
    Finite.of_injective (IntertwiningMap.equivAlgEnd (σ.comp π))
      (IntertwiningMap.equivAlgEnd (σ.comp π)).injective
  exact Nat.card_le_card_of_injective f hf

end CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField
variable {M V : Type*} [Group M] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
private theorem binary_field_card_of_le_four (σ : Representation (ZMod 2) M V) [IsIrreducible σ]
    (h : Nat.card (Module.End (ZMod 2)[M] σ.asModule) ≤ 4) :
    Nat.card (Module.End (ZMod 2)[M] σ.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[M] σ.asModule) = 4 := by
  let E := Module.End (ZMod 2)[M] σ.asModule
  let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
  rw [Nat.card_zmod] at he
  have hp : 0 < finrank (ZMod 2) E := Module.finrank_pos
  have hd : finrank (ZMod 2) E ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← he] using h
  have hd' : finrank (ZMod 2) E = 1 ∨ finrank (ZMod 2) E = 2 := by omega
  rcases hd' with hd' | hd'
  · left; simpa only [hd',pow_one] using he
  · right; simpa only [hd',show (2:ℕ)^2=4 from rfl] using he
end CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField

namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
set_option backward.isDefEq.respectTransparency false
variable {F M V : Type*} [Field F] [Finite F] [CharP F 2] [Group M]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The actual endomorphism field of the source actor has order two or four. -/
theorem source_schurField_card (hcard : Nat.card F = 4)
    (e : PSL(3,F) ≃* Theory.GroupTheory.generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) [IsIrreducible ρ]
    [IsIrreducible (ρ.comp (Theory.GroupTheory.generalizedFitting M).subtype)]
    (hρ : Function.Injective ρ) :
    Nat.card (Module.End (ZMod 2)[M] ρ.asModule) = 2 ∨
      Nat.card (Module.End (ZMod 2)[M] ρ.asModule) = 4 := by
  obtain ⟨ι,b,c,_,_,hd,_⟩ := source_word_model hcard e ρ hρ
  have hc : Nat.card (Module.End (ZMod 2)[SL(3,F)] (coverRep e ρ).asModule) ≤ 4 := by
    let : Module.Finite (ZMod 2) (Module.End (ZMod 2)[SL(3,F)] (coverRep e ρ).asModule) :=
      Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    change 2 ^ schurDegree 2 (coverRep e ρ) ≤ 4
    rw [hd]
    split_ifs <;> decide
  exact CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField.binary_field_card_of_le_four ρ
    ((CFSG.Quasithin.ChapterH.Section01To04.L3Four.SchurField.end_card_le_comp ρ (componentCover e)).trans hc)
end CFSG.Quasithin.ChapterH.Section01To04.L3Four
