module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.RadicalModel
public import Theory.SpecificGroups.AlternatingFiveTriangle
public import Mathlib.GroupTheory.Complement

/-!
# A complement in the actual Hall--Janko first endpoint

The native words a and (ca)^4 satisfy the (2,3,5) presentation. Their
involution is nontrivial, so the proved alternating presentation embeds A₅.
Its intersection with the normal two-core is trivial, and the orders give
a complement. Thus the literal J₂ endpoint has split coordinates, retaining
both the actual core and the conjugation action of this complement.

Source: DGS, Groups and Graphs (1985), (5.16), p.117 and (10.9), p.163.
The finite checks use the retained ATLAS J2G1-p100B0 permutations and the
attribution and license of the imported native carrier.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open GeneratorPair FirstFusion Seed

private def letter (i : Fin 3) : l₁ := ⟨centralizerLetter i, centralizerLetter_mem i⟩

private def x : l₁ := letter 0
private def y : l₁ := (letter 1 * letter 0)^4

set_option maxRecDepth 100000 in
private theorem triangle_check : ∀ p : Fin 100,
    LocalCertificate.localLetterValue 0 (LocalCertificate.localLetterValue 0 p) = p ∧
      (fun q => LocalCertificate.localLetterValue 1 (LocalCertificate.localLetterValue 0 q))^[12] p = p ∧
      (fun q => LocalCertificate.localLetterValue 0
        ((fun r => LocalCertificate.localLetterValue 1 (LocalCertificate.localLetterValue 0 r))^[4] q))^[5] p = p := by
  decide +kernel

private theorem letter_value (i : Fin 3) (p : Fin 100) :
    inclusion ((letter i : l₁) : Carrier) p = LocalCertificate.localLetterValue i p :=
  (LocalCertificate.localLetterValue_eq i p).symm

private theorem triangle : x ≠ 1 ∧ x^2 = 1 ∧ y^3 = 1 ∧ (x*y)^5 = 1 := by
  have hp (g : l₁) (n : ℕ) (p : Fin 100) :
      inclusion ((g^n : l₁) : Carrier) p = (inclusion (g : Carrier))^[n] p := by
    simp only [Subgroup.coe_pow,map_pow,Equiv.Perm.coe_pow]
  refine ⟨?_,?_,?_,?_⟩
  · intro he
    have hh := congrArg (fun g : l₁ => inclusion (g : Carrier) 0) he
    change inclusion (centralizerLetter 0) 0 = 0 at hh
    rw [←LocalCertificate.localLetterValue_eq] at hh
    exact (show LocalCertificate.localLetterValue 0 0 ≠ 0 by decide +kernel) hh
  · apply Subtype.ext
    apply inclusion_injective
    apply Equiv.ext
    intro p
    change inclusion (((x^2 : l₁) : Carrier)) p = p
    simpa only [x,hp,Function.iterate_succ_apply,Function.iterate_zero_apply,letter_value] using (triangle_check p).1
  · apply Subtype.ext
    apply inclusion_injective
    apply Equiv.ext
    intro p
    change inclusion (((letter 1 * letter 0)^4)^3 : l₁) p = p
    rw [←pow_mul,hp]
    simpa only [Subgroup.coe_mul,map_mul,Equiv.Perm.coe_mul,Function.comp_def,letter_value]
      using (triangle_check p).2.1
  · apply Subtype.ext
    apply inclusion_injective
    apply Equiv.ext
    intro p
    change inclusion (((x*y)^5 : l₁) : Carrier) p = p
    rw [hp]
    simpa only [x,y,Subgroup.coe_mul,Subgroup.coe_pow,map_mul,map_pow,Equiv.Perm.coe_mul,
      Equiv.Perm.coe_pow,Function.comp_def,letter_value] using (triangle_check p).2.2

/-- The native endpoint contains an actual A₅ complement to its literal two-core. -/
theorem exists_core_complement :
    ∃ C : Subgroup l₁, (pCore 2 l₁).IsComplement' C ∧
      Nonempty (C ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨f,hf⟩ := alternatingGroup.exists_injective_hom_of_triangle x y
    triangle.1 triangle.2.1 triangle.2.2.1 triangle.2.2.2
  let C := f.range
  let eC : C ≃* alternatingGroup (Fin 5) := (MonoidHom.ofInjective hf).symm
  have hpre : (pCore 2 l₁).comap f ≤ pCore 2 (alternatingGroup (Fin 5)) :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_of_injective f hf⟩
  rw [alternatingGroup.five_twoCore_eq_bot] at hpre
  have hd : Disjoint (pCore 2 l₁) C := by
    apply disjoint_def.mpr
    rintro z hz ⟨a,rfl⟩
    have ha : a = 1 := hpre hz
    rw [ha,map_one]
  have hC : Nat.card C = 60 := by
    rw [Nat.card_congr eC.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  have hQ : Nat.card (pCore 2 l₁) = 32 :=
    (Nat.card_congr coreModelEquiv.toEquiv).trans MinusExtraspecial.card_model
  exact ⟨C,isComplement'_of_card_mul_and_disjoint
    (by rw [hQ,hC,card_l₁]) hd,⟨eC⟩⟩

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
