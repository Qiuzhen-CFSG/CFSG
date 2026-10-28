module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Literal five-letter alternating coordinates inside A₆

Extend a permutation of Fin5 by fixing the last letter of Fin6. Sign is
preserved, and the image is the actual even point stabilizer: injectivity
and the checked common order sixty give surjectivity. The equivalence
retains the action on each of the first five letters, as needed for the
natural-module restriction in13.5.14.

Source: Aschbacher–Smith,13.5.14(3–4), printed p.919.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair

def letterEquiv : Fin 5 ≃ {i : Fin 6 // i.val<5} where
  toFun i := ⟨i.castSucc,i.isLt⟩
  invFun i := ⟨i.val.val,i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def extendPerm : Equiv.Perm (Fin 5) →* S := Equiv.Perm.extendDomainHom letterEquiv

theorem extendPerm_apply (g : Equiv.Perm (Fin 5)) (i : Fin 5) :
    extendPerm g i.castSucc = (g i).castSucc :=
  Equiv.Perm.extendDomain_apply_image g letterEquiv i

theorem extendPerm_last (g : Equiv.Perm (Fin 5)) : extendPerm g 5=5 :=
  Equiv.Perm.extendDomain_apply_not_subtype g letterEquiv (by decide)

theorem extendPerm_sign (g : Equiv.Perm (Fin 5)) :
    Equiv.Perm.sign (extendPerm g) = Equiv.Perm.sign g :=
  Equiv.Perm.sign_extendDomain g letterEquiv

def embedding : alternatingGroup (Fin 5) →* five :=
  (extendPerm.comp (alternatingGroup (Fin 5)).subtype).codRestrict _ (fun g =>
    ⟨extendPerm_last g.val,by change Equiv.Perm.sign (extendPerm g.val)=1;rw [extendPerm_sign];exact g.property⟩)

theorem embedding_injective : Function.Injective embedding := by
  intro a b he
  apply Subtype.ext
  exact Equiv.Perm.extendDomainHom_injective letterEquiv (congrArg Subtype.val he)

theorem embedding_bijective : Function.Bijective embedding :=
  embedding_injective.bijective_of_nat_card_le (by
    rw [five_card,nat_card_alternatingGroup,Nat.card_fin]
    decide)

noncomputable def fiveEquiv : five ≃* alternatingGroup (Fin 5) :=
  (MulEquiv.ofBijective embedding embedding_bijective).symm

@[simp] theorem fiveEquiv_symm_val (g : alternatingGroup (Fin 5)) :
    (fiveEquiv.symm g).val = extendPerm g.val := rfl

theorem fiveEquiv_apply (g : five) (i : Fin 5) :
    g.val i.castSucc = ((fiveEquiv g).val i).castSucc := by
  have he := congrArg (fun h:five=>h.val i.castSucc) (fiveEquiv.symm_apply_apply g)
  rw [fiveEquiv_symm_val,extendPerm_apply] at he
  exact he.symm

/-- The concrete five-letter alternating quotient has no nontrivial two-core. -/
theorem alternating_five_twoCore : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 5))
      (N := pCore 2 (alternatingGroup (Fin 5))) with he | he
  · exact he
  · have hc : Nat.card (pCore 2 (alternatingGroup (Fin 5))) = 60 := by
      rw [he,card_top,nat_card_alternatingGroup,Nat.card_fin]
      decide
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := alternatingGroup (Fin 5))).exists_card_eq
    have hthree : 3 ∣ 2^n := hn ▸ hc.symm ▸ (by decide : 3∣60)
    exact False.elim ((by decide : ¬3∣2) (Nat.prime_three.dvd_of_dvd_pow hthree))

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.FivePair
end
