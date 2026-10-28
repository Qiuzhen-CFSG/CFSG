module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Separation of the actual A₅ block from natural rank-one modules

The alternating A₅ module has a nonzero vector fixed by a cubic element;
the natural plane for SL₂ in characteristic two has no such vector. The
two block markings act on the same intrinsic U/C_U(L), so their actual
conjugation equations give an equivariant additive isomorphism and hence
contradict that fixed-vector obstruction. No particular exceptional group
isomorphism A₅ ≃ SL₂(4) is chosen.

This is the module comparison needed in the ordinary-component branch of
Aschbacher–Smith 4.3.6, printed pp.614–615, specialized to the original
alternating A₅ block. Producing the C.3.1 local embedding remains separate.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]

theorem IsAlternatingBlock.not_linearTwo_model (h : IsAlternatingBlock L 5)
    {F : Type*} [Field F] [CharP F 2] :
    ¬ IsLinearBlockModel L (Representation.specialLinearNatural (k := F) 2) := by
  rintro ⟨ρN,⟨mN⟩,hN⟩
  obtain ⟨ρA,⟨mA⟩,hA⟩ := h.2.2
  let f := mA.quotientIso.symm.trans mN.quotientIso
  let e := mA.moduleIso.symm.trans mN.moduleIso
  let E : BinaryPermutation.natural (Fin 5) →+ (Fin 2 → F) :=
    (MulEquiv.toAdditive e).toAddMonoidHom
  apply BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_natural_injection
    f.toMonoidHom f.injective E (MulEquiv.toAdditive e).injective
  intro a v
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (mA.quotientIso.symm a)
  have ha : mA.quotientIso (QuotientGroup.mk' (pCore 2 L) l) = a := by
    rw [hl,mA.quotientIso.apply_symm_apply]
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (blockFixed L)
    (mA.moduleIso.symm (Multiplicative.ofAdd v))
  have hv : mA.moduleIso (QuotientGroup.mk' (blockFixed L) u) = Multiplicative.ofAdd v := by
    rw [hu,mA.moduleIso.apply_symm_apply]
  have hAv := mA.intertwining l u
  have hNv := mN.intertwining l u
  rw [ha,hv] at hAv
  have heA : e (ρA a (Multiplicative.ofAdd v)) =
      mN.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u)) := by
    rw [← hAv]
    exact congrArg mN.moduleIso (mA.moduleIso.symm_apply_apply _)
  have heV : e (Multiplicative.ofAdd v) = mN.moduleIso (QuotientGroup.mk' (blockFixed L) u) := by
    rw [← hv]
    exact congrArg mN.moduleIso (mA.moduleIso.symm_apply_apply _)
  have heactor : f a = mN.quotientIso (QuotientGroup.mk' (pCore 2 L) l) := by
    rw [← ha]
    exact congrArg mN.quotientIso (mA.quotientIso.symm_apply_apply _)
  have hvA := hA a (Multiplicative.ofAdd v)
  change (ρA a (Multiplicative.ofAdd v)).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 5) a.val v at hvA
  have hvN := hN (f a) (e (Multiplicative.ofAdd v))
  change E ((BinaryPermutation.naturalRepresentation (Fin 5)) a.val v) = _
  rw [← hvA]
  change (e (ρA a (Multiplicative.ofAdd v))).toAdd = _
  rw [heA,hNv]
  change _ = Representation.specialLinearNatural (k := F) 2 (f a)
    (e (Multiplicative.ofAdd v)).toAdd
  rw [heactor,heV]
  rw [heactor,heV] at hvN
  exact hvN

theorem IsAlternatingBlock.not_l2EvenBlock (h : IsAlternatingBlock L 5) (n : ℕ) :
    ¬ IsL2EvenBlock L n := by
  rintro ⟨_,_,F,_,_,hF,_,hm⟩
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact h.not_linearTwo_model hm
end CFSG.Quasithin.ChapterC
