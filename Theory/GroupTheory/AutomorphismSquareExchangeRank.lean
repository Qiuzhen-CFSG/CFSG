module
public import Theory.GroupTheory.AutomorphismSquareRank

/-!
# Rank of an abelian actor containing a factor exchange

For a finite centerless quasisimple group S, an abelian subgroup of
Aut(S × S) containing the literal factor exchange has two-rank at most
one plus the two-rank of Aut(S). Its subgroup preserving both factors has
index at most two. Commutation with the exchange makes its action on the
first factor faithful, which gives the sharper bound needed for exchanged
Suzuki actors without restricting the full normalizer quotient.

Source: Aschbacher--Smith D.3.7, inequality (∗), printed p.197.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.AutomorphismSquare
variable {S : Type*} [Group S]

private def factorMap : (MulAut S × MulAut S) →* MulAut (S × S) where
  toFun ab := ab.1.prodCongr ab.2
  map_one' := by ext x <;> rfl
  map_mul' := by intros; rfl

private theorem factorMap_injective : Function.Injective (factorMap (S := S)) := by
  intro a b h
  apply Prod.ext
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.fst (DFunLike.congr_fun h (x,1))
  · apply MulEquiv.ext
    intro x
    exact congrArg Prod.snd (DFunLike.congr_fun h (1,x))

variable [Finite S] [IsQuasisimple S]

/-- An abelian automorphism group containing the literal exchange has rank
at most one more than the automorphism rank of one factor. -/
theorem abelian_exchange_rank_le (hZ : center S = ⊥)
    (E : Subgroup (MulAut (S × S))) [IsMulCommutative E]
    (hswap : (MulEquiv.prodComm : MulAut (S × S)) ∈ E) :
    primeRank 2 E ≤ primeRank 2 (MulAut S) + 1 := by
  let H := (factorMap (S := S)).range
  let coordinates : H ≃* (MulAut S × MulAut S) :=
    (MonoidHom.ofInjective factorMap_injective).symm
  have hcoord (x : H) : factorMap (coordinates x) = x :=
    MonoidHom.apply_ofInjective_symm factorMap_injective x
  let C : Subgroup E := H.comap E.subtype
  let lift : C →* H :=
    (E.subtype.comp C.subtype).codRestrict H (fun x => x.property)
  let f : C →* MulAut S := (MonoidHom.fst _ _).comp (coordinates.toMonoidHom.comp lift)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    let ab := coordinates (lift x)
    have hxval : factorMap ab = (x.val : MulAut (S × S)) := hcoord (lift x)
    have ha : ab.1 = 1 := hx
    have hc : factorMap ab * (MulEquiv.prodComm : MulAut (S × S)) =
        (MulEquiv.prodComm : MulAut (S × S)) * factorMap ab := by
      rw [hxval]
      exact congrArg Subtype.val (mul_comm x.val ⟨_,hswap⟩)
    have hb : ab.2 = 1 := by
      apply MulEquiv.ext
      intro y
      have hh := congrArg Prod.fst (DFunLike.congr_fun hc (1,y))
      change ab.1 y = ab.2 y at hh
      rw [ha] at hh
      exact hh.symm
    have he : factorMap ab = 1 := by
      have hab : ab = (1,1) := Prod.ext ha hb
      rw [hab]
      exact factorMap.map_one
    exact Subtype.ext (Subtype.ext (hxval.symm.trans he))
  have hindex : C.index ≤ 2^1 := by
    apply Nat.le_of_dvd (by decide)
    apply C.index_dvd_two_iff.mpr
    refine ⟨⟨_,hswap⟩,?_⟩
    intro x
    rcases normal_form hZ (x : MulAut (S × S)) with ⟨a,b,hx⟩ | ⟨a,b,hx⟩
    · right
      exact ⟨(a,b),hx.symm⟩
    · left
      change (x : MulAut (S × S)) * MulEquiv.prodComm ∈ H
      rw [hx]
      exact ⟨(a,b),rfl⟩
  have h1 := primeRank_le_add_of_index_le C hindex
  have h2 := primeRank_le_of_injective 2 f hf
  omega
end Theory.GroupTheory.AutomorphismSquare
