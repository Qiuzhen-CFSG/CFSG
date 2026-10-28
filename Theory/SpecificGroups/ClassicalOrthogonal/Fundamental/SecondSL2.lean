module
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer

/-!
# A second faithful determinant-space SL₂ in orthogonal quotients

The right SL₂ factor extended by the identity remains faithful after
projectivization: any common scalar fixes the nonzero complement and is
therefore one. It commutes with the marked left fundamental factor.
These literal maps feed the odd-center field-degree reduction in A.2.17.
Source: Aschbacher–Smith A.2.17, printed p.39.
-/

open Matrix Subgroup
open scoped MatrixGroups
namespace ClassicalOrthogonal.Fundamental
open SplitOddBlocks
universe u
variable {F V W : Type u} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  (Q : QuadraticForm F V) (S : QuadraticForm F W)
  (e : ((formD 2 F).prod Q).IsometryEquiv S)

public theorem rightProjective_inl_injective [Nontrivial V] :
    Function.Injective ((rightProjective Q S e).comp (MonoidHom.inl _ _)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨c,_,hc,hv⟩ := (rightProjective_kernel Q S e (a,1)).mp ha
  obtain ⟨v,hv0⟩ := exists_ne (0 : V)
  have hc1 : c = 1 := smul_left_injective F hv0 (by simpa using (hv v).symm)
  apply Subtype.ext
  change a.val = (1 : Matrix (Fin 2) (Fin 2) F)
  simpa only [hc1,map_one,SpecialLinearGroup.coe_one] using hc

public theorem projective_two_factors_commute (a b : SL(2,F)) :
    Commute (leftProjective Q S e a)
      (((rightProjective Q S e).comp (MonoidHom.inl _ _)) b) :=
  (factors_commute Q S e a (b,1)).map (projectiveElementaryMap S)

namespace MinusCentralizer
variable {F : Type*} [Field F] [Finite F]
public theorem projectiveBlockHom_inl_injective (s : ℕ) (hq : 2 < Nat.card F) :
    Function.Injective ((projectiveBlockHom (F := F) s hq).comp (MonoidHom.inl _ _)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro a ha
  obtain ⟨c,_,hc,hv⟩ := (projectiveBlockHom_kernel_commonScalar s hq (a,1)).mp ha
  obtain ⟨v,hv0⟩ := exists_ne (0 : Minus.Space F s)
  have hc1 : (c : F) = 1 := smul_left_injective F hv0 (by simpa using (hv v).symm)
  apply Subtype.ext
  change a.val = (1 : Matrix (Fin 2) (Fin 2) F)
  simpa only [hc1,one_smul,SpecialLinearGroup.coe_one] using hc

public theorem two_factors_commute (s : ℕ) (hq : 2 < Nat.card F) (a b : SL(2,F)) :
    Commute (fundamentalHom s hq a)
      (((projectiveBlockHom s hq).comp (MonoidHom.inl _ _)) b) :=
  (coverBlockHom_commute s hq a (b,1)).map
    (QuotientGroup.mk' (Minus.scalarSubgroup F _ _))
end MinusCentralizer
end ClassicalOrthogonal.Fundamental
