module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Blocks

/-!
# Faithful orthogonal block extension across scalar quotients

An orthogonal block acting trivially on a nonzero complementary space
cannot become a nonidentity scalar. Thus the actual block homomorphisms
remain injective after either elementary or full-commutator projectivization.
The final marked adapter transports the ternary minus-six involution and
its concrete elementary subgroup of order 3⁴ through any such embedding.

These are the common transport steps for the higher ternary orthogonal
families in Aschbacher–Smith A.2.17 and I.2.1; see GLS3 §2.7.
-/

open ClassicalOrthogonal.Fundamental.SplitOddBlocks
open Subgroup
@[expose] public noncomputable section
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F]
variable {U V W : Type} [AddCommGroup U] [Module F U]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

def firstBlock (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) (e : (Q.prod R).IsometryEquiv S) :
    elementarySubgroup Q →* elementarySubgroup S :=
  (blockMap Q R S e).comp (MonoidHom.inl _ _)

theorem firstBlock_apply (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) (e : (Q.prod R).IsometryEquiv S)
    (g : elementarySubgroup Q) (u : U) (v : V) :
    (firstBlock Q R S e g).val.val (e (u,v)) = e (g.val.val u,v) :=
  blockMap_apply Q R S e (g,1) (u,v)

theorem firstBlock_projective_injective [Nontrivial V]
    (Q : QuadraticForm F U) (R : QuadraticForm F V)
    (S : QuadraticForm F W) (e : (Q.prod R).IsometryEquiv S) :
    Function.Injective ((projectiveElementaryMap S).comp (firstBlock Q R S e)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨c,_,hc⟩ := (projectiveElementaryMap_eq_one_iff S _).mp hg
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have ht := hc (e (0,v))
  rw [firstBlock_apply, ← map_smul] at ht
  have hs : v=c • v := congrArg Prod.snd (e.injective ht)
  have hc1 : c=1 := smul_left_injective F hv (by simpa using hs.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  have ht := hc (e (u,0))
  rw [firstBlock_apply,hc1,one_smul] at ht
  exact congrArg Prod.fst (e.injective ht)

variable [Finite F] [CharP F 3]

def sixBlock (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S) :
    MinusSix (F := F) →* elementarySubgroup S :=
  (firstBlock (Minus.quadraticForm F 3) Q S e).comp
    (MulEquiv.subgroupCongr
      (Fundamental.MinusCentralizer.complement_elementary_eq_omega (F := F)
        2 (by omega) ternary_two_ne_zero).symm).toMonoidHom

theorem sixBlock_projective_injective [Nontrivial V]
    (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S) :
    Function.Injective ((projectiveElementaryMap S).comp (sixBlock Q S e)) :=
  (firstBlock_projective_injective (Minus.quadraticForm F 3) Q S e).comp
    (MulEquiv.subgroupCongr
      (Fundamental.MinusCentralizer.complement_elementary_eq_omega (F := F)
        2 (by omega) ternary_two_ne_zero).symm).injective

def sixOmegaBlock (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S) :
    MinusSix (F := F) →* Minus.Omega F W S :=
  Fundamental.MinusCentralizer.derivedMap
    ((conjugate e).comp ((orthogonalProd (Minus.quadraticForm F 3) Q).comp
      (MonoidHom.inl _ _)))

omit [CharP F 3] in
theorem sixOmegaBlock_apply (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S)
    (g : MinusSix (F := F)) (u : Minus.Space F 2) (v : V) :
    (sixOmegaBlock Q S e g).val.val (e (u,v)) = e (g.val.val u,v) := by
  change e (g.val.val (e.symm (e (u,v))).1,(e.symm (e (u,v))).2) = _
  rw [e.symm_apply_apply]

def sixProjectiveOmegaBlock (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S) :
    MinusSix (F := F) →* Minus.ProjectiveOmega F W S :=
  (QuotientGroup.mk' (Minus.scalarSubgroup F W S)).comp (sixOmegaBlock Q S e)

omit [CharP F 3] in
theorem sixProjectiveOmegaBlock_injective [Nontrivial V]
    (Q : QuadraticForm F V) (S : QuadraticForm F W)
    (e : ((Minus.quadraticForm F 3).prod Q).IsometryEquiv S) :
    Function.Injective (sixProjectiveOmegaBlock Q S e) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨c,hc⟩ := (Minus.projectiveOmega_mk_eq_one_iff F W S _).mp hg
  obtain ⟨v,hv⟩ := exists_ne (0 : V)
  have ht := hc (e (0,v))
  rw [sixOmegaBlock_apply, ← map_smul] at ht
  have hs : v=(c:F) • v := congrArg Prod.snd (e.injective ht)
  have hc1 : (c:F)=1 := smul_left_injective F hv (by simpa using hs.symm)
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro u
  have ht := hc (e (u,0))
  rw [sixOmegaBlock_apply,hc1,one_smul] at ht
  exact congrArg Prod.fst (e.injective ht)

omit [CharP F 3] in
theorem exists_elementary_four_centralizer_of_embedding
    {H : Type*} [Group H] (hcard : Nat.card F = 3)
    (f : MinusSix (F := F) →* H) (hf : Function.Injective f) :
    ∃ z : H, orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
        Nat.card A = 3^4 ∧ ∃ j : A →* centralizer ({z} : Set H), Function.Injective j := by
  let := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [pow_one,Nat.card_eq_fintype_card] using hcard)
  obtain ⟨A,hG,hfin,hA,hAc,j,hj⟩ := exists_minusSix_elementary_four hcard
  let := hG
  let := hfin
  let := hA
  let z := f (negativeSix hcard)
  have hz2 : z^2=1 := by rw [← map_pow,negativeSix_square,map_one]
  have hz1 : z≠1 := fun hh => negativeSix_ne_one hcard (hf (hh.trans (map_one _).symm))
  let k := f.comp j
  have hk : ∀ a, k a ∈ centralizer ({z} : Set H) := by
    intro a
    exact mem_centralizer_singleton_iff.mpr ((negativeSix_commute hcard (j a)).map f)
  refine ⟨z,orderOf_eq_prime hz2 hz1,A,inferInstance,inferInstance,inferInstance,hAc,
    k.codRestrict _ hk,?_⟩
  intro a b hab
  exact hj (hf (congrArg Subtype.val hab))

end ClassicalOrthogonal.OddSevenTernaryCover
