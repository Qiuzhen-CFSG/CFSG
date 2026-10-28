module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.NativeFour
public import Theory.SpecificGroups.SymmetricFourConjugacy

/-!
# Cubic subgroups in the actual four-letter symmetric group

A cubic normalizer is the complementary point stabilizer of order six.
Two distinct cubic subgroups generate a subgroup containing the normal
four. The latter uses short checked words on the three double swaps,
with no subgroup enumeration.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI.NativeFour
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
abbrev c : Four := SymmetricFourConjugacy.threeCycle

def cubic : Subgroup Four where
  carrier := {g | g=1 ∨ g=c ∨ g=c^2}
  one_mem' := Or.inl rfl
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel
instance : DecidablePred (·∈cubic) := fun _=>inferInstanceAs (Decidable (_∨_∨_))

theorem cubic_card : Nat.card cubic=3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem cubic_normalizer :normalizer (cubic:Set Four)=MulAction.stabilizer Four (3:Fin 4) := by
  ext g
  rw [mem_normalizer_iff,MulAction.mem_stabilizer_iff]
  exact (show ∀g:Four,(∀x:Four,x∈cubic↔g*x*g⁻¹∈cubic)↔g (3:Fin 4)=3 by decide +kernel) g

theorem cubic_normalizer_card : Nat.card (normalizer (cubic:Set Four))=6 := by
  rw [cubic_normalizer,Nat.card_eq_fintype_card]
  decide +kernel

theorem cubic_normalizer_involution : ∃t∈normalizer (cubic:Set Four),orderOf t=2 := by
  refine ⟨Equiv.swap 0 1,?_,?_⟩
  · rw [cubic_normalizer]
    decide +kernel
  · exact orderOf_eq_prime (by decide) (by decide)

private def independentCubics (x y:Four):Prop :=
  x^3=1 ∧ y^3=1 ∧ x≠1 ∧ y≠1 ∧ y≠x ∧ y≠x^2
private instance (x y:Four):Decidable (independentCubics x y) :=
  inferInstanceAs (Decidable (_∧_∧_∧_∧_∧_))
private def wordCover (x y:Four):Prop :=
  ∀d:Fin 3,∃i j k:Fin 3,doubleSwap d=x^i.val*y^j.val*x^k.val
private instance (x y:Four):Decidable (wordCover x y) :=
  inferInstanceAs (Decidable (∀d:Fin 3,∃i j k:Fin 3,doubleSwap d=x^i.val*y^j.val*x^k.val))
private theorem cubic_words : ∀x y:Four,independentCubics x y→wordCover x y := by
  decide +kernel

/-- Two distinct cubic subgroups generate a subgroup containing the four-core. -/
theorem core_le_sup_cubics (U V:Subgroup Four) (hU:Nat.card U=3) (hV:Nat.card V=3)
    (hne:U≠V):core≤U⊔V := by
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=U) 3 (by rw [hU])
  obtain ⟨y,hy⟩:=exists_prime_orderOf_dvd_card' (G:=V) 3 (by rw [hV])
  have hxG:orderOf (x:Four)=3:=(orderOf_injective U.subtype U.subtype_injective x).trans hx
  have hyG:orderOf (y:Four)=3:=(orderOf_injective V.subtype V.subtype_injective y).trans hy
  have hVU:¬(y:Four)∈U := by
    intro hyU
    have hle:zpowers (y:Four)≤U:=zpowers_le.mpr hyU
    have hzV:zpowers (y:Four)=V:=eq_of_le_of_card_ge (zpowers_le.mpr y.property)
      (by rw [Nat.card_zpowers,hyG,hV])
    apply hne
    rw [←hzV]
    exact (eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers,hyG,hU])).symm
  have hw:=cubic_words x y ⟨(hxG ▸ pow_orderOf_eq_one (x:Four)),
    (hyG ▸ pow_orderOf_eq_one (y:Four)),
    (by intro he; simp [he] at hxG),(by intro he; simp [he] at hyG),
    (fun he=>hVU (he ▸ x.property)),(fun he=>hVU (he ▸ U.pow_mem x.property 2))⟩
  have hd:∀d∈core,d=1 ∨ ∃i:Fin 3,d=doubleSwap i := by decide +kernel
  intro d hdcore
  rcases hd d hdcore with rfl|⟨i,rfl⟩
  · exact (U⊔V).one_mem
  · obtain ⟨a,b,c,he⟩:=hw i
    rw [he]
    exact (U⊔V).mul_mem ((U⊔V).mul_mem
      ((U⊔V).pow_mem (show (x:Four)∈U⊔V from (show U≤U⊔V from le_sup_left) x.property) a.val)
      ((U⊔V).pow_mem (show (y:Four)∈U⊔V from (show V≤U⊔V from le_sup_right) y.property) b.val))
      ((U⊔V).pow_mem (show (x:Four)∈U⊔V from (show U≤U⊔V from le_sup_left) x.property) c.val)
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI.NativeFour
