module
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.GroupTheory.CoprimePrimeFusion

/-!
# Fusion of cubic subgroups in full covers of J₄

Native order-three fusion in the actual J₄ matrix carrier conjugates suitable
nonidentity powers of two cubics. Coprime-kernel fusion lifts this conjugacy
through the given full cover. Equality of the generated cyclic subgroups then
removes the choice of powers. The result retains the actual conjugating element.

The exterior pushing-up application uses this to move the identified M₂₂
component to its prescribed cubic, which lies in the original intersection
residual and fixes sixteen exterior vectors.
Source: Aschbacher--Smith, 4.2.13, printed p.612. The imported matrix
certificates retain their ATLAS attribution and license.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure
attribute [local irreducible] modelGroup matrixA matrixB

private theorem image_cubic_order {U Y : Type*} [Group U] [Finite U] [Group Y]
    (f : U →* Y) (hk : Nat.Coprime 3 (Nat.card f.ker))
    (x : U) (hx : orderOf x = 3) : orderOf (f x) = 3 := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1)
    (by simpa only [Nat.card_zpowers,pow_one] using hx)
  have hi := injective_comp_subtype_of_coprime_ker f hk (zpowers x) hp
  exact (orderOf_injective (f.comp (zpowers x).subtype) hi ⟨x,mem_zpowers x⟩).trans
    ((orderOf_coe _).symm.trans hx)

private theorem cubic_powers_conjugate (x y : Model)
    (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ k l : ℕ, orderOf (x ^ k) = 3 ∧ orderOf (y ^ l) = 3 ∧
      IsConj (x ^ k) (y ^ l) := by
  obtain ⟨k,g,hg⟩ := Simplicity.three_explicit_coverage matrixA_mul_self matrixB_pow_four
    Cardinality.model_card x hx
  obtain ⟨l,h,hh⟩ := Simplicity.three_explicit_coverage matrixA_mul_self matrixB_pow_four
    Cardinality.model_card y hy
  have ho := Simplicity.orderOf_primeRepresentative_two matrixA_mul_self matrixB_pow_four
  have hk : orderOf (x ^ k) = 3 := by
    have he := (MulAut.conj g).orderOf_eq (x ^ k)
    change orderOf (g * x ^ k * g⁻¹) = _ at he
    rw [←hg,ho] at he
    exact he.symm
  have hl : orderOf (y ^ l) = 3 := by
    have he := (MulAut.conj h).orderOf_eq (y ^ l)
    change orderOf (h * y ^ l * h⁻¹) = _ at he
    rw [←hh,ho] at he
    exact he.symm
  exact ⟨k,l,hk,hl,(isConj_iff.mpr ⟨g,hg.symm⟩).trans
    (isConj_iff.mpr ⟨h,hh.symm⟩).symm⟩

/-- Cubic cyclic subgroups are conjugate in every full three-free central cover. -/
theorem cubic_cyclic_fusion {U : Type*} [Group U] [Finite U]
    (f : U →* Model) (hf : Function.Surjective f)
    (hthree : Nat.Coprime 3 (Nat.card f.ker))
    (x y : U) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    ∃ g : U, (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers y := by
  obtain ⟨k,l,hk,hl,hc⟩ := cubic_powers_conjugate (f x) (f y)
    (image_cubic_order f hthree x hx) (image_cubic_order f hthree y hy)
  have hxp : orderOf (x ^ k) = 3 := by
    apply Nat.dvd_antisymm ((orderOf_pow_dvd k).trans (by rw [hx]))
    have he : orderOf (f (x ^ k)) = 3 := by rw [map_pow]; exact hk
    exact he ▸ orderOf_map_dvd f (x ^ k)
  have hyp : orderOf (y ^ l) = 3 := by
    apply Nat.dvd_antisymm ((orderOf_pow_dvd l).trans (by rw [hy]))
    have he : orderOf (f (y ^ l)) = 3 := by rw [map_pow]; exact hl
    exact he ▸ orderOf_map_dvd f (y ^ l)
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (f.isConj_of_map_isConj_of_prime_order_of_coprime_ker hf hthree hxp hyp
      (by simpa only [map_pow] using hc))
  have hX : zpowers (x ^ k) = zpowers x :=
    eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers x) k))
      (by rw [Nat.card_zpowers,Nat.card_zpowers,hxp,hx])
  have hY : zpowers (y ^ l) = zpowers y :=
    eq_of_le_of_card_ge (zpowers_le.mpr (pow_mem (mem_zpowers y) l))
      (by rw [Nat.card_zpowers,Nat.card_zpowers,hyp,hy])
  refine ⟨g,?_⟩
  rw [←hX,MonoidHom.map_zpowers]
  exact (congrArg zpowers hg).trans hY

end Janko4.LocalStructure
