module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
/-!
# A₆ local normalizers and the innerness criterion for a two-group fixer

The actual involution centralizer has order eight. Characteristic two of
all nontrivial two-subgroup normalizers follows from the prime-centralizer
criterion. The complete outer fixed-subgroup models also imply that an
involutory automorphism with two-group fixed subgroup must be inner.
Transport retains the given marked carrier and automorphism.

Source application: Aschbacher–Smith, the field-two branch of 2.5.2(2)
and 2.5.3(4), printed pp.551–553.
-/

public section
open Subgroup GLS3.Chapter5
namespace AlternatingSix.ShadowLocal

/-- An involution with a two-group fixed subgroup is inner. -/
theorem involution_inner_of_fixed_isTwoGroup (β : AutA6) (hβ : orderOf β = 2)
    (hp : IsPGroup 2 (automorphismFixedSubgroup β)) : β ∈ inner := by
  obtain ⟨P,hP⟩ := (hp.map (MulAut.conj : A6 →* AutA6)).exists_le_sylow
  exact innerSylowCenter_le_inner P ((involution_fixed_le_sylow_iff P β hβ).mp hP)

/-- Transport that criterion to the actual marked carrier. -/
theorem involution_inner_of_equiv_fixed_isTwoGroup
    {L : Type*} [Group L] (e : L ≃* A6) (α : MulAut L)
    (hα : orderOf α = 2) (hp : IsPGroup 2 (automorphismFixedSubgroup α)) :
    α ∈ (MulAut.conj (G := L)).range := by
  let β := MulAut.congr e α
  let j := fixedSubgroupMulEquivOfCompat e α β (fun x => by simp [β])
  have hβ : orderOf β = 2 := ((MulAut.congr e).orderOf_eq α).trans hα
  obtain ⟨b,hb⟩ := involution_inner_of_fixed_isTwoGroup β hβ (hp.of_equiv j)
  refine ⟨e.symm b, (MulAut.congr e).injective ?_⟩
  calc
    _ = MulAut.conj b := by
      ext x
      simp [MulAut.congr, MulAut.conj_apply]
    _ = _ := hb

/-- Every nontrivial two-subgroup normalizer in A₆ has characteristic two. -/
theorem normalizer_core_selfCentralizing
    (R : Subgroup A6) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    centralizer (pCore 2 (normalizer (R : Set A6)) : Set (normalizer (R : Set A6))) ≤
      pCore 2 (normalizer (R : Set A6)) := by
  apply Subgroup.normalizer_core_selfCentralizing_of_prime_centralizers ?_ R hp hne
  intro t ht
  have hc : Nat.card (centralizer ({t} : Set A6)) = 8 := by
    rw [← inner_fixed_eq_centralizer]
    exact inner_involution_fixed_card t ht
  have hp : IsPGroup 2 (centralizer ({t} : Set A6)) :=
    IsPGroup.of_card (n := 3) hc
  have he : pCore 2 (centralizer ({t} : Set A6)) = ⊤ :=
    top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
  rw [he]
  exact le_top
end AlternatingSix.ShadowLocal
