module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.Transposition
public import Theory.ElementaryAbelian.VectorSpace
/-!
# Transposition movement on a whole augmentation quotient

A transposition has only zero and one duad as its displacements on the
six-letter augmentation module. Equivariance and surjectivity transport
that bound to every whole moved cover, giving a commutator of order at most
two. The target is the original subgroup, not a chosen natural complement.
The application to the actual critical edge is in CriticalTransposition.

Source: MS93 (3.3)(ii)(2), printed pp.866--867.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
private def duadCore (i j : Fin 6) : core (Fin 6) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core,Finset.sum_add_distrib]
    decide⟩

private theorem swap_two_values (i j : Fin 6) (v : core (Fin 6)) :
    coreRepresentation (Fin 6) (Equiv.swap i j) v - v = 0 ∨
      coreRepresentation (Fin 6) (Equiv.swap i j) v - v = duadCore i j := by
  have cert : ∀ i j : Fin 6, ∀ v : Fin 6 → ZMod 2,
      representation (Fin 6) (Equiv.swap i j) v-v = 0 ∨
        representation (Fin 6) (Equiv.swap i j) v-v = Pi.single i 1 + Pi.single j 1 := by
    decide +kernel
  rcases cert i j v.val with hh | hh
  · exact Or.inl (Subtype.ext hh)
  · exact Or.inr (Subtype.ext hh)

/-- A transposition image moves at most one line on every quotient of the
whole augmentation cover, without splitting off its constant line. -/
theorem commutator_card_le_two_of_transposition
    {M : Type*} [Group M] [Finite M] (W : Subgroup M) [W.Normal]
    [IsElementaryAbelian 2 W] (q : M →* Equiv.Perm (Fin 6))
    (f : core (Fin 6) →ₗ[ZMod 2] Additive W) (hf : Function.Surjective f)
    (hact : ∀ g v, (f (coreRepresentation (Fin 6) (q g) v)).toMul =
      MulAut.conjNormal g (f v).toMul)
    (A : Subgroup M) (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap)
    (hA : A.map q = zpowers t) : Nat.card (⁅A,W⁆ : Subgroup M) ≤ 2 := by
  obtain ⟨i,j,hij,rfl⟩ := ht
  let z : W := (f (duadCore i j)).toMul
  have hbound : ⁅A,W⁆ ≤ zpowers (z : M) := by
    apply commutator_le.mpr
    intro a ha w hw
    obtain ⟨v,hv⟩ := hf (Additive.ofMul (⟨w,hw⟩ : W))
    have hqa : q a ∈ zpowers (Equiv.swap i j) := hA ▸ mem_map_of_mem q ha
    rw [mem_zpowers_iff_mem_range_orderOf,
      (show (Equiv.swap i j).IsSwap from ⟨i,j,hij,rfl⟩).orderOf] at hqa
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hqa
    have hnlt := Finset.mem_range.mp hn
    have hdelta : (f (coreRepresentation (Fin 6) (q a) v-v)).toMul.val = ⁅a,w⁆ := by
      rw [map_sub,toMul_sub,div_eq_mul_inv,hact,hv]
      rfl
    have hd : coreRepresentation (Fin 6) (q a) v-v = 0 ∨
        coreRepresentation (Fin 6) (q a) v-v = duadCore i j := by
      interval_cases n
      · rw [pow_zero] at he
        rw [←he,map_one,Module.End.one_apply,sub_self]
        exact Or.inl rfl
      · rw [pow_one] at he
        rw [←he]
        exact swap_two_values i j v
    rw [←hdelta]
    rcases hd with hh | hh
    · rw [hh,map_zero]
      exact one_mem _
    · rw [hh]
      exact mem_zpowers (z : M)
  have hz2 : (z : M) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) _ z.property
  exact (card_le_of_le hbound).trans (by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by decide : 0 < 2) (orderOf_dvd_of_pow_eq_one hz2))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
