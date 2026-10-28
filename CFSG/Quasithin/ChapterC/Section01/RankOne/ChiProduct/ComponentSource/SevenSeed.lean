module
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.GroupTheory.Perm.SevenPointIndexTen
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
/-!
# The rank-one seed in the seven-letter C.1.27 branch

The actual B.6.9 seed is SL₂ over an even field of size greater than two.
An embedding in A₇ bounds its field degree by three. The degree-three
case has order 504 and contradicts the seven-point Sylow-three/Jordan
obstruction. The remaining field has four elements, and its original
rank-one group is explicitly A₅. This uses the genuine seed hypothesis
and does not require a classification of all primitive seven-point groups.

Source: Aschbacher–Smith C.1.27, printed p.133, applying B.1.13 to the
rank-one or odd alternating seed selected by B.6.9.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource

theorem rankOne_degree_of_seven_embedding
    {F : Type*} [Field F] [Finite F] {n : ℕ} (hn : 1 < n)
    (hF : Nat.card F = 2 ^ n) (f : SL(2,F) →* alternatingGroup (Fin 7))
    (hf : Function.Injective f) : n = 2 := by
  have hc := Nat.card_le_card_of_injective f hf
  rw [Atlas.card_sl_two, hF, nat_card_alternatingGroup, Nat.card_fin] at hc
  norm_num [Nat.factorial] at hc
  have hn4 : n < 4 := by
    by_contra h
    have h16 : 16 ≤ 2 ^ n := by
      calc
        16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
    have hs : 255 ≤ (2 ^ n) ^ 2 - 1 := by
      have hh := Nat.pow_le_pow_left h16 2
      norm_num at hh
      omega
    have hm := Nat.mul_le_mul h16 hs
    omega
  have hcases : n = 2 ∨ n = 3 := by omega
  rcases hcases with h | rfl
  · exact h
  · exfalso
    apply Theory.GroupTheory.SevenPoint.no_faithful_action_of_card_504
      (M := SL(2,F))
      (by rw [Atlas.card_sl_two, hF]; norm_num)
      ((alternatingGroup (Fin 7)).subtype.comp f)
    exact (alternatingGroup (Fin 7)).subtype_injective.comp hf

theorem rankOne_seed_in_seven
    {G F : Type*} [Group G] [Field F] [Finite F]
    (K L : Subgroup G) (hKL : K ≤ L) (eL : L ≃* alternatingGroup (Fin 7))
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (eK : K ≃* SL(2,F)) :
    n = 2 ∧ Nonempty (K ≃* alternatingGroup (Fin 5)) := by
  let f : SL(2,F) →* alternatingGroup (Fin 7) :=
    (eL.toMonoidHom.comp (inclusion hKL)).comp eK.symm.toMonoidHom
  have hf : Function.Injective f :=
    eL.injective.comp ((inclusion_injective hKL).comp eK.symm.injective)
  have hn2 := rankOne_degree_of_seven_embedding hn hF f hf
  have hcard : Nat.card F = 4 := by simpa [hn2] using hF
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard
  exact ⟨hn2, ⟨eK.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans e)⟩⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.ComponentSource
