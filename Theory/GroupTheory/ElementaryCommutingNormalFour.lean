module
public import Theory.GroupTheory.ElementaryCommutingConnectivity
public import Theory.GroupAction.SubgroupConjugation
public import Theory.Representation.CardFourTwoGroupImage

/-!
# Commuting paths through a normalized four-group

An elementary abelian two-subgroup A of order at least eight belongs to
the same rank-two commuting component as every elementary four-subgroup
E that it normalizes. The action of A on E has image of order at most two,
so its kernel has order at least four. The ambient image B of this kernel
commutes with both A and E, giving the path A, B, E.

This is the normal-four-group step in GLS2, Lemmas 10.20 and 10.21
(`refs/KGroup/GLS2/ChapterC.tex`). It does not require a global connectivity
hypothesis, or assert that a normal four-group exists in a given two-group.
-/

namespace Subgroup
open scoped IsMulCommutative

/-- A rank-three elementary subgroup is connected to each four-group
that it normalizes, through the kernel of its action on that four-group. -/
public theorem elementaryCommutingConnected_of_normalizes_four
    {G : Type*} [Group G] [Finite G]
    (A E : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E]
    (hA : 8 ≤ Nat.card A) (hE : Nat.card E = 4)
    (hAE : A ≤ normalizer (E : Set G)) :
    ElementaryCommutingConnected 2 A E := by
  let _ := conjMulDistribMulActionOfLeNormalizer A E hAE
  let f : A →* MulAut E := MulDistribMulAction.toMulAut A E
  have himage : Nat.card f.range ≤ 2 :=
    Representation.card_action_image_le_two_of_card_four
      (IsElementaryAbelian.isPGroup 2 A) hE
  have hker : 4 ≤ Nat.card f.ker := by
    have hcard := f.ker.card_mul_index
    rw [index_ker] at hcard
    nlinarith
  let B : Subgroup G := f.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  let _ : IsElementaryAbelian 2 f.ker := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) x) }
  let _ : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hB : 4 ≤ Nat.card B := by
    simpa only [B, card_map_of_injective A.subtype_injective] using hker
  have hAB : A ≤ centralizer (B : Set G) := by
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)
  have hBE : B ≤ centralizer (E : Set G) := by
    rintro b ⟨x, hx, rfl⟩ e he
    have hfix : f x (⟨e, he⟩ : E) = ⟨e, he⟩ := by
      rw [MonoidHom.mem_ker.mp hx]
      rfl
    have hfixG := congrArg Subtype.val hfix
    change (x : G) * e * (x : G)⁻¹ = e at hfixG
    exact (mul_inv_eq_iff_eq_mul.mp hfixG).symm
  exact (ElementaryCommutingAdjacent.connected
    ⟨inferInstance, by omega, inferInstance, hB, hAB⟩).trans
      (ElementaryCommutingAdjacent.connected
        ⟨inferInstance, hB, inferInstance, by omega, hBE⟩)

end Subgroup
