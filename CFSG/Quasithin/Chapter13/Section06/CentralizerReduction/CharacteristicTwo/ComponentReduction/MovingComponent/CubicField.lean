module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.CubicAction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Constructing the cubic Suzuki field action

Suppose D is two-perfect, D/O₂(D) has order three, and D acts nontrivially
on a component K whose central quotient has an actual Suzuki matrix model.
A cubic complement to O₂(D) acts nontrivially: otherwise the action image
would be a two-group, contradicting two-perfectness. Faithfulness on the
perfect central quotient retains this nontrivial action even for central covers.

Inner-field coverage and the three-free order of the Suzuki group imply that
the field subgroup has index prime to three in the full automorphism group.
A Sylow three-subgroup of the field subgroup is therefore Sylow in the full
automorphism group. Sylow conjugacy puts the cubic action into the literal
entrywise field subgroup. Composing the original model equivalence with that
conjugating automorphism constructs the required coordinates, with the same
matrix parameter. Injectivity of the field action preserves order three.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 13.6.6,
printed p.927, the moving Suzuki component branch. The field degree is 2*n+1;
n=1 (source m=3) and nontrivial centers are included. The subsequent paired
component and Borel arguments are separate from this intrinsic construction.
-/

public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent

private theorem cubic_image {D A : Type*} [Group D] [Finite D] [Group A]
    (hD : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 3)
    (f : D →* A) (hf : f ≠ 1) :
    ∃ c : D, orderOf c = 3 ∧ orderOf (f c) = 3 := by
  obtain ⟨c, hc3, hgen⟩ := exists_prime_order_sup_pCore_eq_top
    (show Nat.Coprime 2 3 by decide) hc
  have hne : f c ≠ 1 := by
    intro he
    have hsub : (⊤ : Subgroup D) ≤ f.ker ⊔ pCore 2 D := by
      rw [← hgen]
      exact sup_le_sup (zpowers_le.mpr he) le_rfl
    have htop : IsPPerfect 2 (⊤ : Subgroup D) := hD.of_surjective
      (topEquiv (G := D)).symm.toMonoidHom (topEquiv (G := D)).symm.surjective
    have hk := le_normal_of_isPPerfect_of_le_sup_pGroup (⊤ : Subgroup D)
      f.ker (pCore 2 D) htop pCore_isPGroup hsub
    apply hf
    ext d
    exact hk (show d ∈ (⊤ : Subgroup D) from trivial)
  refine ⟨c, hc3, ?_⟩
  have hd : orderOf (f c) ∣ 3 := hc3 ▸ orderOf_map_dvd f c
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact (hne (orderOf_eq_one_iff.mp h)).elim
  · exact h

private theorem field_index_three_free (n : ℕ) (hn : 1 ≤ n) :
    ¬ 3 ∣ (suzukiFieldAutHom n).range.index := by
  let I := (MulAut.conj : SuzukiMatrixGroup n →* MulAut (SuzukiMatrixGroup n)).range
  let F := (suzukiFieldAutHom n).range
  have hcover : I ⊔ F = ⊤ := by
    apply top_unique
    intro α _
    obtain ⟨g, σ, rfl⟩ := suzukiAut_eq_inner_mul_field n hn α
    exact mul_mem_sup (show MulAut.conj g ∈ I from ⟨g, rfl⟩)
      (show suzukiFieldAut n σ ∈ F from ⟨σ, suzukiFieldAutHom_apply n σ⟩)
  have hcard := card_mul_eq_card_inf_mul_card_sup_of_normalizes I F
    (show F ≤ normalizer (I : Set (MulAut (SuzukiMatrixGroup n))) from
      le_normalizer_of_normal)
  rw [hcover, Nat.card_congr (topEquiv (G := MulAut (SuzukiMatrixGroup n))).toEquiv] at hcard
  have hI : Nat.card I =
      Nat.card (I ⊓ F : Subgroup (MulAut (SuzukiMatrixGroup n))) * F.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := F))
    calc
      Nat.card I * Nat.card F = Nat.card (I ⊓ F : Subgroup _) *
          Nat.card (MulAut (SuzukiMatrixGroup n)) := hcard
      _ = (Nat.card (I ⊓ F : Subgroup _) * F.index) * Nat.card F := by
        rw [← F.index_mul_card]
        ac_rfl
  intro hd
  apply suzukiMatrixGroup_three_free n (by omega)
  apply dvd_trans _ (card_range_dvd (MulAut.conj : SuzukiMatrixGroup n →* _))
  change 3 ∣ Nat.card I
  rw [hI]
  exact dvd_mul_of_dvd_right hd _

private theorem cubic_field_conjugate (n : ℕ) (hn : 1 ≤ n)
    (α : MulAut (SuzukiMatrixGroup n)) (hα : orderOf α = 3) :
    ∃ (β : MulAut (SuzukiMatrixGroup n))
      (σ : BinaryGaloisField (2 * n + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * n + 1)),
      orderOf σ = 3 ∧ β * α * β⁻¹ = suzukiFieldAut n σ := by
  let F := (suzukiFieldAutHom n).range
  let Q : Sylow 3 F := Sylow.nonempty.some
  have hidx : ¬ 3 ∣ ((Q : Subgroup F).map F.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_three.not_dvd_mul Q.not_dvd_index (field_index_three_free n hn)
  let P : Sylow 3 (MulAut (SuzukiMatrixGroup n)) :=
    (Q.isPGroup'.map F.subtype).toSylow hidx
  have hPF : (P : Subgroup (MulAut (SuzukiMatrixGroup n))) ≤ F := map_subtype_le _
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hα)
  obtain ⟨β, hβ⟩ := isConj_iff.mp hy
  obtain ⟨σ, hσ⟩ := hPF y.property
  rw [suzukiFieldAutHom_apply] at hσ
  have he : β * α * β⁻¹ = suzukiFieldAut n σ := hβ.trans hσ.symm
  refine ⟨β, σ, ?_, he⟩
  rw [← orderOf_injective (suzukiFieldAutHom n) (suzukiFieldAutHom_injective n) σ]
  rw [suzukiFieldAutHom_apply, ← he]
  exact (MulAut.conj β).orderOf_eq α |>.trans hα

/-- Composing the model coordinates conjugates the literal normalizer action. -/
theorem modelAction_trans {H S : Type*} [Group H] [Group S]
    (K D : Subgroup H) (hn : D ≤ normalizer (K : Set H))
    (e : NormalizerAction.componentImage K ≃* S) (β : MulAut S) (d : D) :
    modelAction K D hn (e.trans β) d = β * modelAction K D hn e d * β⁻¹ := by
  ext x
  rfl

/-- A cubic element of the actual actor has order-three action on the component
model. This uses the two-core quotient and two-perfectness of D, and remains
valid when K has nontrivial center. -/
theorem exists_cubic_modelAction {H S : Type*} [Group H] [Finite H] [Group S]
    (K D : Subgroup H) (hK : IsComponent H K)
    (hn : D ≤ normalizer (K : Set H))
    (hD : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 3)
    (hm : ⁅K, D⁆ ≠ ⊥) (e : NormalizerAction.componentImage K ≃* S) :
    ∃ c : D, orderOf c = 3 ∧ orderOf (modelAction K D hn e c) = 3 := by
  have hf : modelAction K D hn e ≠ 1 := by
    intro hf
    apply hm
    rw [commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro d hd
    apply (modelAction_eq_one_iff K D hK hn e ⟨d, hd⟩).mp
    rw [hf]
    rfl
  exact cubic_image hD hc (modelAction K D hn e) hf

/-- The intrinsic cubic-field construction used in the moving Suzuki branch of
13.6.6. The new equivalence has the original matrix parameter; both later product
factors can therefore use this same equivalence and its literal cubic action. -/
theorem exists_cubicFieldAction {H : Type*} [Group H] [Finite H]
    (K D : Subgroup H) (hK : IsComponent H K)
    (hn : D ≤ normalizer (K : Set H))
    (hD : IsPPerfect 2 D) (hc : Nat.card (D ⧸ pCore 2 D) = 3)
    (hm : ⁅K, D⁆ ≠ ⊥) (n : ℕ) (hpos : 1 ≤ n)
    (e0 : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n) :
    ∃ eK : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n,
      Nonempty (CubicFieldAction K D hn n eK) := by
  obtain ⟨c, hc3, ha3⟩ := exists_cubic_modelAction K D hK hn hD hc hm e0
  obtain ⟨β, σ, hσ, he⟩ := cubic_field_conjugate n hpos (modelAction K D hn e0 c) ha3
  refine ⟨e0.trans β, ⟨⟨c, hc3, σ, hσ, ?_⟩⟩⟩
  rw [modelAction_trans]
  exact he

/-- The constructed field action forces three to divide the source field degree. -/
theorem CubicFieldAction.three_dvd_degree {H : Type*} [Group H]
    {K D : Subgroup H} {hn : D ≤ normalizer (K : Set H)}
    {n : ℕ} {eK : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n}
    (a : CubicFieldAction K D hn n eK) : 3 ∣ 2 * n + 1 := by
  rw [← suzukiFieldAut_card n, ← a.field_order]
  exact orderOf_dvd_natCard a.field

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
