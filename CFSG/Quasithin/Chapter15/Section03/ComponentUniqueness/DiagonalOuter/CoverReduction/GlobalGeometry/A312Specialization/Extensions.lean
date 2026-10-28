module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization.Quotient
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings

/-!
# Normal-kernel exclusions in the A.3.12 specialization

Every normal p-subgroup of a finite quasisimple group is central. Hence a
quasisimple group with center of order at most four admits none of the large
normal p-kernels in A.3.12. The cyclic-four central-product case is handled
using its actual commuting factors, without assuming the extension splits.
The noncentral odd-core alternatives are excluded by quasisimplicity and
even order, without an odd-order theorem.

Source: Aschbacher--Smith, A.3.12(10),(12),(14),(16)--(22), pp.47--48,
as applied on printed p.1136.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
open Chapter1.Section02.LocalModels
universe u
variable {X : Type u} [Group X] [Finite X] [IsQuasisimple X]

theorem normal_pGroup_card_le (hZ : Nat.card (center X) ≤ 4)
    {p : ℕ} [Fact p.Prime] (N : Subgroup X) [N.Normal] (hp : IsPGroup p N) :
    Nat.card N ≤ 4 := by
  have hN : N ≤ pCore p X := le_sSup ⟨inferInstance, hp⟩
  exact (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le (hN.trans (IsQuasisimple.pCore_le_center p)))).trans hZ

/-- The normal kernel alone excludes these extensions, regardless of quotient. -/
theorem no_large_pGroup_extension (hZ : Nat.card (center X) ≤ 4)
    {p : ℕ} [Fact p.Prime] (kernel quotient : GroupClass.{u})
    (hk : ∀ (N : Type u) [Group N] [Finite N], kernel N → IsPGroup p N ∧ 4 < Nat.card N) :
    ¬ HasExtension X kernel quotient := by
  rintro ⟨N, hn, hN, _⟩
  let := hn
  obtain ⟨hp, hc⟩ := hk N hN
  exact (not_lt_of_ge (normal_pGroup_card_le hZ N hp)) hc

theorem no_elementary_extension (hZ : Nat.card (center X) ≤ 4)
    {p r : ℕ} [Fact p.Prime] (hr : 4 < p ^ r) (quotient : GroupClass.{u}) :
    ¬ HasExtension X (ElementaryModel p r) quotient := by
  apply no_large_pGroup_extension hZ (p := p) _ quotient
  intro N _ _ hN
  obtain ⟨e⟩ := hN
  have hc : Nat.card N = p ^ r := by
    rw [Nat.card_congr e.toEquiv]
    simp
  exact ⟨IsPGroup.of_card hc, hc ▸ hr⟩

theorem no_extraspecial_extension (hZ : Nat.card (center X) ≤ 4)
    {p n : ℕ} [Fact p.Prime] (hn : 4 < p ^ (1 + 2 * n)) (quotient : GroupClass.{u}) :
    ¬ HasExtension X (ExtraspecialModel p n) quotient := by
  apply no_large_pGroup_extension hZ (p := p) _ quotient
  intro N _ _ hN
  exact ⟨IsPGroup.of_card hN.2, hN.2 ▸ hn⟩

/-- The central product is a two-group of order at least that of its
extraspecial factor. Its source intersection convention is retained. -/
theorem no_cyclicFour_extension (hZ : Nat.card (center X) ≤ 4)
    (quotient : GroupClass.{u}) :
    ¬ HasExtension X (CyclicFourCentralProduct 2) quotient := by
  apply no_large_pGroup_extension hZ (p := 2) _ quotient
  intro N _ _ hN
  obtain ⟨C, E, ⟨e⟩, hE, hgen, hcomm, _⟩ := hN
  have hC : IsPGroup 2 C := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_congr e.toEquiv]
    norm_num)
  have hEp : IsPGroup 2 E := IsPGroup.of_card hE.2
  have hp := hC.to_sup_of_normal_right' hEp
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (Subgroup.centralizer_le_normalizer _))
  rw [hgen] at hp
  have hc : 4 < Nat.card E := by rw [hE.2]; norm_num
  exact ⟨hp.of_equiv topEquiv, hc.trans_le E.card_le_card_group⟩

theorem no_homocyclicFour_extension (hZ : Nat.card (center X) ≤ 4)
    (quotient : GroupClass.{u}) :
    ¬ HasExtension X
      (fun N _ => Nonempty (N ≃* Multiplicative (Fin 3 → ZMod 4))) quotient := by
  apply no_large_pGroup_extension hZ (p := 2) _ quotient
  intro N _ _ hN
  obtain ⟨e⟩ := hN
  have hc : Nat.card N = 64 := by rw [Nat.card_congr e.toEquiv]; simp
  exact ⟨IsPGroup.of_card (n := 6) (by simpa using hc), by omega⟩

/-- The odd core is central whenever the finite quasisimple group has even order. -/
theorem oddCore_central (heven : 2 ∣ Nat.card X) :
    ⁅pPrimeCore 2 X, (⊤ : Subgroup X)⁆ = ⊥ := by
  apply commutator_top_right_eq_bot_iff_le_center.mpr
  rcases IsQuasisimple.normal_le_center_or_eq_top (pPrimeCore 2 X) with hc | ht
  · exact hc
  · have hcop := pPrimeCore_coprime_card (p := 2) (G := X)
    rw [ht, card_top] at hcop
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop heven).elim

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
