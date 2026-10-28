module
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.LocalStructure
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# The exceptional Ree quartet is a Suzuki Sylow subgroup

Over the eight-element field, the literal fifth Ree root block has order 64.
Its two-coordinate parametrization is bijective by uniqueness of the positive
root word. The prescribed Suzuki Levi contains a conjugate of this two-group;
its order identifies it as a Suzuki Sylow subgroup. Sylow conjugacy therefore
identifies the embedded standard Suzuki root with a conjugate of the fifth
block in the original Ree carrier.

For an arbitrary surjection onto that carrier, lift the conjugating element
to transport the fifth-block triple-commutator identity to the exact embedded
Suzuki root preimage. The ambient commutator calculation is retained as its
source premise, for discharge by `EightAmbient`.

Source: GLS3 §§2.3--2.4, Table 2.4 and 2.4.5(d); the exceptional q=8 step in
Aschbacher--Smith I.1.1--4, printed pp.407--408.
-/

open Subgroup
open scoped Pointwise
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
open ElementaryTwoBound ElementaryTwoBound.RootCalculations
open NormalizedRootCentralizers.CenterExponent
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics.RadicalCoordinates.FixedCoordinates
open BenderSuzuki.MatrixGroups

private theorem blockPoint_five_injective (m : ℕ) :
    Function.Injective (fun ab : CoefficientField m × CoefficientField m =>
      blockPoint m 4 ab.1 ab.2) := by
  classical
  let pack (a b : CoefficientField m) : PositiveParameters m :=
    ⟨fun _ => 0, Function.update (fun _ => 0) 1 a, Function.update (fun _ => 0) 1 b⟩
  have hw (a b : CoefficientField m) : wordElement m (pack a b) =
      blockPoint m 4 a b := by
    simp [wordElement, pack, blockPoint, pairCount, quartetCount,
      positive_quartet_indices, List.ofFn_succ]
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hp := wordElement_injective m ((hw a b).trans (h.trans (hw c d).symm))
  apply Prod.ext
  · simpa [pack] using congrArg (fun p => p.main 1) hp
  · simpa [pack] using congrArg (fun p => p.central 1) hp

/-- The fifth source root block has two independent field coordinates. -/
public theorem root_five_card (m : ℕ) : Nat.card (X m 4) = (2 ^ (2 * m + 1)) ^ 2 := by
  let point : CoefficientField m × CoefficientField m → X m 4 :=
    fun ab => ⟨blockPoint m 4 ab.1 ab.2, (mem_X_even m 4 (by decide) _).mpr ⟨ab.1,ab.2,rfl⟩⟩
  have hp : Function.Bijective point := by
    refine ⟨fun a b h => blockPoint_five_injective m (congrArg Subtype.val h), ?_⟩
    intro x
    obtain ⟨a,b,h⟩ := (mem_X_even m 4 (by decide) x.val).mp x.property
    exact ⟨(a,b), Subtype.ext h⟩
  rw [← Nat.card_congr (Equiv.ofBijective point hp), Nat.card_prod, field_card, pow_two]

/-- At the eight-element field, the embedded Suzuki root subgroup is a
conjugate of the literal fifth Ree root block. -/
public theorem embedded_suzuki_root_eq_conjugate_five :
    ∃ g : Model 1, (SuzukiRootSubgroup 1).map (suzukiEmbedding 1) =
      (X 1 4).map (MulAut.conj g).toMonoidHom := by
  classical
  have hindex : rootIndex (.inr (1 : Fin 4)) = 4 := by
    change positiveRootWordLayout.quartetIndex (1 : Fin 4) = 4
    rw [positive_quartet_indices]
    rfl
  obtain ⟨n, hn⟩ := quartet_le_conjugate_suzuki 1 (1 : Fin 4)
  rw [hindex] at hn
  let f : SuzukiMatrixGroup 1 →* Model 1 :=
    (MulAut.conj n).toMonoidHom.comp (suzukiEmbedding 1)
  have hf : Function.Injective f := (MulAut.conj n).injective.comp (suzukiEmbedding_injective 1)
  have hXf : X 1 4 ≤ f.range := by
    rw [MonoidHom.range_comp]
    exact hn
  let K := (X 1 4).comap f
  have hKmap : K.map f = X 1 4 := map_comap_eq_self hXf
  have hKcard : Nat.card K = 64 := by
    rw [Nat.card_congr (equivMapOfInjective K f hf).toEquiv, hKmap, root_five_card]
    norm_num
  have hXtwo : IsPGroup 2 (X 1 4) :=
    (Parabolics.unipotent_isPGroup 1).of_injective
      (inclusion (X_le_unipotent 1 4)) (inclusion_injective _)
  have hKtwo : IsPGroup 2 K := hXtwo.comap_of_injective f hf
  obtain ⟨P, hKP⟩ := hKtwo.exists_le_sylow
  obtain ⟨Q, hQ⟩ := suzukiRootSubgroup_isSylow 1 (by decide)
  have hQcard : Nat.card Q = 64 := by
    rw [hQ, suzukiRootSubgroup_card 1 (by decide)]
    norm_num
  have hPeq : K = (P : Subgroup (SuzukiMatrixGroup 1)) :=
    eq_of_le_of_card_ge hKP (by rw [Nat.card_congr (P.equiv Q).toEquiv, hQcard, hKcard])
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup 1) P Q
  have hKQ : K.map (MulAut.conj k).toMonoidHom = SuzukiRootSubgroup 1 := by
    rw [hPeq, ← hQ]
    exact congrArg Sylow.toSubgroup hk
  refine ⟨suzukiEmbedding 1 k * n⁻¹, ?_⟩
  rw [← hKQ, ← hKmap, map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  change suzukiEmbedding 1 (k * x * k⁻¹) =
    (suzukiEmbedding 1 k * n⁻¹) * (n * suzukiEmbedding 1 x * n⁻¹) *
      (suzukiEmbedding 1 k * n⁻¹)⁻¹
  simp only [map_mul, map_inv]
  group

open scoped commutatorElement

/-- Lift conjugacy through the original surjection to transport the actual
fifth-block triple-commutator identity to the prescribed Suzuki root subgroup. -/
public theorem liftedRootClassTwo_of_fifth_block
    {E : Type*} [Group E] (f : E →* Model 1) (hf : Function.Surjective f)
    (hc : ∀ a b c : E, f a ∈ X 1 4 → f b ∈ X 1 4 → f c ∈ X 1 4 →
      ⁅⁅a,b⁆,c⁆ = 1) : LiftedRootClassTwo 1 f := by
  obtain ⟨g, hg⟩ := embedded_suzuki_root_eq_conjugate_five
  obtain ⟨v, hv⟩ := hf g
  let e := MulAut.conj v⁻¹
  have hmem (a : E) (ha : f a ∈ (SuzukiRootSubgroup 1).map (suzukiEmbedding 1)) :
      f (e a) ∈ X 1 4 := by
    rw [hg] at ha
    obtain ⟨b, hb, he⟩ := ha
    have heq : f (e a) = b := by
      change f (v⁻¹ * a * (v⁻¹)⁻¹) = b
      rw [map_mul, map_mul, map_inv, inv_inv, hv, ← he]
      change g⁻¹ * (g * b * g⁻¹) * g = b
      group
    exact heq ▸ hb
  intro a b c ha hb hc'
  apply e.injective
  simpa only [map_commutatorElement, map_one] using
    hc (e a) (e b) (e c) (hmem a ha) (hmem b hb) (hmem c hc')

end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
