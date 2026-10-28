module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Residuals
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.BorelLift
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.SL2.EvenBorelResidual.FieldInvolution
public import Theory.SpecificGroups.PSL3.CartanActions.OddDegree
public import Theory.FieldTheory.BinaryTorusInvolution

/-!
# Intrinsic Borel calculations used in the higher-field reduction

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955.

The imported rank-one calculation identifies the Borel at a specified Sylow
two-subgroup, its two-core, and its actual quotient torus. The maps below
transport the odd/even degree calculations through surjective maps with
two-group kernel to the source's lifted Borel. The lift is not identified
with the model Borel. In odd degree, both the L₂ and L₃ calculations make
its two-residual three-prime; the
published residual containment then makes it centralize V.

The imported assembly proves the full intrinsic actor trichotomy and outer
commutator restriction for all seven actual carriers, under the explicitly
typed earlier automorphism-classification inputs. Its model witnesses contain
genuine group equivalences. Special and projective linear and unitary carriers
are retained separately; the unitary matrix field has order (2ⁿ)². An outer
fixer with commutator quotient of order at most three leaves exactly L₂(4),
(S)L₃(4), or (S)U₃(8).

The ambient fixer is the embedded Sylow joined with C_T(K). The literal
source equality requires the kernel control characterized in the assembly;
it is not inferred from the action image alone. The remaining local B_C,
external-X and final source exclusion arguments belong to HigherFieldReduction.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_threePrime (B₀ : Subgroup G)
    (h : Nat.Coprime 3 (Nat.card B₀)) :
    Nat.Coprime 3 (Nat.card (borelResidual B₀)) :=
  h.of_dvd_right (card_dvd_of_le (map_subtype_le _))

/-- A two-group kernel preserves three-prime order. This applies to a
lifted Borel; the lift need not be isomorphic to its star image. -/
private theorem threePrime_of_twoKernel {D E : Type*} [Group D] [Group E]
    [Finite D] (f : D →* E) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (hE : Nat.Coprime 3 (Nat.card E)) :
    Nat.Coprime 3 (Nat.card D) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  rw [← f.ker.card_mul_index, index_ker, MonoidHom.range_eq_top.mpr hf, card_top, hk]
  exact ((by decide : Nat.Coprime 3 2).pow_right k).mul_right hE

/-- The source rank-one B has order prime to three in odd field degree. -/
theorem linearTwo_odd_threePrime
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (B₀ : Subgroup G)
    (f : B₀ →* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nat.Coprime 3 (Nat.card (borelResidual B₀)) := by
  apply residual_threePrime
  apply threePrime_of_twoKernel f hf hker
  exact Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_threePrime_of_odd F hF hn

/-- Even degree supplies a factor three in O² of the lifted Borel.
No identification of the lift with the model Borel is used. -/
theorem linearTwo_even_three_dvd
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (heven : Even n) (B₀ : Subgroup G)
    (f : B₀ →* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F)
    (hf : Function.Surjective f) :
    3 ∣ Nat.card (borelResidual B₀) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ n by omega)
  have hmap : (pResidual 2 B₀).map f = ⊤ := by
    rw [map_pResidual_of_surjective 2 f hf,
      Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_twoResidual F hq]
  have hd := (pResidual 2 B₀).card_map_dvd f
  rw [hmap, card_top] at hd
  have ht := ((Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.three_dvd_card_torus_iff
    F hF).mpr heven).trans (card_dvd_of_le
      (show Matrix.ProjectiveSpecialLinearGroup.OddBorel.complement F ≤
        Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F from le_sup_right))
  rw [borelResidual, residualIn,
    ← Nat.card_congr ((pResidual 2 B₀).equivMapOfInjective B₀.subtype B₀.subtype_injective).toEquiv]
  exact ht.trans hd

/-- The odd-degree L₃ Borel calculation retains the genuine central quotient. -/
theorem linearThree_odd_threePrime
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (B₀ : Subgroup G)
    (f : B₀ →* Matrix.PSL3.LinearThree.borel F)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker) :
    Nat.Coprime 3 (Nat.card (borelResidual B₀)) := by
  apply residual_threePrime
  apply threePrime_of_twoKernel f hf hker
  exact Matrix.PSL3.CartanActions.OddDegree.borel_threePrime F hF hn

/-- Odd rank-one degree discharges the order premise of the source
three-residual centralization step. -/
theorem linearTwo_odd_centralizes
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (B₀ C V : Subgroup G)
    (f : B₀ →* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hR : residualIn 3 (borelResidual B₀) ≤ C) (hC : C ≤ centralizer (V : Set G)) :
    borelResidual B₀ ≤ centralizer (V : Set G) :=
  borel_centralizes_of_threePrime _ C V (linearTwo_odd_threePrime hF hn B₀ f hf hker) hR hC

/-- The same source centralization step for odd-degree L₃. -/
theorem linearThree_odd_centralizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n) (B₀ C V : Subgroup G)
    (f : B₀ →* Matrix.PSL3.LinearThree.borel F)
    (hf : Function.Surjective f) (hker : IsPGroup 2 f.ker)
    (hR : residualIn 3 (borelResidual B₀) ≤ C) (hC : C ≤ centralizer (V : Set G)) :
    borelResidual B₀ ≤ centralizer (V : Set G) :=
  borel_centralizes_of_threePrime _ C V (linearThree_odd_threePrime hF hn B₀ f hf hker) hR hC

/-- Three-prime order descends to the two-residual of the actual source lift. -/
theorem borelLift_threePrime_of_image (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K)
    (hcard : Nat.Coprime 3 (Nat.card B₀star)) :
    Nat.Coprime 3 (Nat.card (borelResidual (borelLift H K hKH B₀star))) :=
  residual_threePrime _ (threePrime_of_twoKernel (borelStarProjection H K hKH B₀star hB)
    (borelStarProjection_surjective H K hKH B₀star hB)
    (borelStarProjection_ker_isTwoGroup H K hKH B₀star hB) hcard)

/-- Odd L₂ degree, with the two-kernel of the source projection discharged. -/
theorem linearTwo_star_odd_threePrime
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n)
    (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K)
    (e : B₀star ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) :
    Nat.Coprime 3 (Nat.card (borelResidual (borelLift H K hKH B₀star))) := by
  apply borelLift_threePrime_of_image H K hKH B₀star hB
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.borel_threePrime_of_odd F hF hn

/-- Even L₂ degree for the source lift, with no assumption on its two-kernel. -/
theorem linearTwo_star_even_three_dvd
    {F : Type*} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2 ^ n) (heven : Even n)
    (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K)
    (e : B₀star ≃* Matrix.ProjectiveSpecialLinearGroup.OddBorel.borel F) :
    3 ∣ Nat.card (borelResidual (borelLift H K hKH B₀star)) :=
  linearTwo_even_three_dvd hn hF heven _
    (e.toMonoidHom.comp (borelStarProjection H K hKH B₀star hB))
    (e.surjective.comp (borelStarProjection_surjective H K hKH B₀star hB))

/-- Odd L₃ degree, retaining both the projective scalar quotient and the
two-kernel of the source lift. -/
theorem linearThree_star_odd_threePrime
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Odd n)
    (H K : Subgroup G) (hKH : K ≤ H)
    (B₀star : Subgroup (Source.Hstar H)) (hB : B₀star ≤ Source.starImage H K)
    (e : B₀star ≃* Matrix.PSL3.LinearThree.borel F) :
    Nat.Coprime 3 (Nat.card (borelResidual (borelLift H K hKH B₀star))) := by
  apply borelLift_threePrime_of_image H K hKH B₀star hB
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.PSL3.CartanActions.OddDegree.borel_threePrime F hF hn

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels
