module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.CommutatorPrimes
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

/-!
# The source Cartan argument

The natural covered action supplies the cubic marked quotients and an actual
inverter in T ∩ L. The moving component coordinates transport these to the
Borel torus. Its displacement is an image of [O²(B₀),s], whose prime divisors
are two and three. Thus the cyclic odd Cartan factor is a three-group; its
order 2ⁿ − 1 and even n force n = 2. The theta identity then identifies L₁
with the embedded two-residual of B₀.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969;
Notation 13.2.1 and the earlier factorization 13.2.2(3), printed p.877.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
variable {G : Type*} [Group G] [Finite G]
variable (H K T : Subgroup G) (hTH : T ≤ H) {t : G} (ht : t ∈ T)
  (hK : K ⊔ K.conjBy t ≤ H)
  (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
  (htn : t ∉ normalizer (K : Set G))
  (e : Source.starImage H (K ⊔ K.conjBy t) ≃*
    Source.starImage H K × Source.starImage H K)
  (he : ∀ a b, (e.symm (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
    (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩ * b *
      (QuotientGroup.mk' (pCore 2 H) ⟨t, hTH ht⟩)⁻¹))
  (S : Sylow 2 (Source.starImage H (K ⊔ K.conjBy t)))
  {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
local notation "B₀" => SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S
local notation "C" => SourceActions.CommonTorus H (K ⊔ K.conjBy t) e S
local notation "Z" => SourceActions.D₀ H (K ⊔ K.conjBy t) hK e S hn hmodel
local notation "P" => SourceActions.Dplus H (K ⊔ K.conjBy t) hK e S hn hmodel
variable {L V V₁ V₃ : Subgroup G} (d : LocalAction.NaturalSetup L T V V₁ V₃)
  (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
  (hLB : one L T V₁ ≤ SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S)
  (hTB : T ≤ normalizer (SourceTorus.chosenLift H (K ⊔ K.conjBy t) hK S : Set G))

include hi htn he d hfactor hLB hTB hn hmodel in
/-- The diagonal statements concern the actual torus images, canonically
identified with the intrinsic two-core quotients by markedQuotientEquiv.
No claim of injectivity on the entire marked groups is made. -/
theorem marked_diagonals :
    Function.Injective (fun x : Z L => (x : C × C).1) ∧
    Function.Injective (fun x : Z L => (x : C × C).2) ∧
    Function.Injective (fun x : P L T V₁ => (x : C × C).1) ∧
    Function.Injective (fun x : P L T V₁ => (x : C × C).2) ∧
    (Z L).map (MonoidHom.fst C C) = (P L T V₁).map (MonoidHom.fst C C) ∧
    (Z L).map (MonoidHom.snd C C) = (P L T V₁).map (MonoidHom.snd C C) := by
  obtain ⟨s, hinv, _⟩ := d.exists_plus_inverter hfactor
  obtain ⟨hcyc, _, hτ, _, hz, hp, hτz, hτp, _, _⟩ :=
    SourceActions.source_actions H K T hTH ht hK hi htn e he S hn hmodel L V₁ hLB
      (LocalAction.zero_le_one_of_factorization L T V₁ hfactor)
      (plus_le_one L T V₁ d.line_stable) hTB
      (d.normalizes_L.trans (normalizer_le_zero_normalizer L))
      (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable)
      d.zero_core_card (d.plus_core_card hfactor) s.property hinv
  let := hcyc
  exact ⟨CartanAction.fst_injective _ hτ _ hz hτz,
    CartanAction.snd_injective _ hτ _ hz hτz,
    CartanAction.fst_injective _ hτ _ hp hτp,
    CartanAction.snd_injective _ hτ _ hp hτp,
    CartanAction.projected_images_eq _ hτ _ _ hz hp hτz hτp⟩

include hi htn he d hfactor hLB hTB hn hmodel in
/-- The source commutator and inverter force the Cartan three-power and n = 2.
Every cubic-image, factor-action, and displacement hypothesis is discharged. -/
theorem parameter_two (heven : Even n)
    (hBL : B₀ ≤ normalizer (L : Set G)) (hBV : B₀ ≤ normalizer (V₁ : Set G)) :
    (∃ a : ℕ, 2 ^ n - 1 = 3 ^ a) ∧ n = 2 := by
  obtain ⟨s, hinv, _⟩ := d.exists_plus_inverter hfactor
  obtain ⟨hcyc, hodd, hτ, hα, hz, hp, hτz, hτp, hfix, hinvert⟩ :=
    SourceActions.source_actions H K T hTH ht hK hi htn e he S hn hmodel L V₁ hLB
      (LocalAction.zero_le_one_of_factorization L T V₁ hfactor)
      (plus_le_one L T V₁ d.line_stable) hTB
      (d.normalizes_L.trans (normalizer_le_zero_normalizer L))
      (T_normalizes_plus L T V₁ d.normalizes_L d.line_stable)
      d.zero_core_card (d.plus_core_card hfactor) s.property hinv
  let := hcyc
  have hq : IsPGroup 3 (one L T V₁ ⧸ pCore 2 (one L T V₁)) :=
    IsPGroup.iff_card.mpr ⟨2, by simpa using d.one_quotient_card hfactor⟩
  have hpr := commutator_primes_of_source_parabolic L (one L T V₁) T V₁ B₀
    (SourceActions.residualBorel H (K ⊔ K.conjBy t) hK S) rfl hq
    (map_subtype_le _) hBL hBV s.property.2 (hTB s.property.1)
  have hdisp := SourceActions.displacement_primes H (K ⊔ K.conjBy t) hK e S hn hmodel
    ⟨s.val, hTB s.property.1⟩ (fun p => p = 2 ∨ p = 3) hpr
  obtain ⟨a, ha⟩ := CartanAction.three_power_of_markings _ _ hτ hα _ _
    hz hp hτz hτp hfix hinvert hodd hdisp
  have hpower : ∃ a : ℕ, 2 ^ n - 1 = 3 ^ a :=
    ⟨a, (BinaryBorel.torus_card hn hmodel _).symm.trans ha⟩
  exact ⟨hpower, parameter_eq_two_of_torus_three_power hn heven hpower⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SourceConclusion
end
