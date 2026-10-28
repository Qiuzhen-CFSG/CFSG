module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve.Exceptional.Transport
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedSylowCenter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup

/-!
# G₂ branches of the initial binary sieve

For even fields larger than two, the intrinsic Sylow-fixer calculation puts
the marked four-group inside K*, conditional only on full inner–field
automorphism coverage. That independent coverage theorem is still owned by
qt-f-01-g2-inner-field-coverage. The action used here is on K/Z(K), so the
nontrivial central-cover case at field order four is retained.

For the literal derived subgroup G₂(2)′, automorphism coverage is proved.
Move the fixed four-group to the standard Sylow. Each fixer is induced by a
central square-one element, hence by the distinguished subgroup of order two.
Its image cannot contain the faithful four-group.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927; intrinsic fixer
geometry is 16.1.6, printed p.1172. G₂ coordinates use the licensed ATLAS
port; see LICENSES/ATLAS.txt.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
open A5Module ClassificationModels
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- The large G₂ branch, with its independently owned intrinsic coverage premise. -/
theorem largeField_of_g2_of_coverage
    (coverage : ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
      2 < Nat.card F → Function.Surjective (semilinearAction (F := F)))
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) {m : ℕ} (hm : 2 ≤ m)
    (hi : IsG2At (NormalizerAction.componentImage K) (2 ^ m)) :
    LargeField K a := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hi
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (by decide : 2 < 2 ^ 2).trans_le (Nat.pow_le_pow_right (by decide) hm)
  refine ⟨m, by omega, .g2 m hm ⟨F, inferInstance, inferInstance, hF, ⟨e⟩⟩,
    EStar_le_component_of_model_fixers K hK a e ?_⟩
  intro S α hfix
  obtain ⟨x, _, hx⟩ := EvenInvolutionGeometry.fixing_sylow_inner (coverage F hq) S α hfix
  exact ⟨x, hx.symm⟩

/-- The derived binary G₂ model admits no source central four-group. -/
theorem not_g2_derived (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty (NormalizerAction.componentImage K ≃* commutator (Model (ZMod 2))) := by
  rintro ⟨e⟩
  obtain ⟨A, hA, hfix⟩ := exists_model_fixed_four_on_sylow K hK a e derivedSylow
  let : IsKleinFour A := hA
  have hle : A ≤ BinaryCore.distinguished.map binaryConjugation := by
    intro α hα
    obtain ⟨x, hx, he⟩ := EvenInvolutionGeometry.binary_fixing_sylow_inner
      binaryConjugation_bijective derivedSylow α (hfix α hα)
    have hsq : α ^ 2 = 1 := by
      exact congrArg Subtype.val (show (⟨α, hα⟩ : A) ^ 2 = 1 by
        rw [pow_two, IsKleinFour.mul_self])
    have hx2 : x.val ^ 2 = 1 := by
      apply binaryConjugation_bijective.1
      rw [map_pow, binaryConjugation_inner, ← he, hsq, map_one]
    have hxD : x.val ∈ BinaryCore.distinguished := by
      apply derivedSylowAmbient_central_involution_mem
      · rw [← derivedSylow_map_subtype]
        exact mem_map_of_mem DerivedModel.subtype hx
      · exact hx2
      · intro y hy
        rw [← derivedSylow_map_subtype] at hy
        obtain ⟨y, hy, rfl⟩ := hy
        have hc := hfix α hα y hy
        rw [he, MulAut.conj_apply] at hc
        exact congrArg Subtype.val (mul_inv_eq_iff_eq_mul.mp hc).symm
    exact ⟨x.val, hxD, (binaryConjugation_inner x).trans he.symm⟩
  have hb := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hm := Nat.card_congr (BinaryCore.distinguished.equivMapOfInjective
    binaryConjugation binaryConjugation_bijective.1).toEquiv
  rw [hA.card_four, ← hm, BinaryCore.card_distinguished] at hb
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions.BinarySieve
