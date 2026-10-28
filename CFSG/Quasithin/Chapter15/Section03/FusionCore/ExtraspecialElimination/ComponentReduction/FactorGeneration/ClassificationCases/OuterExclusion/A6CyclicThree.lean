module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion.Residual
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ConjugatePlacement.GeometryTransport
public import Theory.GroupTheory.PCorePrimeToIndex
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Excluding the A₆ × C₃ outer-involution alternative

For the actual index-two subgroup K ≃ A₆ × C₃, simplicity of A₆ computes
O₃(K) as the displayed C₃. Its characteristic image is normal in the whole
extension, and the index-two bound identifies it with the whole three-core.
The prescribed inversion by the extending element makes this core noncentral.
Residual.threeCore_le_center_of_card_three gives the opposite conclusion
for the actual selected conjugate span. This excludes B.5.6(4).

The branch input is an actual multiplicative equivalence on K and its
compatible inversion formula, not an abstract family tag. The argument
uses no restriction on the representation, so it covers both allowed
ranks 4 and 5 of V₁ and the rank-two V₂ clause simultaneously. It even
needs neither the involution equation nor the specified outer action on
A₆: inversion of the cubic factor already suffices.

The source application keeps A = V_alpha as the genuine endpointModule,
a conjugate of V_H = localSpan V H. Y₀ is the literal two-residual of
C_Y(V). The source classification implication supplying K and its
compatible model remains the separate universal B.5.6 input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(4),
printed p.105, and the proof of 15.3.49(i), printed pp.1143–1144.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion

open ConjugatePlacement

private abbrev A6 := alternatingGroup (Fin 6)
private abbrev C3 := Multiplicative (ZMod 3)

private theorem a6_threeCore : pCore 3 A6 = ⊥ := by
  let : IsSimpleGroup A6 := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pCore 3 A6) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 3 A6 := (h ▸ pCore_isPGroup).of_equiv (topEquiv (G := A6))
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card A6 = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hc] at hn
    have h2 : 2 ∣ 3 ^ n := dvd_trans (by decide : 2 ∣ 360) hn
    exact False.elim ((by decide : ¬ 2 ∣ 3) (Nat.prime_two.dvd_of_dvd_pow h2))

private theorem product_threeCore :
    pCore 3 (A6 × C3) = (MonoidHom.fst A6 C3).ker := by
  let f := MonoidHom.fst A6 C3
  have hf : Function.Surjective f := fun a => ⟨(a, 1), rfl⟩
  have hmap : (pCore 3 (A6 × C3)).map f ≤ pCore 3 A6 :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  apply le_antisymm
  · rw [a6_threeCore] at hmap
    simpa only [Subgroup.map_eq_bot_iff] using (le_bot_iff.mp hmap)
  · apply le_sSup
    refine ⟨inferInstance, ?_⟩
    let e : f.ker ≃* C3 :=
      { toFun := fun x => x.1.2
        invFun := fun x => ⟨(1, x), rfl⟩
        left_inv := by rintro ⟨⟨a, c⟩, h⟩; apply Subtype.ext; exact Prod.ext h.symm rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    exact (IsPGroup.of_card (p := 3) (n := 1) (by simp [C3])).of_equiv e.symm

private theorem product_threeCore_card : Nat.card (pCore 3 (A6 × C3)) = 3 := by
  rw [product_threeCore]
  let e : (MonoidHom.fst A6 C3).ker ≃ C3 :=
    { toFun := fun x => x.1.2
      invFun := fun x => ⟨(1, x), rfl⟩
      left_inv := by rintro ⟨⟨a, c⟩, h⟩; apply Subtype.ext; exact Prod.ext h.symm rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  simp [C3]

variable {D : Type*} [Group D] [Finite D]

/-- The literal index-two extension of A₆ × C₃ has a noncentral three-core
of order three when an element inverts its marked cubic generator. -/
theorem a6_cyclic_three_extension_core
    (K : Subgroup D) (hK : K.index = 2) (e : K ≃* alternatingGroup (Fin 6) × Multiplicative (ZMod 3))
    (t : D) (hinv : t * (e.symm (1, Multiplicative.ofAdd 1) : K) * t⁻¹ =
      ((e.symm (1, Multiplicative.ofAdd 1) : K) : D)⁻¹) :
    Nat.card (pCore 3 D) = 3 ∧ ¬ pCore 3 D ≤ center D := by
  have hKn : K.Normal := K.normal_of_index_eq_two hK
  have hcore : pCore 3 D = (pCore 3 K).map K.subtype := by
    apply le_antisymm
    · exact pCore_le_map_pCore_of_prime_not_dvd_index K (by rw [hK]; decide)
    · have hn : ((pCore 3 K).map K.subtype).Normal := by
        apply normalizer_eq_top_iff.mp
        apply top_unique
        calc
          ⊤ = normalizer (K : Set D) := K.normalizer_eq_top.symm
          _ ≤ normalizer ((pCore 3 K).map K.subtype : Set D) :=
            normalizer_le_normalizer_characteristic_image K (pCore 3 K)
      exact le_sSup ⟨hn, pCore_isPGroup.map K.subtype⟩
  have hKe : (pCore 3 K).map e.toMonoidHom = pCore 3 (A6 × C3) := pCore_map_iso 3 e
  have hcK : Nat.card (pCore 3 K) = 3 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) (K := pCore 3 K) e.injective, hKe]
    exact product_threeCore_card
  refine ⟨by rw [hcore, card_map_of_injective K.subtype_injective, hcK], ?_⟩
  intro hz
  let r : K := e.symm (1, Multiplicative.ofAdd 1)
  have hr : r ∈ pCore 3 K := by
    have hm : (1, Multiplicative.ofAdd 1) ∈ (pCore 3 K).map e.toMonoidHom := by
      rw [hKe, product_threeCore]
      rfl
    obtain ⟨x, hx, he⟩ := hm
    have hxr : x = r := e.injective (he.trans (e.apply_symm_apply _).symm)
    exact hxr ▸ hx
  have hrc : (r : D) ∈ center D := hz (hcore ▸ mem_map_of_mem K.subtype hr)
  have hfix : t * (r : D) * t⁻¹ = r := by
    rw [((mem_center_iff.mp hrc) t), mul_inv_cancel_right]
  have hri : r = r⁻¹ := Subtype.ext (hfix.symm.trans hinv)
  have he := congrArg (fun x : K => (e x).2) hri
  simp only [map_inv, r, e.apply_symm_apply] at he
  change (1 : ZMod 3) = -1 at he
  exact (by decide : (1 : ZMod 3) ≠ -1) he


/-- Exclusion of B.5.6(4) for the actual selected endpoint, from the earlier
local residual and two-core containments and the compatible branch model. -/
theorem exclude_a6_cyclic_three_extension
    {G : Type*} [Group G] [Finite G]
    (H M Y Y0 T V : Subgroup G) (g : G)
    (hAH : endpointModule V H g ≤ H) (hYH : Y0 ≤ H)
    (hY0 : Y0 = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V : Set G)))
    (hN : normalizer (Y0 : Set G) = M) (hQM : localTwoCore H ≤ M)
    (hθ : theta (M ⊓ H) = Y0)
    (hA : starImage H (endpointModule V H g) ≤
      (pCore 2 ↥(starImage H Y0 ⊔ starImage H T)).map
        (starImage H Y0 ⊔ starImage H T).subtype)
    (K : Subgroup (starImage H (localSpan (endpointModule V H g) H)))
    (hK : K.index = 2)
    (e : K ≃* alternatingGroup (Fin 6) × Multiplicative (ZMod 3))
    (t : starImage H (localSpan (endpointModule V H g) H))
    (hinv : t * (e.symm (1, Multiplicative.ofAdd 1) : K) * t⁻¹ =
      ((e.symm (1, Multiplicative.ofAdd 1) : K) :
        starImage H (localSpan (endpointModule V H g) H))⁻¹) : False := by
  obtain ⟨hcard, hnoncentral⟩ := a6_cyclic_three_extension_core K hK e t hinv
  have hY : IsPPerfect 2 Y0 := by
    rw [hY0]
    intro N hN hp
    have h := BenderSuzuki.External.hktPResidual_le N hN hp
    rw [twoResidualAmbient_has_top_twoResidual] at h
    exact top_unique h
  exact hnoncentral (threeCore_le_center_of_card_three H M Y0 T
    (endpointModule V H g) hAH hYH hY hN hQM hθ hA hcard)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.OuterExclusion
