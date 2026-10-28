module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.MarkedBorel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.QuotientActions

/-!
# Transporting the two source factors with their cores

The actual H/O₂(H) map and the specified K* ≃ SL₃(4) equivalence identify
the two-core quotients of each source subgroup and its model image. The
embedded cores, relative normalizers, joins, and fixing/inverting congruences
are transported separately. No assertion kills a factor's surviving core.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), printed p.877; application pp.954–955.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G]

theorem starImage_mono (H : Subgroup G) {A D : Subgroup G} (hAD : A ≤ D) :
    Source.starImage H A ≤ Source.starImage H D := map_mono (subgroupOf_mono H hAD)

theorem modelImage_map (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDK : D ≤ K) :
    (modelImage H K D eK).map (sourceActor H K eK) = Source.starImage H D :=
  map_comap_eq_self ((starImage_mono H hDK).trans (sourceActor_range H K eK).ge)

def modelImageEquiv (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDK : D ≤ K) : modelImage H K D eK ≃* Source.starImage H D :=
  (equivMapOfInjective _ _ (sourceActor_injective H K eK)).trans
    (MulEquiv.subgroupCongr (modelImage_map H K D eK hDK))

theorem modelImage_isPPerfect (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDH : D ≤ H) (hDK : D ≤ K) (hp : IsPPerfect 2 D) :
    IsPPerfect 2 (modelImage H K D eK) :=
  (starImage_isPPerfect H D hDH hp).of_surjective
    (modelImageEquiv H K D eK hDK).symm.toMonoidHom
    (modelImageEquiv H K D eK hDK).symm.surjective

variable [Finite G]

def modelCoreQuotientEquiv (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDH : D ≤ H) (hDK : D ≤ K) :
    (D ⧸ pCore 2 D) ≃* (modelImage H K D eK ⧸ pCore 2 (modelImage H K D eK)) :=
  (starCoreQuotientEquiv H D hDH).trans
    (QuotientGroup.congr _ _ (modelImageEquiv H K D eK hDK).symm
      (pCore_map_iso 2 (modelImageEquiv H K D eK hDK).symm))

theorem model_quotient_card (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDH : D ≤ H) (hDK : D ≤ K) :
    Nat.card (modelImage H K D eK ⧸ pCore 2 (modelImage H K D eK)) =
      Nat.card (D ⧸ pCore 2 D) :=
  (Nat.card_congr (modelCoreQuotientEquiv H K D eK hDH hDK).toEquiv).symm

theorem starImage_core (H D : Subgroup G) (hDH : D ≤ H) :
    Source.starImage H (D.pCoreIn 2) = (Source.starImage H D).pCoreIn 2 := by
  have he : (D.pCoreIn 2).subgroupOf H = (D.subgroupOf H).pCoreIn 2 := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 D).trans hDH),
      map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le hDH]
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  change ((D.pCoreIn 2).subgroupOf H).map _ = ((D.subgroupOf H).map _).pCoreIn 2
  rw [he]
  exact map_pCoreIn_of_ker_isPGroup _ hk _

theorem modelImage_core (H K D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hDH : D ≤ H) (hDK : D ≤ K) :
    modelImage H K (D.pCoreIn 2) eK = (modelImage H K D eK).pCoreIn 2 := by
  apply map_injective (sourceActor_injective H K eK)
  rw [modelImage_map H K _ eK ((pCoreIn_le 2 D).trans hDK),
    map_pCoreIn_of_injective 2 _ _ (sourceActor_injective H K eK),
    modelImage_map H K D eK hDK, starImage_core H D hDH]

omit [Finite G] in
theorem starImage_normalizes (H A D : Subgroup G)
    (hn : A ≤ normalizer (D : Set G)) :
    Source.starImage H A ≤ normalizer (Source.starImage H D : Set _) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨a, ha, rfl⟩ _ ⟨d, hd, rfl⟩
  exact ⟨a * d * a⁻¹, le_normalizer_iff.mp hn a.val ha d.val hd, by simp only [map_mul, map_inv]⟩

omit [Finite G] in
theorem modelImage_normalizes (H K A D : Subgroup G)
    (eK : Source.starImage H K ≃* SL) (hn : A ≤ normalizer (D : Set G)) :
    modelImage H K A eK ≤ normalizer (modelImage H K D eK : Set SL) :=
  (comap_mono (starImage_normalizes H A D hn)).trans
    ((Source.starImage H D).le_normalizer_comap _)

omit [Finite G] in
theorem modelImage_sup (H K A D : Subgroup G) (eK : Source.starImage H K ≃* SL)
    (hAH : A ≤ H) (hDH : D ≤ H) (hAK : A ≤ K) (hDK : D ≤ K) :
    modelImage H K (A ⊔ D) eK = modelImage H K A eK ⊔ modelImage H K D eK := by
  apply map_injective (sourceActor_injective H K eK)
  rw [Subgroup.map_sup, modelImage_map H K _ eK (sup_le hAK hDK),
    modelImage_map H K A eK hAK, modelImage_map H K D eK hDK,
    Source.starImage, subgroupOf_sup hAH hDH, Subgroup.map_sup]
  rfl

theorem model_fix (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hDH : D ≤ H) (hDK : D ≤ K) (t : H)
    (hfix : ∀ d ∈ D, t.val⁻¹ * d * t.val * d⁻¹ ∈ D.pCoreIn 2) :
    ∀ x ∈ modelImage H K D eK,
      sourceConjugation H K eK (QuotientGroup.mk' (pCore 2 H) t) x * x⁻¹ ∈
        (modelImage H K D eK).pCoreIn 2 := by
  intro x hx
  rw [← modelImage_core H K D eK hDH hDK]
  obtain ⟨d, hd, he⟩ := hx
  change sourceActor H K eK _ ∈ Source.starImage H (D.pCoreIn 2)
  rw [map_mul, map_inv, sourceActor_sourceConjugation, ← he]
  exact ⟨t⁻¹ * d * t * d⁻¹, hfix d.val hd, by simp only [map_mul, map_inv]⟩

theorem model_invert (H K D : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hDH : D ≤ H) (hDK : D ≤ K) (t : H)
    (hinv : ∀ d ∈ D, t.val⁻¹ * d * t.val * d ∈ D.pCoreIn 2) :
    ∀ x ∈ modelImage H K D eK,
      sourceConjugation H K eK (QuotientGroup.mk' (pCore 2 H) t) x * x ∈
        (modelImage H K D eK).pCoreIn 2 := by
  intro x hx
  rw [← modelImage_core H K D eK hDH hDK]
  obtain ⟨d, hd, he⟩ := hx
  change sourceActor H K eK _ ∈ Source.starImage H (D.pCoreIn 2)
  rw [map_mul, sourceActor_sourceConjugation, ← he]
  exact ⟨t⁻¹ * d * t * d, hinv d.val hd, by simp only [map_mul, map_inv]⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
