module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.CentralizingSource
/-!
# The original noncubic centralizing-core branch of C.5.12

The proved C.5.13 normalizer bound combines with the literal core-centralizer
identity and the Frattini argument. Both source block markings therefore
control the full Sylow normalizer when P₁ centralizes the original full span.
The core-centralizing assumption is precisely this branch of the source
case split; no C.5.13 input remains.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_source_control_of_core_centralizing {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (V : Subgroup G) (hUV : U K ≤ V) (hXV : X ≤ normalizer (V : Set G))
    (hCV : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (U K : Set G) := by
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core K T
    h.short hT hTK ⟨P,hP⟩).2.2.2.2.2
  exact normalizer_control_of_source_core_centralizing_sylow X T (U K) V _
    hUV hXV S hS hcore hCV (natural_source_normalizer_control hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc)

theorem alternating_source_control_of_core_centralizing {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (V : Subgroup G) (hUV : sourceModule K ≤ V) (hXV : X ≤ normalizer (V : Set G))
    (hCV : (K ⊔ T).pCoreIn 2 ≤ centralizer (V : Set G)) :
    X ⊓ normalizer (T : Set G) ≤ normalizer (sourceModule K : Set G) := by
  have hcore := (CounterexampleCharacteristic.ReducedMarking.reduced_baumann_core K T
    h.block.2.1 h.twoGroup hTK ⟨P,hP⟩).2.2.2.2.2
  exact normalizer_control_of_source_core_centralizing_sylow X T (sourceModule K) V _
    hUV hXV S hS hcore hCV (alternating_source_normalizer_control hG hA312 h hTK P hP X hA hAX hX S hS hx hnc)

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
