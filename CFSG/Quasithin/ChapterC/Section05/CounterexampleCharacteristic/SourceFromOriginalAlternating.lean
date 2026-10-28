module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.SourceAlternating
/-!
# C.5.10–11 from the original alternating source data

The reduced setup is constructed by C.5.9 and its actual Baumann marking.
The literal residual span therefore supplies characteristic two, its
normalizer intersection, and the original T₁ as a Sylow subgroup of X.
No reduced setup is assumed by this source endpoint.

Source: Aschbacher–Smith C.5.9–11, printed p.161.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]
theorem alternating_source_from_original (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (sourceModule K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (sourceModule K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : sourceModule K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let V := conjugateSpanBy (sourceModule K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    V ≤ RankOne.Q T₁ K ∧ X ≤ normalizer (V : Set G) ∧
      V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ ∧ X ∈ Chapter1.He G ∧
      X ⊓ Y = T₁ ⊔ (pResidual 2 Y).map Y.subtype ∧
      ∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = T₁ := by
  obtain ⟨h₁⟩ := ReducedMarking.alternating_source_setup T hG H R K L T₁ hRT h hH hHe hcoreU
    hT₁ hhalf hNK hUorbit t ht hKt x hx hxR hnc
  have hv := alternating_source T hG R K L T₁ ⊥ hRT hTR h h' h₁ hNK hT₁ hhalf hpair
    t ht htout hKt x hx hxR hnc
  exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2,
    CounterexampleReduction.alternating_reduced_sylow T T₁ K ⊥ (hT₁ ▸ inf_le_left) hhalf h₁ hNK x hx hnc⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
