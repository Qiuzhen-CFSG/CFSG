module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingSetup
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AlternatingOriginalControl

/-!
# The original alternating branch with C.5.4 discharged

The original block and Sylow data now construct both alternating setups.
Their original C.5.12 consumer gives the contrary-configuration contradiction.
The universal A.3.12 embedding implication and the genuine earlier source
configuration remain visible; this is not the unrestricted C.5.8 theorem.

Source: Aschbacher–Smith C.5.3–13, printed pp.154–166.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem alternating_counterexample_false_of_block_data (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hR : IsPGroup 2 R) (hK : IsAlternatingBlock K 5) (hL : IsAlternatingBlock L 5)
    (hmoveK : K = ⁅K,elementaryAbelianMaxJ R⁆)
    (hmoveL : L = ⁅L,elementaryAbelianMaxJ R⁆)
    (hnK : ChapterB.baumann R ≤ normalizer (K : Set G))
    (hnL : ChapterB.baumann R ≤ normalizer (L : Set G))
    (PK : Sylow 2 K) (hPK : (PK : Subgroup K).map K.subtype = R ⊓ K)
    (PL : Sylow 2 L) (hPL : (PL : Subgroup L).map L.subtype = R ⊓ L)
    (hcomm : L ≤ centralizer (K : Set G))
    (hpermK : ∀ r ∈ R, K.map (MulAut.conj r).toMonoidHom = K ∨
      K.map (MulAut.conj r).toMonoidHom = L)
    (hpermL : ∀ r ∈ R, L.map (MulAut.conj r).toMonoidHom = L ∨
      L.map (MulAut.conj r).toMonoidHom = K)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (sourceModule K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (sourceModule K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : sourceModule K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) : False := by
  obtain ⟨h⟩ := exists_alternatingPairSetup R K L hR hK hmoveK hnK PK hPK hcomm hpermK
  obtain ⟨h'⟩ := exists_alternatingPairSetup R L K hR hL hmoveL hnL PL hPL
    (le_centralizer_iff.mp hcomm) hpermL
  exact NormalizerControl.alternating_counterexample_false T hG hA312 H R K L T₁
    hRT hTR h h' hH hHe hcoreU hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
