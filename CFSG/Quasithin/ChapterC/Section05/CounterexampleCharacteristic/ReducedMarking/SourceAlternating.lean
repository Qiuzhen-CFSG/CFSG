module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.AlternatingSetup
/-!
# The alternating reduced C.5.3–4 setup from the original C.5.9 data

The original simple-QTKE Sylow subgroup, original block pair, and escaping
conjugate first construct the reduced minimal parabolic and no-common-normal
conditions. The actual reduced Baumann/action argument then constructs the
new marked setup on Baum(T₁). Thus no reduced action or core identity is an
input to this literal source application.

Source: Aschbacher–Smith C.5.9, printed p.161, applying C.5.3–4.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]
theorem alternating_source_setup (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (h : AlternatingPairSetup R K L)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (sourceModule K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (sourceModule K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : sourceModule K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    Nonempty (AlternatingPairSetup T₁ K ⊥) := by
  obtain ⟨_,_,_,⟨P,hP,hmin⟩,_,hno⟩ :=
    alternating_reduced_conditions T hG H R K L T₁ hRT h hH hHe hcoreU hT₁ hhalf hNK hUorbit
      t ht hKt x hx hxR hnc
  have hT₁T : T₁ ≤ (T : Subgroup G) := hT₁ ▸ inf_le_left
  have hST : ChapterB.baumann R ≤ T₁ := by
    rw [hT₁]
    exact le_inf (inf_le_left.trans hRT) (h.normalizes.trans
      (normalizer_le_normalizer_characteristic_image K (blockU K)))
  exact exists_alternating_reduced_setup h T₁ (T.isPGroup'.to_le hT₁T) hNK hST
    P hP hmin hno x hxR hnc
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
