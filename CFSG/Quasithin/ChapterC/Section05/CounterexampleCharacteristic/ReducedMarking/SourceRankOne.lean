module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.LinearSource
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.CubicSetup
/-!
# The reduced natural/A₃ marking from the original source data

C.5.9 constructs the actual reduced minimal parabolic and excludes a common
normal subgroup. The natural branch retains its original central cover and
possible field automorphisms; the A₃ branch uses the actual binary plane.
Both construct every field of the new Setup on the literal Baum(T₁).

Source: Aschbacher–Smith C.5.9, printed p.161, applying C.5.3–4.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]
theorem rank_one_source_setup (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    {F : Type*} [Field F] (h : RankOne.Setup R K F)
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (t : G) (ht : t ∈ (T : Subgroup G)) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    ∃ (F₁ : Type) (_ : Field F₁), Nonempty (RankOne.Setup T₁ K F₁) := by
  obtain ⟨_,_,_,⟨P,hP,hmin⟩,_,hno⟩ :=
    rank_one_reduced_conditions T hG H R K L T₁ hRT h hH hHe hcoreU hT₁ hhalf hNK hUorbit
      t ht hKt x hx hxR hnc
  have hT₁p := T.isPGroup'.to_le (show T₁ ≤ (T : Subgroup G) from hT₁ ▸ inf_le_left)
  rcases h.block with ⟨n,hn,_⟩ | hA
  · exact exists_linear_reduced_setup K T₁ hn hT₁p hNK P hP hmin hno
  · have hST : RankOne.S R ≤ T₁ := by
      rw [hT₁]
      exact le_inf (inf_le_left.trans hRT) h.coordinates.normalizes
    exact ⟨ZMod 2,inferInstance,exists_cubic_reduced_setup h hA T₁ hT₁p hNK hST P hP hmin hno⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
