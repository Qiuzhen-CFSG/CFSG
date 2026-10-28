module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalControlKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.SourceFromOriginalRankOne
/-!
# Known-simple source NaturalOriginalControl

The original C.5.9–11 construction supplies the reduced natural setup, its characteristic-two overgroup and full Sylow. The proved known-simple C.5.12 theorem gives normalizer control, and the actual two-block orbit contradicts the original noncommuting conjugate.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource CounterexampleCharacteristic
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_control_from_original_knownSimple (T : Sylow 2 G) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    {n : ℕ} (hn : IsL2EvenBlock K n) (hKL : L ≤ centralizer (K : Set G))
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    X ⊓ normalizer (T₁ : Set G) ≤ normalizer (RankOne.U K : Set G) := by
  let Y := normalizer (T₁ : Set G)
  let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
  let V := conjugateSpanBy (RankOne.U K) N
  let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
  obtain ⟨F₁,_,⟨h₁⟩⟩ := ReducedMarking.rank_one_source_setup T hG H R K L T₁ hRT h hH hHe hcoreU
    hT₁ hhalf hNK hUorbit t ht hKt x hx hxR hnc
  have hv := rank_one_source_from_original T hG H R K L T₁ hRT hTR h h' hKL hH hHe hcoreU
    hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  have hr := rank_one_reduced_conditions T hG H R K L T₁ hRT h hH hHe hcoreU
    hT₁ hhalf hNK hUorbit t ht hKt x hx hxR hnc
  obtain ⟨P,hP,_⟩ := hr.2.2.2.1
  obtain ⟨S,hS⟩ := hv.2.2.2.2.2
  have hNX : N ≤ X := sup_le (le_sup_right.trans le_sup_right) le_sup_left
  have he : V = conjugateSpanBy (RankOne.U K) X :=
    le_antisymm (conjugateSpanBy_mono le_rfl hNX)
      (conjugateSpanBy_le (le_conjugateSpanBy _ _) hv.2.1)
  have hVC : conjugateSpanBy (RankOne.U K) X ≤ centralizer (RankOne.U K : Set G) := by
    rw [← he]
    exact hv.1.trans (h₁.core.trans_le inf_le_right)
  have hT₁p := T.isPGroup'.to_le (show T₁ ≤ (T : Subgroup G) from hT₁ ▸ inf_le_left)
  exact natural_source_theorem_5_12_knownSimple hG h₁ hn hT₁p hNK P hP X hr.1 le_sup_right
    hv.2.2.2.1 S hS hx hnc hVC

omit [Finite G] in
private theorem pair_span_normalizes (T U₁ U₂ : Subgroup G)
    (hpair : ∀ g ∈ T, U₁.conjBy g = U₁ ∨ U₁.conjBy g = U₂)
    (t : G) (ht : t ∈ T) (hUt : U₁.conjBy t = U₂) :
    T ≤ normalizer ((U₁ ⊔ U₂ : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg z hz
  have hsecond : U₂.conjBy g = U₁ ∨ U₂.conjBy g = U₂ := by
    have he : U₂.conjBy g = U₁.conjBy (g*t) := by rw [← hUt,conjBy_conjBy]
    rw [he]
    exact hpair (g*t) (T.mul_mem hg ht)
  have hm : (U₁ ⊔ U₂ : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ U₁ ⊔ U₂ := by
    rw [Subgroup.map_sup]
    change U₁.conjBy g ⊔ U₂.conjBy g ≤ _
    apply sup_le
    · rcases hpair g hg with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
    · rcases hsecond with he | he
      · rw [he]; exact le_sup_left
      · rw [he]; exact le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hz)

theorem natural_counterexample_false_knownSimple (T : Sylow 2 G) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    {n : ℕ} (hn : IsL2EvenBlock K n) (hKL : L ≤ centralizer (K : Set G))
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) : False := by
  have hcontrol := natural_control_from_original_knownSimple T hG H R K L T₁ hRT hTR h h' hn hKL hH hHe hcoreU
    hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  have hv := rank_one_source_from_original T hG H R K L T₁ hRT hTR h h' hKL hH hHe hcoreU
    hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  have hmod (g : G) : (RankOne.U K).conjBy g = RankOne.U (K.conjBy g) :=
    RankOne.U_map_equiv K (MulAut.conj g)
  have hpairU : ∀ g ∈ (T : Subgroup G), (RankOne.U K).conjBy g = RankOne.U K ∨
      (RankOne.U K).conjBy g = RankOne.U L := by
    intro g hg
    rcases hpair g hg with he | he
    · exact Or.inl ((hmod g).trans (congrArg RankOne.U he))
    · exact Or.inr ((hmod g).trans (congrArg RankOne.U he))
  have hUt : (RankOne.U K).conjBy t = RankOne.U L :=
    (hmod t).trans (congrArg RankOne.U hKt)
  have hTU := pair_span_normalizes (T : Subgroup G) (RankOne.U K) (RankOne.U L)
    hpairU t ht hUt
  have hULC : RankOne.U L ≤ centralizer (RankOne.U K : Set G) :=
    (map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))
  have hcomm : RankOne.U K ⊔ RankOne.U L ≤ centralizer (RankOne.U K : Set G) := by
    let : IsElementaryAbelian 2 (RankOne.U K) := h.short.elementary.map K.subtype
    exact sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) hULC
  obtain ⟨F₁,_,⟨h₁⟩⟩ := ReducedMarking.rank_one_source_setup T hG H R K L T₁ hRT h hH hHe hcoreU
    hT₁ hhalf hNK hUorbit t ht hKt x hx hxR hnc
  let V := conjugateSpanBy (RankOne.U K) (T₁ ⊔
    (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype)
  have hVC : V ≤ centralizer (RankOne.U K : Set G) := hv.1.trans (h₁.core.trans_le inf_le_right)
  exact CounterexampleReduction.source_normalizer_control_contradiction T T₁ K (RankOne.U K)
    (RankOne.U L) V (hT₁ ▸ inf_le_left) hhalf hTU t ht hUt hcomm
    (le_conjugateSpanBy _ _) hv.2.1 hcontrol x hx (fun hm => hnc (hm.trans hVC)) hnc
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
