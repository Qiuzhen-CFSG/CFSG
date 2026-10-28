module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.G6OriginalSource
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.SymmetricQuotientControl
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.Inputs

/-!
# The A₃ normalizer and counterexample endpoints from the earlier G.6 input

Every action, core, Sylow, cubic, and displacement premise is constructed
from the original C.5.9 data. The normalized-cubic source implication from
G.6.4 supplies the S₃/S₇ actor model; the actual quotient normalizer then
controls U(K). The original two-block orbit gives the C.5.8 counterexample
contradiction. The still-unproved earlier G.6 source implication remains
an explicit argument, rather than an assumed action-classification witness.

Source: Aschbacher–Smith C.5.12 and the end of C.5.8, printed pp.161–163.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource CounterexampleCharacteristic
universe u
variable {G : Type u} [Group G] [Finite G]
/-- Original C.5.12 for the A₃ branch, retaining only the genuine earlier
normalized-cubic source theorem in addition to the original source data. -/
theorem alternating_three_control_from_original_of_g6 (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hG6 : ChapterG.Section06.NormalizedCubicSourceInput.{u,u} 𝒦)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
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
  obtain ⟨hp,b,hb,hbC,hyp,htv,hrank,P,hP,c,hc,hcne,hPn,hinv⟩ :=
    alternating_three_g6_from_original T hG H R K L T₁ hRT hTR h ha h' hKL hH hHe hcoreU
      hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  let : (V.subgroupOf X).Normal := hp.normal
  let : IsElementaryAbelian 2 (V.subgroupOf X) := hp.elementary
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))
  let ρ := Representation.centralizerQuotient (V.subgroupOf X)
  have hmodel := hG6.apply hyp hrank
    (P.mapSurjective (QuotientGroup.mk'_surjective _)) c hc hcne hPn hinv
  have hv := rank_one_source_from_original T hG H R K L T₁ hRT hTR h h' hKL hH hHe hcoreU
    hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  have hKX : K ≤ X := le_sup_left.trans le_sup_right
  have hNX : N ≤ X := sup_le (le_sup_right.trans le_sup_right) le_sup_left
  exact source_span_control_of_symmetric_quotient K T₁ N X hKX hNX hNK P hP hv.2.1 hmodel

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

/-- The original A₃ counterexample configuration is impossible once the
earlier normalized-cubic source theorem is supplied. -/
theorem alternating_three_counterexample_false_of_g6 (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (hG6 : ChapterG.Section06.NormalizedCubicSourceInput.{u,u} 𝒦)
    (H R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (ha : ChapterC.IsAlternatingBlock K 3)
    (h' : RankOne.Setup R L F')
    (hKL : L ≤ centralizer (K : Set G))
    (hH : H = (K ⊔ L) ⊔ (T : Subgroup G)) (hHe : H ∈ Chapter1.He G)
    (hcoreU : H.pCoreIn 2 ≤ centralizer (RankOne.U K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2) (hNK : T₁ ≤ normalizer (K : Set G))
    (hUorbit : RankOne.U K ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) : False := by
  have hcontrol := alternating_three_control_from_original_of_g6 T hG hG6 H R K L T₁ hRT hTR
    h ha h' hKL hH hHe hcoreU hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
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
    let := h.elementary
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
