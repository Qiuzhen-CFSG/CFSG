module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.Witness
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleSpan
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Orbit
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingCommutator
public import Theory.ElementaryAbelian.Join

/-!
# C.5.10 characteristic two for the literal reduced source subgroup

The original two-block setup constructs E₁E₂ and its central involution;
the reduced marked setup constructs the actual span V and X-normality.
Applying 1.1.4 to these same subgroups proves X∈He in both the rank-one/A₃
and alternating-five branches. The reduced setup is the genuine output
of C.5.9 and its C.5.3–4 application, retained with its assembly owner.

Source: Aschbacher–Smith, C.5.10, printed p.161.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
open ConjugateSource
variable {G : Type*} [Group G] [Finite G]

private theorem source_mem_He (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hUK : RankOne.U K ≤ T₁) (hUL : RankOne.U L ≤ ChapterB.baumann R)
    (hSU : ChapterB.baumann R ≤ normalizer (RankOne.U K : Set G))
    (hKelem : IsElementaryAbelian 2 (RankOne.U K))
    (hLelem : IsElementaryAbelian 2 (RankOne.U L))
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G))
    (hcomm : ⁅RankOne.U K,ChapterB.baumann R⁆ =
      ⁅RankOne.U K,(RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom⁆)
    (hspan : conjugateSpanBy (RankOne.U K) (T₁ ⊔ (pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype) ≤ ChapterB.baumann T₁ ⊓ centralizer (RankOne.U K : Set G))
    (hXV : (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ⊔
      (K ⊔ T₁) ≤ normalizer (conjugateSpanBy (RankOne.U K) (T₁ ⊔
        (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype) : Set G)) :
    let V := conjugateSpanBy (RankOne.U K) (T₁ ⊔ (pResidual 2 (normalizer (T₁ : Set G))).map
      (normalizer (T₁ : Set G)).subtype)
    V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ ∧
      (pResidual 2 (normalizer (T₁ : Set G))).map (normalizer (T₁ : Set G)).subtype ⊔
        (K ⊔ T₁) ∈ Chapter1.He G := by
  have hT₁T : T₁ ≤ (T : Subgroup G) := hT₁ ▸ inf_le_left
  have hULC : RankOne.U L ≤ centralizer (RankOne.U K : Set G) :=
    (map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))
  have hULT₁ : RankOne.U L ≤ T₁ := by
    rw [hT₁]
    exact le_inf (hUL.trans (inf_le_left.trans hRT))
      (hULC.trans (Subgroup.centralizer_le_normalizer _))
  have hmod (g : G) : (RankOne.U K).conjBy g = RankOne.U (K.conjBy g) :=
    RankOne.U_map_equiv K (MulAut.conj g)
  have hpairU : ∀ g ∈ (T : Subgroup G), (RankOne.U K).conjBy g = RankOne.U K ∨
      (RankOne.U K).conjBy g = RankOne.U L := by
    intro g hg
    rcases hpair g hg with he | he
    · exact Or.inl ((hmod g).trans (congrArg RankOne.U he))
    · exact Or.inr ((hmod g).trans (congrArg RankOne.U he))
  have hU : IsElementaryAbelian 2 (RankOne.U K ⊔ RankOne.U L : Subgroup G) := by
    let := hKelem
    let := hLelem
    exact IsElementaryAbelian.sup_of_le_centralizer hULC
  have hw := span_central_witness T T₁ (ChapterB.baumann R) (RankOne.U K) (RankOne.U L)
    hT₁T hhalf hUK hULT₁ hSU (hTR.trans (normalizer_le_normalizer_baumann R))
    hpairU hU t ht htout ((hmod t).trans (congrArg RankOne.U hKt)) x hx hnc hcomm
    (hspan.trans inf_le_right)
  exact ⟨hw,mem_He_of_central_witness T hE T₁ _ _ hT₁T hhalf
    (hspan.trans (inf_le_left.trans inf_le_left)) (le_sup_right.trans le_sup_right) hXV hw⟩

/-- The full C.5.10 conclusion for the actual natural/A₃ reduced span. -/
theorem rank_one_source (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (R K L T₁ : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    {F F' F₁ : Type*} [Field F] [Field F'] [Field F₁]
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F') (h₁ : RankOne.Setup T₁ K F₁)
    (hKL : L ≤ centralizer (K : Set G)) (hRK : T₁ ≤ normalizer (K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (RankOne.U K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let V := conjugateSpanBy (RankOne.U K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    V ≤ RankOne.Q T₁ K ∧ X ≤ normalizer (V : Set G) ∧
      V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ ∧ X ∈ Chapter1.He G := by
  have hT₁T : T₁ ≤ (T : Subgroup G) := hT₁ ▸ inf_le_left
  have hv := CounterexampleReduction.rank_one_reduced_span T T₁ K hT₁T hhalf h₁ hRK
  exact ⟨hv.1,hv.2,source_mem_He T (hG.evenCharacteristic T) R K L T₁ hRT hTR hT₁ hhalf
    (h₁.module_le.trans inf_le_left) h'.module_le h.coordinates.normalizes h.elementary h'.elementary
    hKL hpair t ht htout hKt x hx hnc (h.commutator_structure hxR hnc).1
    (hv.1.trans h₁.core.le) hv.2⟩

/-- The full C.5.10 conclusion for the actual alternating-five reduced span. -/
theorem alternating_source (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
    (R K L T₁ B : Subgroup G) (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (h₁ : AlternatingPairSetup T₁ K B) (hRK : T₁ ≤ normalizer (K : Set G))
    (hT₁ : T₁ = (T : Subgroup G) ⊓ normalizer (sourceModule K : Set G))
    (hhalf : T₁.relIndex (T : Subgroup G) = 2)
    (hpair : ∀ g ∈ (T : Subgroup G), K.conjBy g = K ∨ K.conjBy g = L)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htout : t ∉ T₁) (hKt : K.conjBy t = L)
    (x : G) (hx : x ∈ normalizer (T₁ : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let Y := normalizer (T₁ : Set G)
    let V := conjugateSpanBy (sourceModule K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    V ≤ RankOne.Q T₁ K ∧ X ≤ normalizer (V : Set G) ∧
      V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ ∧ X ∈ Chapter1.He G := by
  have hT₁T : T₁ ≤ (T : Subgroup G) := hT₁ ▸ inf_le_left
  have hv := CounterexampleReduction.alternating_reduced_span T T₁ K B hT₁T hhalf h₁ hRK
  have hKelem : IsElementaryAbelian 2 (RankOne.U K) := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  have hLelem : IsElementaryAbelian 2 (RankOne.U L) := by
    let := h'.block.2.1.elementary
    exact IsElementaryAbelian.map L.subtype
  have hnU : ChapterB.baumann R ≤ normalizer (sourceModule K : Set G) :=
    h.normalizes.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  exact ⟨hv.1,hv.2,source_mem_He T (hG.evenCharacteristic T) R K L T₁ hRT hTR hT₁ hhalf
    (h₁.module_le.trans inf_le_left) h'.module_le hnU hKelem hLelem h.commute hpair
    t ht htout hKt x hx hnc (h.commutator_structure x hxR hnc).1 (hv.1.trans h₁.core.le) hv.2⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic
