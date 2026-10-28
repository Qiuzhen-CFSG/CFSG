module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FullCubicAction
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.SourceFromOriginalRankOne

/-!
# The original C.5 source data supplies G.6.1

The C.5.9 reduction constructs the smaller Baumann marking; C.5.10–11
construct the residual span, its characteristic-two overgroup, and its
actual Sylow subgroup. They identify that residual span with the full
X-span. Thus G.6.1 applies to the canonical action quotient, using X as
its original SQTK cover. The same moving element has displacement rank one
and inverts the actual cubic normalized by the full quotient Sylow subgroup.
No reduced setup, action, or Sylow witness is an additional premise.

Source: Aschbacher–Smith C.5.9–12, printed pp.161–163.
-/
public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource CounterexampleCharacteristic
universe u
variable {G : Type u} [Group G] [Finite G]
private theorem faithful_transvection_rank
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (hi : Function.Injective ρ)
    (a : D) (hne : a ≠ 1)
    (ht : LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a) ∈
      LinearEquiv.transvections (ZMod 2) W) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ a-LinearMap.id)) = 1 := by
  have hrank := (LinearEquiv.mem_dilatransvections_iff_finrank
    (e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a))).mp
      (LinearEquiv.transvections_subset_dilatransvections ht)
  have hrank' : Module.finrank (ZMod 2) (LinearMap.range (ρ a-LinearMap.id)) ≤ 1 := by
    convert! hrank using 1
  have hrne : LinearMap.range (ρ a-LinearMap.id) ≠ ⊥ := by
    intro he
    apply hne
    apply hi
    rw [map_one]
    exact sub_eq_zero.mp (LinearMap.range_eq_bot.mp he)
  have : Nontrivial (LinearMap.range (ρ a-LinearMap.id)) :=
    Submodule.nontrivial_iff_ne_bot.mpr hrne
  exact Nat.le_antisymm hrank' Module.finrank_pos

/-- All G.6.1 hypotheses and the actual marked transvection follow from
the original C.5.9 configuration. -/
theorem alternating_three_g6_from_original (T : Sylow 2 G) {𝒦 : GroupClass} (hG : IsSimpleQTKE 𝒦 G)
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
    let V := conjugateSpanBy (RankOne.U K) (T₁ ⊔ (pResidual 2 Y).map Y.subtype)
    let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
    ∃ hp : Theory.GroupTheory.IsPReduced 2 (V.subgroupOf X),
      let : (V.subgroupOf X).Normal := hp.normal
      let : IsElementaryAbelian 2 (V.subgroupOf X) := hp.elementary
      ∃ b : X, (b : G) ∈ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ∧
        (b : G) ∉ centralizer (RankOne.U K : Set G) ∧
        ChapterG.Section06.Hypotheses 𝒦 (Representation.centralizerQuotient (V.subgroupOf X))
          (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b)
          (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X))) ∧
        LinearMap.GeneralLinearGroup.toLinearEquiv
          ((Representation.centralizerQuotient (V.subgroupOf X)).asGroupHom
            (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b)) ∈
          LinearEquiv.transvections (ZMod 2) (Additive (V.subgroupOf X)) ∧
        Module.finrank (ZMod 2) (LinearMap.range
          (Representation.centralizerQuotient (V.subgroupOf X)
            (QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b) -
              (LinearMap.id : Additive (V.subgroupOf X) →ₗ[ZMod 2] Additive (V.subgroupOf X)))) = 1 ∧
        ∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = T₁ ∧
          ∃ c : X ⧸ centralizer (V.subgroupOf X : Set X), c^3=1 ∧ c≠1 ∧
            ((S.mapSurjective (QuotientGroup.mk'_surjective (centralizer (V.subgroupOf X : Set X)))) :
              Subgroup (X ⧸ centralizer (V.subgroupOf X : Set X))) ≤
              normalizer (zpowers c : Set (X ⧸ centralizer (V.subgroupOf X : Set X))) ∧
            QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b * c =
              c^2 * QuotientGroup.mk' (centralizer (V.subgroupOf X : Set X)) b := by
  let Y := normalizer (T₁ : Set G)
  let N := T₁ ⊔ (pResidual 2 Y).map Y.subtype
  let V := conjugateSpanBy (RankOne.U K) N
  let X := (pResidual 2 Y).map Y.subtype ⊔ (K ⊔ T₁)
  obtain ⟨F₁,_,⟨h₁⟩⟩ := ReducedMarking.rank_one_source_setup T hG H R K L T₁ hRT h hH hHe hcoreU
    hT₁ hhalf hNK hUorbit t ht hKt x hx hxR hnc
  have hv := rank_one_source_from_original T hG H R K L T₁ hRT hTR h h' hKL hH hHe hcoreU
    hT₁ hhalf hNK hUorbit hpair t ht htout hKt x hx hxR hnc
  obtain ⟨P,hP⟩ := hv.2.2.2.2.2
  have hKX : K ≤ X := le_sup_left.trans le_sup_right
  have hTX : T₁ ≤ X := le_sup_right.trans le_sup_right
  have hNX : N ≤ X := sup_le hTX le_sup_left
  have he : V = conjugateSpanBy (RankOne.U K) X :=
    le_antisymm (conjugateSpanBy_mono le_rfl hNX)
      (conjugateSpanBy_le (le_conjugateSpanBy _ _) hv.2.1)
  have hVC : V ≤ centralizer (RankOne.U K : Set G) :=
    hv.1.trans (h₁.core.trans_le inf_le_right)
  have hVT : V ≤ T₁ := hv.1.trans (h₁.core.trans_le (inf_le_left.trans inf_le_left))
  have hXp : IsSQTK 𝒦 X := sqtk_of_mem_He hG X hv.2.2.2.1 (by
    intro hbot
    have hUbot : RankOne.U K = ⊥ := bot_unique ((map_subtype_le _).trans (hKX.trans_eq hbot))
    apply hnc
    rw [hUbot,Subgroup.map_bot]
    exact bot_le)
  have hT₁p := T.isPGroup'.to_le (show T₁ ≤ (T : Subgroup G) from hT₁ ▸ inf_le_left)
  obtain ⟨hp,b,hb,hbC,hyp,htv⟩ := alternating_three_g6_hypotheses h₁ ha hT₁p hNK X hKX hTX P hP
    hXp V he hVC hVT hx hnc
  let : (V.subgroupOf X).Normal := hp.normal
  let : IsElementaryAbelian 2 (V.subgroupOf X) := hp.elementary
  have hVX : V ≤ X := he ▸ conjugateSpanBy_le_self ((map_subtype_le _).trans hKX)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_surjective
    (subgroupOfEquivOfLe hVX).toMonoidHom (subgroupOfEquivOfLe hVX).surjective
  have hrank := faithful_transvection_rank (Representation.centralizerQuotient (V.subgroupOf X))
    hyp.faithful _ hyp.nonidentity htv
  have hbT : (b : G) ∈ T₁ := (h₁.conjugate_le hx).trans inf_le_left hb
  have hcubic := alternating_three_full_inverter h₁ ha hT₁p hNK X V hKX hVX hv.2.1
    (le_conjugateSpanBy _ _) P hP b hbT hbC
  exact ⟨hp,b,hb,hbC,hyp,htv,hrank,P,hP,hcubic⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
