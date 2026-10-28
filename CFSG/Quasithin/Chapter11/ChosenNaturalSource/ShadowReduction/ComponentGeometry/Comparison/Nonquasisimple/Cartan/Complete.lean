module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Cartan.Quadratic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue
public import Theory.GroupTheory.CComponent.ImageInOvergroup

/-!
# Cartan normalization through the actual residual overcomponent

Project the original flag seed, residual and containing C-component to
N_G(R₁)/O₂(N_G(R₁)). The seed has its actual A₅ image and the residual
has its actual PSL₂(p) image. Both are normalized by the full Sylow image.
The proved model exclusions force equality of the residual and containing
images. Since the quotient kernel is R₁ and lies in the residual--Sylow
join, C-component comparison lifts equality to the original subgroups.
Relative normality of the containing component now gives normalization by
all of N_G(R₁), and hence by XT.

The final theorem supplies the literal Frattini factorization and residual
model from the complete catalogue, then applies this normalization to the
Cartan contradiction. Fitting centralization is its one remaining local
premise; Nonquasisimple.lean derives it from canonical starred membership.
The latter and final source assembly remain owned by
qt-d-1222-comparison-nonquasisimple. No source 11.4.2 completion is asserted
until that premise is discharged.
Source: Aschbacher--Smith 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The actual residual fills its containing C-component of N_G(R₁).
The original seed and full Sylow discharge every embedding alternative. -/
theorem ofFlag_residual_eq_overcomponent (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p)
    {K₀ : Subgroup G}
    (hK : Source.ComponentIn (normalizer ((ofFlag S f X z H).R₁ : Set G)) K₀)
    (hBK : normalizerResidual (ofFlag S f X z H) ≤ K₀) :
    normalizerResidual (ofFlag S f X z H) = K₀ := by
  let E := ofFlag S f X z H
  let N := normalizer (E.R₁ : Set G)
  let q := QuotientGroup.mk' (pCore 2 N)
  let B := normalizerResidual E
  have hTN : (T : Subgroup G) ≤ N := le_sup_right.trans seedJoin_normalizes_radical
  have hUN : E.L₁ ≤ N := le_sup_left.trans seedJoin_normalizes_radical
  have hBN : B ≤ N := (Closure.residualIn_le _).trans inf_le_right
  let Tn := T.subtype hTN
  let Tbar := Tn.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))
  let Ubar := (E.L₁.subgroupOf N).map q
  let Bbar := (B.subgroupOf N).map q
  let Kbar := (K₀.subgroupOf N).map q
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  let : Fact p.Prime := ⟨hp.1⟩
  have hBl := ofFlag_residual_mem_local S f X z H h hp3 hm
  have hUl : E.L₁.subgroupOf N ∈ Chapter1.L N (Tn : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTN hUN).mp
      ⟨hUN,LocalGeometry.Components.flag_mem_local_of_model D S f 0 hseed⟩
  have hBn : B.subgroupOf N ∈ Chapter1.L N (Tn : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTN hBN).mp ⟨hBN,hBl⟩
  have hUb : Ubar ∈ ChapterA.Section03.localCComponents Tbar :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hUl
  have hBb : Bbar ∈ ChapterA.Section03.localCComponents Tbar :=
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hBn
  have hTU : (Tn : Subgroup N) ≤ normalizer (E.L₁.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hUN]
    exact comap_mono (f.sylow_normalizes_Li 0)
  have hTB : (Tn : Subgroup N) ≤ normalizer (B.subgroupOf N : Set N) := by
    rw [←subgroupOf_normalizer_eq hBN]
    exact comap_mono (normalizerResidual_sylow_invariant h)
  have hTUbar : (Tbar : Subgroup (N ⧸ pCore 2 N)) ≤ normalizer (Ubar : Set (N ⧸ pCore 2 N)) :=
    (map_mono (f := q) hTU).trans (le_normalizer_map q)
  have hTBbar : (Tbar : Subgroup (N ⧸ pCore 2 N)) ≤ normalizer (Bbar : Set (N ⧸ pCore 2 N)) :=
    (map_mono (f := q) hTB).trans (le_normalizer_map q)
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  have hKb : Kbar.IsCComponent := hK.2.map_quotient (pCore 2 N)
  have heB : Bbar = (residualNormalizerProjection E).range := by
    ext y
    constructor
    · rintro ⟨b,hb,rfl⟩
      exact ⟨⟨b,hb⟩,rfl⟩
    · rintro ⟨b,rfl⟩
      exact ⟨⟨b,hBN b.property⟩,b.property,rfl⟩
  have hmodel : ClassicalGroup.IsPSL Bbar 2 p :=
    hm.of_mulEquiv ((MulEquiv.subgroupCongr heB).trans (residualNormalizerQuotientEquiv h).symm)
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hK.1)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hK.1))
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) :=
    ofFlag_overcomponent_quasisimple S f X z H h hp3 hm hK hBK
  let : IsQuasisimple Kbar :=
    IsQuasisimple.of_mulEquiv (((cComponentTwoCoreQuotientEquiv hK.2).symm.trans eK).symm)
  have hRne : E.R₁ ≠ ⊥ := by
    intro he
    exact f.V_ne_bot 0 (bot_unique (he ▸ E.V₁_le.trans (f.seed_le_Ri S 0)))
  have hN := S.source.simpleQTKE.twoLocal_sqtk ⟨E.R₁,hRne,isPGroup_pCoreIn 2 _,rfl⟩
  have hQ := ChapterE.Structure.sqtk_two_quotient hN (pCore 2 N) pCore_isPGroup
  obtain ⟨eU⟩ := seed_image_model S f X z H hseed hfour
  have he : Bbar = Kbar := eq_of_five_seed_and_prime_residual hQ
    (pCore_quotient_pCore_eq_bot 2) Tbar hUb hTUbar eU hBb hTBbar hKb
    (map_mono (comap_mono (ofFlag_seed_le_residual S f X z H)))
    (map_mono (comap_mono hBK)) hp hmodel
  have hRN : (pCore 2 N).map N.subtype ≤ (T : Subgroup G) := by
    change N.pCoreIn 2 ≤ (T : Subgroup G)
    rw [radical_normalizer_core]
    change (E.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact cComponent_eq_of_equal_images_of_kernel_le N (B ⊔ (T : Subgroup G)) B K₀ q
    (sup_le hBN hTN) le_sup_left hK.1 hBK hBl.1 hK.2
    (by rw [QuotientGroup.ker_mk']; exact hRN.trans le_sup_right) he

/-- The whole actual normalizer N_G(R₁), and therefore XT, normalizes the
literal residual N_Kz(R₁)^∞. No embedding or Cartan-invariance premise remains. -/
theorem ofFlag_normalizer_normalizes_residual (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p) :
    normalizer ((ofFlag S f X z H).R₁ : Set G) ≤
      normalizer (normalizerResidual (ofFlag S f X z H) : Set G) := by
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  obtain ⟨K₀,hK,hBK,_⟩ := ofFlag_exists_unique_normal_overcomponent S f X z H h hp3 hm
  rw [ofFlag_residual_eq_overcomponent S f X z H h hseed hfour hp hm hK.1 hBK]
  exact (normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2

/-- The original XT-normalization conclusion of the nonquasisimple Cartan
argument. The independent Frattini producer supplies the residual model. -/
theorem ofFlag_cartanJoin_normalizes_residual (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2) {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G)) :
    X ⊔ (T : Subgroup G) ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G) :=
  (sup_le hXN (le_sup_right.trans seedJoin_normalizes_radical)).trans
    (ofFlag_normalizer_normalizes_residual S f X z H h hseed hfour hp hm)

/-- The full nonquasisimple Cartan contradiction, conditional only on the
independently required Fitting centralization and preceding source facts.
The literal Frattini factorization, residual model and XT-normalization are proved. -/
theorem ofFlag_eq_of_fitting_centralizes (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hXN : X ≤ normalizer ((ofFlag S f X z H).R₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative
      (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K := by
  by_cases he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K
  · exact he
  obtain ⟨hs,hd,_,_,p,hp,hm,_⟩ :=
    Frattini.ofFlag_frattini_of_catalogue S f X z H h hA hseed hf he hn hF hc
  have hX := le_sup_left.trans
    (ofFlag_cartanJoin_normalizes_residual S f X z H h hseed hd hp hm hXN)
  exact eq_of_fitting_normalizer_split h hf hline hF hs hX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Cartan
