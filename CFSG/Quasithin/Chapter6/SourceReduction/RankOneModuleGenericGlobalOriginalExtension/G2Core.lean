module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.Marked
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.G2
public import Theory.AtlasPort.LinearGroups.G2.HighestRootWeakClosure
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer
public import Mathlib.Algebra.CharP.Reduced
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.A5LocalFactorization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionG2Short

/-!
# The original G₂ extension core and its short-local orientation

The short local's intrinsic two-core recovers its full parabolic normalizer.
An automorphism preserving this local is inner times coefficient transport.
The trace of its action on the actual two-dimensional quotient detects that
coefficient: every scalar is the trace of a determinant-one matrix. A
quotient-trivial two-element is therefore inner in the parabolic, and its
determinant has two-power order in characteristic two, so it lies in the local.

Transporting the resulting core identity through the original right endpoint
proves O₂(RS)=O₂(R). The normalized right Borel and the actual relative Sylows
then give S≤R. Binary fields are excluded directly from the solvability of the
marked short local. The source's faithful core-center action also excludes a
short local on the left before any extension collapse. These statements apply
to the same selected perfect R, without R=O²(H) or S=T.

Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651,
`refs/quasithin.pdf`. Native root and quotient facts are imported from the
licensed ATLAS port; no additional ATLAS source is copied here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalG2
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem normalizer_short_le :
    normalizer (local₁ (F := F) : Set (Model F)) ≤ parabolic₁ := by
  have hn := normalizer_le_normalizer_characteristic_image (local₁ (F := F)) (pCore 2 local₁)
  change normalizer (local₁ (F := F) : Set (Model F)) ≤
    normalizer ((local₁ (F := F)).pCoreIn 2 : Set (Model F)) at hn
  rwa [local₁_pCore, HighestRootWeakClosure.normalizer_radical] at hn

omit [Finite F] in
private theorem short_two_element (g : Model F) (hg : g ∈ parabolic₁)
    (k : ℕ) (hk : g^(2^k)=1) : g ∈ local₁ := by
  let p : shortPlaneStabilizer (F := F) := ⟨g,parabolic₁_le_shortPlaneStabilizer hg⟩
  have hp : p^(2^k)=1 := Subtype.ext hk
  have hd : (shortDet p)^(2^k)=1 := by rw [←map_pow,hp,map_one]
  have hd1 : shortDet p = 1 := by
    apply iterateFrobenius_inj F 2 k
    simpa only [iterateFrobenius_def,one_pow] using hd
  rw [local₁_eq_shortSpecial]
  exact ⟨p,hd1,rfl⟩

private theorem short_detection (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) (hK : (local₁ (F := F)).map a.toMonoidHom = local₁)
    (htwo : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x : local₁ (F := F), a x.val / x.val ∈ radical₁) :
    ∃ g : local₁ (F := F), a = MulAut.conj g.val := by
  obtain ⟨g,σ,ha⟩ := exists_inner_field hq a
  have hg : g ∈ parabolic₁ := by
    apply normalizer_short_le
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at hK
    change local₁.map ((MulAut.conj g).toMonoidHom.comp (fieldAction σ).toMonoidHom) = _ at hK
    rw [←map_map,show local₁.map (fieldAction σ).toMonoidHom = local₁ from local₁_field_map σ] at hK
    exact hK
  let p : shortPlaneStabilizer (F := F) := ⟨g,parabolic₁_le_shortPlaneStabilizer hg⟩
  have hblock (x : local₁ (F := F)) :
      shortSLHom ⟨a x.val, hK.le (mem_map_of_mem _ x.property)⟩ = shortSLHom x := by
    apply div_eq_one.mp
    rw [←map_div]
    apply (show _ ∈ (shortSLHom (F := F)).ker → _ from id)
    rw [shortSLHom_ker]
    exact hc x
  have htrace (x : local₁ (F := F)) :
      Matrix.trace (shortSLHom (local₁FieldEquiv σ x)).val = Matrix.trace (shortSLHom x).val := by
    let y : shortPlaneStabilizer (F := F) :=
      ⟨(local₁FieldEquiv σ x).val,
        parabolic₁_le_shortPlaneStabilizer ((show local₁ (F := F) ≤ parabolic₁ from sup_le_sup le_sup_left le_rfl) (local₁FieldEquiv σ x).property)⟩
    have he : shortRepresentation (p*y*p⁻¹) = (shortSLHom x).val := by
      have hh := congrArg Subtype.val (hblock x)
      exact (show shortRepresentation (p*y*p⁻¹) =
        (shortSLHom ⟨a x.val,hK.le (mem_map_of_mem _ x.property)⟩).val from by
          congr 1
          apply Subtype.ext
          exact (MulEquiv.congr_fun ha x.val).symm).trans hh
    have ht := congrArg Matrix.trace he
    rw [map_mul,map_mul,Matrix.trace_mul_cycle,←map_mul,inv_mul_cancel,map_one,one_mul] at ht
    exact ht
  have hs : σ = 1 := by
    apply RingEquiv.ext
    intro t
    let M : SL(2,F) := ⟨!![0,-1;1,t],by simp [Matrix.det_fin_two]⟩
    obtain ⟨x,hx⟩ := shortSLHom_surjective M
    have ht := htrace x
    rw [shortSLHom_field,hx] at ht
    simp only [Matrix.trace_fin_two] at ht
    change σ 0 + σ t = 0+t at ht
    simpa using ht
  have he : a = MulAut.conj g := by simpa only [hs,map_one,mul_one] using ha
  obtain ⟨k,hk⟩ := htwo
  have hgpow : g^(2^k)=1 := by
    apply conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    simpa only [he, map_pow, map_one] using hk
  exact ⟨⟨g,short_two_element g hg k hgpow⟩,he⟩

private theorem short_join_core (hq : 2 < Nat.card F)
    (U : Subgroup (MulAut (Model F)))
    (hn : U ≤ normalizer ((local₁ (F := F)).map MulAut.conj : Set _)) :
    ((local₁ (F := F)).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((local₁ (F := F)).map MulAut.conj).pCoreIn 2 := by
  have hi := conj_injective_of_center_eq_bot (model_center_eq_bot hq)
  apply join_pCore_eq_of_quotient_action_detection 2 _ U hn
  intro a ha htwo hc
  have hnorm : a ∈ normalizer ((local₁ (F := F)).map MulAut.conj : Set _) :=
    (sup_le ((local₁ (F := F)).map MulAut.conj).le_normalizer hn) ha
  have hK : (local₁ (F := F)).map a.toMonoidHom = local₁ := by
    apply Subgroup.map_injective hi
    have he : MulAut.conj.comp a.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp MulAut.conj := by
      ext x y
      simp
    rw [map_map,he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hnorm
  have hdiff (x : local₁ (F := F)) : a x.val / x.val ∈ radical₁ := by
    have hh := hc ⟨MulAut.conj x.val,mem_map_of_mem MulAut.conj x.property⟩
    change ⁅a,MulAut.conj x.val⁆ ∈ ((local₁ (F := F)).map MulAut.conj).pCoreIn 2 at hh
    rw [←map_pCoreIn_of_injective 2 _ _ hi,local₁_pCore] at hh
    have he : MulAut.conj (a x.val / x.val) = ⁅a,MulAut.conj x.val⁆ := by
      apply MulEquiv.ext
      intro y
      change (a x.val / x.val) * y * (a x.val / x.val)⁻¹ =
        a (x.val * a.symm (x.val⁻¹ * y * x.val) * x.val⁻¹)
      simp only [div_eq_mul_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    rw [←he] at hh
    exact (mem_map_iff_mem hi).mp hh
  obtain ⟨g,hg⟩ := short_detection hq a hK htwo hdiff
  rw [hg]
  exact mem_map_of_mem MulAut.conj g.property

private theorem core_eq {X : Type*} [Group X]
    (hq : 2 < Nat.card F) (K U : Subgroup X)
    (hn : U ≤ normalizer (K : Set X))
    (f : X →* MulAut (Model F)) (hf : Function.Injective f)
    (hK : K.map f = (local₁ (F := F)).map MulAut.conj) :
    (K ⊔ U).pCoreIn 2 = K.pCoreIn 2 := by
  apply Subgroup.map_injective hf
  rw [map_pCoreIn_of_injective 2 _ _ hf,map_pCoreIn_of_injective 2 _ _ hf,
    Subgroup.map_sup,hK]
  apply short_join_core hq (U.map f)
  rw [←hK]
  exact (map_mono hn).trans (le_normalizer_map f)

private def localEquiv {X : Type*} [Group X]
    (hq : 2 < Nat.card F) (K : Subgroup X)
    (f : X →* MulAut (Model F)) (hf : Function.Injective f)
    (hK : K.map f = (local₁ (F := F)).map MulAut.conj) : K ≃* local₁ (F := F) :=
  ((K.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hK)).trans
    ((local₁ (F := F)).equivMapOfInjective MulAut.conj
      (conj_injective_of_center_eq_bot (model_center_eq_bot hq))).symm
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.OriginalG2

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (F : Type) [Field F] [Finite F] [CharP F 2]

include d h hTH hp in
/-- The marked short local forces the nonbinary field before collapse. -/
theorem Preparation.g2_extension_parameter (i : Fin 2)
    (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) i →* MulAut (Model F))
    (hf : Function.Injective f)
    (hK : ((![L,R] i).subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) i)).map f =
      (local₁ (F := F)).map MulAut.conj) : 2 < Nat.card F := by
  by_contra hgt
  have htwo : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  let := G2Short.parabolic_solvable_of_card_two htwo
  let : Group.IsSolvable (local₁ (F := F)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show local₁ (F := F) ≤ parabolic₁ from sup_le_sup le_sup_left le_rfl))
      (inclusion_injective _)
  let j := (MulAut.conj : Model F →* MulAut (Model F)).comp (local₁ (F := F)).subtype
  have hj : j.range = (local₁ (F := F)).map MulAut.conj := by
    rw [MonoidHom.range_comp,range_subtype]
  let : Group.IsSolvable j.range := Group.isSolvable_of_surjective j.rangeRestrict_surjective
  let : Group.IsSolvable ((local₁ (F := F)).map MulAut.conj) := hj ▸ inferInstance
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) i
  have hKP : ![L,R] i ≤ P := le_sup_left.trans le_sup_left
  let q := ((subgroupOfEquivOfLe hKP).symm.trans
    (( (![L,R] i).subgroupOf P).equivMapOfInjective f hf)).trans (MulEquiv.subgroupCongr hK)
  let : Group.IsSolvable (![L,R] i) :=
    Group.isSolvable_of_isSolvable_injective (f := q.toMonoidHom) q.injective
  exact d.parabolics_not_solvable h hp i
    (((d.hypothesisF11 h hTH).parabolic_solvable_iff_local_quotient i).mpr inferInstance)

variable (hq : 2 < Nat.card F)
  (f : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 →* MulAut (Model F))
  (hf : Function.Injective f)
  (hR : (R.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 1)).map f =
    (local₁ (F := F)).map MulAut.conj)

omit [Finite G] in
include d hq hf hR in
/-- The literal right endpoint transports the native two-core identity. -/
theorem Preparation.g2_extension_right_core :
    (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  have hn : (sourceS L H).subgroupOf P ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [←subgroupOf_normalizer_eq hRP]
    exact comap_mono d.S_normalizes_right
  have hc := OriginalG2.core_eq hq (R.subgroupOf P)
    ((sourceS L H).subgroupOf P) hn f hf hR
  have hh := congrArg (Subgroup.map P.subtype) hc
  rw [map_pCoreIn_of_injective 2 _ _ P.subtype_injective,
    map_pCoreIn_of_injective 2 _ _ P.subtype_injective,Subgroup.map_sup,
    map_subgroupOf_eq_of_le hRP,map_subgroupOf_eq_of_le hSP] at hh
  exact hh

include d h hTH hq hf hR in
/-- The normalized original right Borel places S in the same selected R. -/
theorem Preparation.sourceS_le_right_of_g2_extension : sourceS L H ≤ R := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hRP : R ≤ P := le_sup_left.trans le_sup_left
  let e : R ≃* local₁ (F := F) := (subgroupOfEquivOfLe hRP).symm.trans
    (OriginalG2.localEquiv hq (R.subgroupOf P) f hf hR)
  let q := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans local₁CoreQuotientEquivPSL
  have hs := (d.hypothesisF11 h hTH).linear_local_sylow_factorization 1 F q
    d.right_borel_normalizes_sourceS
  change sourceS L H = (R ⊔ sourceS L H).pCoreIn 2 ⊔ (sourceS L H ⊓ R) at hs
  rw [d.g2_extension_right_core F hq f hf hR] at hs
  exact hs.le.trans (sup_le (map_subtype_le _) inf_le_right)

include h hq in
/-- The short local cannot mark the faithful left source factor, before collapse. -/
theorem Preparation.not_g2_short_extension_left
    (j : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 →* MulAut (Model F))
    (hj : Function.Injective j)
    (hL : (L.subgroupOf (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0)).map j =
      (local₁ (F := F)).map MulAut.conj) : False := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 0
  have hLP : L ≤ P := le_sup_left.trans le_sup_left
  let e : L ≃* local₁ (F := F) := (subgroupOfEquivOfLe hLP).symm.trans
    (OriginalG2.localEquiv hq (L.subgroupOf P) j hj hL)
  exact faithful_not_core_center_central h.local_mem.2 e local₁_core_center_le_center
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
