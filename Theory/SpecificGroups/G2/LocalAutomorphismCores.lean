module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.FieldCompatibility
public import Theory.AtlasPort.LinearGroups.G2.HighestRootWeakClosure
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Long
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Mathlib.Algebra.CharP.Reduced

/-!
# Two-cores of arbitrary automorphism overgroups of the G₂ locals

A quotient-trivial two-element normalizing either standard local is inner
by an element of that local. The inner-field description first writes the
actor as conjugation followed by coefficient transport. The actual SL₂
quotient detects the field part by traces. The short quotient uses its
plane representation; the long quotient uses the determinant-normalized
map on the full point parabolic. Frobenius injectivity then kills the
scalar character of the inner two-element.

This controls the two-core after adjoining any normalizing automorphism
subgroup, without a complement or splitting hypothesis. The source
application transports this identity to both original A5-marked factors.

Source: Aschbacher–Smith F.1.12, printed p.264. The short-side argument
extends the existing private proof in Chapter6's OriginalExtension/G2Core;
the native model and representation calculations come from the imported
ATLAS port, covered by LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace Atlas.G2.LocalAutomorphismCores
open LieParabolicSetup LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

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


private theorem normalizer_long_le :
    normalizer (local₂ (F := F) : Set (Model F)) ≤ parabolic₂ := by
  have h := le_normalizer_sylow_sup (local₂ (F := F)) (normalizer (local₂ (F := F) : Set (Model F)))
    le_normalizer le_rfl ((sylow (F := F)).subtype unipotent_le_local₂)
  have hs : ((sylow (F := F)).subtype unipotent_le_local₂ : Subgroup (local₂ (F := F))) =
      (unipotent (K := F)).subgroupOf local₂ := rfl
  rw [hs, map_subgroupOf_eq_of_le unipotent_le_local₂] at h
  change normalizer (local₂ (F := F) : Set (Model F)) ≤
    normalizer (unipotent (K := F) : Set (Model F)) ⊔ local₂ at h
  rw [SylowNormalizer.normalizer_unipotent] at h
  exact h.trans (sup_le borel_le_parabolic₂ local₂_le_parabolic₂)

omit [Finite F] in
private theorem long_two_element (g : Model F) (hg : g ∈ parabolic₂)
    (k : ℕ) (hk : g^(2^k)=1) : g ∈ local₂ := by
  let p : parabolic₂ (F := F) := ⟨g,hg⟩
  have hp : p^(2^k)=1 := Subtype.ext hk
  have hd : (HigherParabolicRadical.Long.scalarHom p)^(2^k)=1 := by
    rw [←map_pow,hp,map_one]
  apply (HigherParabolicRadical.Long.scalar_eq_one_iff p).mp
  apply Units.ext
  apply iterateFrobenius_inj F 2 k
  have he := congrArg (fun z : Fˣ => (z : F)) hd
  simpa only [iterateFrobenius_def,one_pow,Units.val_pow_eq_pow_val,Units.val_one] using he

private theorem long_detection (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) (hK : (local₂ (F := F)).map a.toMonoidHom = local₂)
    (htwo : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x : local₂ (F := F), a x.val / x.val ∈ radical₂) :
    ∃ g : local₂ (F := F), a = MulAut.conj g.val := by
  obtain ⟨g,σ,ha⟩ := exists_inner_field hq a
  have hg : g ∈ parabolic₂ := by
    apply normalizer_long_le
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [ha] at hK
    change local₂.map ((MulAut.conj g).toMonoidHom.comp (fieldAction σ).toMonoidHom) = _ at hK
    rw [←map_map,show local₂.map (fieldAction σ).toMonoidHom = local₂ from local₂_field_map σ] at hK
    exact hK
  let p : parabolic₂ (F := F) := ⟨g,hg⟩
  have hblock (x : local₂ (F := F)) :
      longSLHom ⟨a x.val, hK.le (mem_map_of_mem _ x.property)⟩ = longSLHom x := by
    apply div_eq_one.mp
    rw [←map_div]
    apply (show _ ∈ (longSLHom (F := F)).ker → _ from id)
    rw [longSLHom_ker]
    exact hc x
  have htrace (x : local₂ (F := F)) :
      Matrix.trace (longSLHom (local₂FieldEquiv σ x)).val = Matrix.trace (longSLHom x).val := by
    let y : parabolic₂ (F := F) :=
      ⟨(local₂FieldEquiv σ x).val, local₂_le_parabolic₂ (local₂FieldEquiv σ x).property⟩
    have he : HigherParabolicRadical.Long.fullSLHom (p*y*p⁻¹) = longSLHom x := by
      calc
        _ = HigherParabolicRadical.Long.fullSLHom
            ⟨a x.val, local₂_le_parabolic₂ (hK.le (mem_map_of_mem _ x.property))⟩ := by
          congr 1
          apply Subtype.ext
          exact (MulEquiv.congr_fun ha x.val).symm
        _ = _ := (HigherParabolicRadical.Long.fullSLHom_local _).trans (hblock x)
    have ht := congrArg (fun M : SL(2,F) => Matrix.trace M.val) he
    rw [map_mul,map_mul,map_inv] at ht
    have ht' : Matrix.trace (HigherParabolicRadical.Long.fullSLHom y).val =
        Matrix.trace (longSLHom x).val := by
      calc
        _ = Matrix.trace ((HigherParabolicRadical.Long.fullSLHom p) *
          (HigherParabolicRadical.Long.fullSLHom y) *
          (HigherParabolicRadical.Long.fullSLHom p)⁻¹).val := by
            change _ = Matrix.trace (_ * _ * _)
            rw [Matrix.trace_mul_cycle]
            simp only [←Matrix.SpecialLinearGroup.coe_mul,inv_mul_cancel,one_mul]
        _ = _ := ht
    simpa only [y,HigherParabolicRadical.Long.fullSLHom_local] using ht'
  have hs : σ = 1 := by
    apply RingEquiv.ext
    intro t
    let M : SL(2,F) := ⟨!![0,-1;1,t],by simp [Matrix.det_fin_two]⟩
    obtain ⟨x,hx⟩ := longSLHom_surjective M
    have ht := htrace x
    rw [longSLHom_field,hx] at ht
    simp only [Matrix.trace_fin_two] at ht
    change σ 0 + σ t = 0+t at ht
    simpa using ht
  have he : a = MulAut.conj g := by simpa only [hs,map_one,mul_one] using ha
  obtain ⟨k,hk⟩ := htwo
  have hgpow : g^(2^k)=1 := by
    apply conj_injective_of_center_eq_bot (model_center_eq_bot hq)
    simpa only [he,map_pow,map_one] using hk
  exact ⟨⟨g,long_two_element g hg k hgpow⟩,he⟩

omit [CharP F 2] in
private theorem local_join_core (hq : 2 < Nat.card F) (K : Subgroup (Model F))
    (hdetect : ∀ (a : MulAut (Model F)), K.map a.toMonoidHom = K →
      (∃ k : ℕ, a^(2^k)=1) → (∀ x : K, a x.val / x.val ∈ K.pCoreIn 2) →
      ∃ g : K, a = MulAut.conj g.val)
    (U : Subgroup (MulAut (Model F)))
    (hn : U ≤ normalizer (K.map MulAut.conj : Set _)) :
    (K.map MulAut.conj ⊔ U).pCoreIn 2 =
      (K.map MulAut.conj).pCoreIn 2 := by
  have hi := conj_injective_of_center_eq_bot (model_center_eq_bot hq)
  apply join_pCore_eq_of_quotient_action_detection 2 _ U hn
  intro a ha htwo hc
  have hnorm : a ∈ normalizer (K.map MulAut.conj : Set _) :=
    (sup_le (K.map MulAut.conj).le_normalizer hn) ha
  have hK : K.map a.toMonoidHom = K := by
    apply Subgroup.map_injective hi
    have he : MulAut.conj.comp a.toMonoidHom =
        (MulAut.conj a).toMonoidHom.comp MulAut.conj := by
      ext x y
      simp
    rw [map_map,he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp hnorm
  have hdiff (x : K) : a x.val / x.val ∈ K.pCoreIn 2 := by
    have hh := hc ⟨MulAut.conj x.val,mem_map_of_mem MulAut.conj x.property⟩
    change ⁅a,MulAut.conj x.val⁆ ∈ (K.map MulAut.conj).pCoreIn 2 at hh
    rw [←map_pCoreIn_of_injective 2 _ _ hi] at hh
    have he : MulAut.conj (a x.val / x.val) = ⁅a,MulAut.conj x.val⁆ := by
      apply MulEquiv.ext
      intro y
      change (a x.val / x.val) * y * (a x.val / x.val)⁻¹ =
        a (x.val * a.symm (x.val⁻¹ * y * x.val) * x.val⁻¹)
      simp only [div_eq_mul_inv,map_mul,map_inv,MulEquiv.apply_symm_apply]
      group
    rw [←he] at hh
    exact (mem_map_iff_mem hi).mp hh
  obtain ⟨g,hg⟩ := hdetect a hK htwo hdiff
  rw [hg]
  exact mem_map_of_mem MulAut.conj g.property


/-- Adjoining any subgroup of automorphisms normalizing a standard local
leaves its embedded two-core unchanged. No complement is required. -/
theorem join_core (hq : 2 < Nat.card F) (short : Bool)
    (U : Subgroup (MulAut (Model F)))
    (hn : U ≤ normalizer (((if short then local₁ else local₂) : Subgroup (Model F)).map
      MulAut.conj : Set _)) :
    ((((if short then local₁ else local₂) : Subgroup (Model F)).map MulAut.conj) ⊔ U).pCoreIn 2 =
      (((if short then local₁ else local₂) : Subgroup (Model F)).map MulAut.conj).pCoreIn 2 := by
  apply local_join_core hq _ ?_ U hn
  intro a hK htwo hc
  cases short
  · exact long_detection hq a hK htwo (by
      intro x
      have hh := hc x
      change a x.val / x.val ∈ (local₂ (F := F)).pCoreIn 2 at hh
      rwa [local₂_pCoreIn] at hh)
  · exact short_detection hq a hK htwo (by
      intro x
      have hh := hc x
      change a x.val / x.val ∈ (local₁ (F := F)).pCoreIn 2 at hh
      rwa [local₁_pCore] at hh)

end Atlas.G2.LocalAutomorphismCores

