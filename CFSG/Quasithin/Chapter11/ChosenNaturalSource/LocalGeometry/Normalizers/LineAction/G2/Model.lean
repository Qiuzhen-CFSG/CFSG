module
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer
public import Theory.GroupTheory.SylowKernelCore
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.StandardLocalExtensions
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Long

/-!
# The two-core of an automorphism extension of the G₂ point residual

A two-element preserving the long local and acting trivially on its SL₂
quotient has trivial field part: the full parabolic quotient action is inner,
and the SL₂ trace test detects the field automorphism. Its remaining scalar
has odd order, so the actor is inner from the local itself. The local core
criterion therefore proves that adjoining a normalizing subgroup in Aut(G₂)
does not enlarge the embedded point-local two-core.

The application in G2.Comparison uses the original marked Sylow action.
Source: Aschbacher--Smith F.1.12, printed p.264, and the radical identity
used in 11.1.5 and 11.2.3, pp.765--766,768--769. The concrete octonion and
field-action conventions are the licensed ATLAS imports; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups commutatorElement
open Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.LieAutomorphismExtensions
open Atlas.G2.HigherParabolicRadical.Long
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem local_normalizer (hq : 2 < Nat.card F) :
    normalizer (local₂ (F := F) : Set (Model F)) = parabolic₂ := by
  let := Atlas.G2.isSimple hq
  have hne : local₂ (F := F) ≠ ⊥ := by
    intro h
    have hr : rootE (1 : F) ∈ local₂ := unipotent_le_local₂ (subset_closure (by simp))
    have he : rootE (1 : F) = rootE 0 := by simpa only [h,mem_bot,rootE_zero] using hr
    exact one_ne_zero (rootE_injective he)
  have hn : normalizer (local₂ (F := F) : Set (Model F)) ≠ ⊤ := by
    intro h
    let : (local₂ (F := F)).Normal := normalizer_eq_top_iff.mp h
    rcases (inferInstance : (local₂ (F := F)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hne hb
    · exact HigherFieldResiduals.parabolic₂_isCoatom.1
        (top_le_iff.mp (ht ▸ local₂_le_parabolic₂))
  exact ((isCoatom_iff_ge_of_le.mp HigherFieldResiduals.parabolic₂_isCoatom).2 _ hn
    parabolic₂_le_normalizer_local₂).antisymm parabolic₂_le_normalizer_local₂

omit [Finite F] in
private theorem field_preserves_local (σ : F ≃+* F) :
    (local₂ (F := F)).map (fieldAction σ).toMonoidHom = local₂ := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (longFieldAction σ ⟨x,hx⟩).property
  · intro x hx
    refine ⟨(longFieldAction σ⁻¹ ⟨x,hx⟩).val,
      (longFieldAction σ⁻¹ ⟨x,hx⟩).property,?_⟩
    change fieldAction σ (fieldAction σ⁻¹ x) = x
    rw [map_inv]
    exact (fieldAction σ).apply_symm_apply x

private theorem two_element_local_kernel (hq : 2 < Nat.card F)
    (a : MulAut (Model F)) (ha : (local₂ (F := F)).map a.toMonoidHom = local₂)
    (htwo : ∃ n : ℕ, a ^ (2 ^ n) = 1)
    (hc : ∀ l : local₂ (F := F), a l.val / l.val ∈ (local₂ (F := F)).pCoreIn 2) :
    ∃ g : local₂ (F := F), a = MulAut.conj g.val := by
  obtain ⟨g,σ,rfl⟩ := exists_inner_field hq a
  have hg : g ∈ parabolic₂ (F := F) := by
    rw [← local_normalizer hq,mem_normalizer_iff_map_conj_eq]
    have he : (MulAut.conj g * fieldAction σ).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (fieldAction σ).toMonoidHom := rfl
    rw [he,← Subgroup.map_map,field_preserves_local] at ha
    exact ha
  let gp : parabolic₂ (F := F) := ⟨g,hg⟩
  have he (l : local₂ (F := F)) :
      fullSLHom gp * Atlas.fieldEquivSL 2 σ (longSLHom l) *
        (fullSLHom gp)⁻¹ = longSLHom l := by
    let y : local₂ (F := F) := ⟨(MulAut.conj g * fieldAction σ) l.val,
      ha.le (mem_map_of_mem _ l.property)⟩
    have hy : longSLHom y = longSLHom l := by
      have hh : y / l ∈ (longSLHom (F := F)).ker := by
        rw [longSLHom_ker]
        change (MulAut.conj g * fieldAction σ) l.val / l.val ∈ radical₂
        simpa only [local₂_pCoreIn] using hc l
      change longSLHom (y / l) = 1 at hh
      rw [map_div] at hh
      exact div_eq_one.mp hh
    have hprod : inclusion local₂_le_parabolic₂ y =
        gp * inclusion local₂_le_parabolic₂ (longFieldAction σ l) * gp⁻¹ := rfl
    rw [← fullSLHom_local y] at hy
    change fullSLHom (inclusion local₂_le_parabolic₂ y) = _ at hy
    rw [hprod,map_mul,map_mul,map_inv] at hy
    have hlocal : fullSLHom (inclusion local₂_le_parabolic₂ (longFieldAction σ l)) =
        longSLHom (longFieldAction σ l) := fullSLHom_local _
    have hfield : longSLHom (longFieldAction σ l) =
        Atlas.fieldEquivSL 2 σ (longSLHom l) := longSLHom_field σ l
    rw [hlocal,hfield] at hy
    exact hy
  have hσ : σ = 1 := by
    apply Atlas.RankOneFieldAutomorphisms.field_eq_one_of_SL_inner σ ((fullSLHom gp)⁻¹)
    apply MulEquiv.ext
    intro x
    obtain ⟨l,rfl⟩ := longSLHom_surjective x
    have hh := he l
    change Atlas.fieldEquivSL 2 σ (longSLHom l) =
      (fullSLHom gp)⁻¹ * longSLHom l * ((fullSLHom gp)⁻¹)⁻¹
    simpa only [inv_inv,mul_assoc] using
      (eq_inv_mul_iff_mul_eq).mpr (mul_inv_eq_iff_eq_mul.mp hh)
  simp only [hσ,map_one,mul_one] at htwo ⊢
  have hgLocal : g ∈ local₂ (F := F) := by
    apply (scalar_eq_one_iff gp).mp
    obtain ⟨n,hn⟩ := htwo
    have hgpow : g ^ (2^n) = 1 := by
      apply Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hq)
      simpa only [map_pow,map_one] using hn
    have hpow : scalarHom gp ^ (2^n) = 1 := by
      rw [←map_pow,show gp ^ (2^n) = 1 from Subtype.ext hgpow,map_one]
    have ho : Odd (Nat.card Fˣ) := by
      rw [Nat.card_units]
      let := Fintype.ofFinite F
      obtain ⟨n,_,hn⟩ := FiniteField.card F 2
      rw [Nat.card_eq_fintype_card,hn]
      exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
        (even_two.pow_of_ne_zero (ne_of_gt n.pos)) odd_one
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((Nat.coprime_two_right.mpr ho).pow_right n)
      (orderOf_dvd_natCard _) (orderOf_dvd_of_pow_eq_one hpow))
  exact ⟨⟨g,hgLocal⟩,rfl⟩

omit [CharP F 2] in
theorem inner_injective (hq : 2 < Nat.card F) :
    Function.Injective (MulAut.conj : Model F →* MulAut (Model F)) :=
  Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hq)

omit [CharP F 2] in
theorem preserves_of_normalizes_inner (hq : 2 < Nat.card F)
    (U : Subgroup (Model F)) (a : MulAut (Model F))
    (ha : a ∈ normalizer (U.map MulAut.conj : Set _)) : U.map a.toMonoidHom = U := by
  rw [mem_normalizer_iff_map_conj_eq] at ha
  have he : (MulAut.conj a : MulAut (Model F) →* _).comp MulAut.conj =
      MulAut.conj.comp a.toMonoidHom := by ext x y; simp
  rw [Subgroup.map_map,he,← Subgroup.map_map] at ha
  exact map_injective (inner_injective hq) ha

theorem local_join_core_in_aut (hq : 2 < Nat.card F)
    (U : Subgroup (MulAut (Model F)))
    (hU : ∀ a ∈ U, (local₂ (F := F)).map a.toMonoidHom = local₂) :
    ((local₂ (F := F)).map MulAut.conj ⊔ U).pCoreIn 2 =
      ((local₂ (F := F)).map MulAut.conj).pCoreIn 2 := by
  let K := (local₂ (F := F)).map MulAut.conj
  have hn : U ≤ normalizer (K : Set (MulAut (Model F))) := by
    intro a ha
    rw [mem_normalizer_iff_map_conj_eq]
    have he : (MulAut.conj a).toMonoidHom.comp MulAut.conj =
        MulAut.conj.comp a.toMonoidHom := by ext x y; simp
    change K.map (MulAut.conj a).toMonoidHom = K
    dsimp only [K]
    rw [Subgroup.map_map,he,← Subgroup.map_map,hU a ha]
  apply join_pCore_eq_of_quotient_action_detection 2 K U hn
  intro a ha ht hc
  obtain ⟨l,hl⟩ := two_element_local_kernel hq a
    (preserves_of_normalizes_inner hq _ a ((sup_le K.le_normalizer hn) ha)) ht (by
      intro l
      have hh := hc ⟨MulAut.conj l.val,mem_map_of_mem _ l.property⟩
      change ⁅a,MulAut.conj l.val⁆ ∈ K.pCoreIn 2 at hh
      have he : MulAut.conj (a l.val / l.val) = ⁅a,MulAut.conj l.val⁆ := by
        ext x
        simp [commutatorElement_def,div_eq_mul_inv,mul_assoc]
      rw [← map_pCoreIn_of_injective 2 local₂ MulAut.conj (inner_injective hq),←he] at hh
      exact (Subgroup.mem_map_iff_mem (inner_injective hq)).mp hh)
  exact hl ▸ mem_map_of_mem MulAut.conj l.property
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.G2Line
