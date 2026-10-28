module
public import Theory.SpecificGroups.SL2.EvenBorelResidual.Semilinear
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Binary linear Borel two-cores in normal extensions

A root-preserving automorphism trivial on the Borel quotient is inner:
semilinear coverage makes its quotient action the field action on the full
unit group, which detects every nonzero field element. Sylow conjugacy gives
the same detector at any prescribed Sylow. In a faithful normal extension,
the maximal two-core lies in T, and its Borel displacements lie in T ∩ K;
the detector therefore places that whole two-core inside the normal layer.

Source: Aschbacher–Smith E.2.7, printed p.218, normal linear Bender branch.
-/

public section
open Subgroup Matrix Atlas
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open BenderSuzuki.Converse OddBorel
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem inner_of_borel_quotient_fixed {n : ℕ} (hF : Nat.card F = 2^n)
    (a : MulAut PSL(2,F))
    (ha : (kernel F).map a.toMonoidHom = kernel F)
    (hfix : ∀ x ∈ borel F, x⁻¹ * a x ∈ kernel F) : ∃ g, a = MulAut.conj g := by
  have hcoverage : ∀ β : MulAut PSL(2,F),
      ∃ (g : PSL(2,F)) (σ : F ≃+* F), β = MulAut.conj g * fieldEquivPSL 2 σ := by
    intro β
    obtain ⟨g,σ,hg⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage β
    have heq : BenderSuzuki.ZD.Linear.fieldAut σ = fieldEquivPSL 2 σ := by
      ext x
      obtain ⟨y,rfl⟩ := BenderSuzuki.Converse.pi_surjective x
      rw [BenderSuzuki.ZD.Linear.fieldAut_apply_pi]
      change _ = fieldEquivPSL 2 σ (QuotientGroup.mk' _ y)
      rw [fieldEquivPSL_mk]
      rfl
    exact ⟨g,σ,heq ▸ hg⟩
  obtain ⟨g,σ,he⟩ := hcoverage a
  have hg := inner_factor_mem_borel F g σ (he ▸ ha)
  have hσ : σ = 1 := by
    have hu (u : Fˣ) : Units.map σ.toMonoidHom u = u := by
      obtain ⟨x,hx⟩ := torusProjection_surjective F u
      have hh := (borelActor_commutator_mem_core_iff F hF ⟨g,hg⟩ σ x).mp (by
        rw [twoCoreIn_eq_kernel F hF]
        rw [← he]
        exact hfix x x.property)
      rwa [hx] at hh
    apply RingEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · exact congrArg Units.val (hu (Units.mk0 x hx))
  refine ⟨g,?_⟩
  rw [he,hσ]
  have hf : fieldEquivPSL 2 (1 : F ≃+* F) = 1 := by
    change RankOneFieldAutomorphisms.pslFieldAction (1 : F ≃+* F) = 1
    exact RankOneFieldAutomorphisms.pslFieldAction.map_one
  rw [hf,mul_one]

theorem inner_of_sylow_borel_quotient_fixed {n : ℕ} (hF : Nat.card F = 2^n)
    (S : Sylow 2 PSL(2,F)) (a : MulAut PSL(2,F))
    (ha : (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hfix : ∀ x ∈ normalizer (S : Set PSL(2,F)), x⁻¹ * a x ∈ S) :
    ∃ g, a = MulAut.conj g := by
  obtain ⟨c,hcS,hcB⟩ := sylow_normalizer_conjugate F S
  let e := MulAut.conj c
  let b := MulAut.congr e.symm a
  have hb : (kernel F).map b.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map a.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map,Subgroup.map_map]
        rfl
      _ = (S : Subgroup PSL(2,F)).map e.symm.toMonoidHom := by rw [hcS,ha]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcS
  have hbfix : ∀x ∈ borel F, x⁻¹ * b x ∈ kernel F := by
    intro x hx
    have hex : e x ∈ normalizer (S : Set PSL(2,F)) := by
      rw [← hcB]
      exact mem_map_of_mem e.toMonoidHom hx
    have hd := hfix (e x) hex
    have hm := mem_map_of_mem e.symm.toMonoidHom hd
    have hpre : (S : Subgroup PSL(2,F)).map e.symm.toMonoidHom = kernel F :=
      (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcS
    rw [hpre] at hm
    change e.symm ((e x)⁻¹ * a (e x)) ∈ kernel F at hm
    change x⁻¹ * e.symm (a (e x)) ∈ kernel F
    simpa only [map_mul,map_inv,e.symm_apply_apply] using hm
  obtain ⟨g,hg⟩ := inner_of_borel_quotient_fixed hF b hb hbfix
  refine ⟨e g, (MulAut.congr e.symm).injective ?_⟩
  rw [MulAut.congr_conj,e.symm_apply_apply]
  exact hg
end Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear

namespace Matrix.ProjectiveSpecialLinearGroup
open Subgroup
open scoped MatrixGroups
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

theorem normal_borel_twoCore_le {n : ℕ} (hF : Nat.card F = 2^n)
    (K : Subgroup H) [K.Normal] (e : K ≃* PSL(2,F))
    (T : Sylow 2 H) (M : Subgroup H) (hTM : (T : Subgroup H) ≤ M)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = (T : Subgroup H).subgroupOf K)
    (hB : M.subgroupOf K = normalizer (S : Set K))
    (hC : centralizer (K : Set H) = ⊥) : M.pCoreIn 2 ≤ K := by
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup H) := by
    have h := pCoreIn_le_sylow M (T.subtype hTM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using h
  rintro v ⟨v,hv,rfl⟩
  let a : MulAut K := MulAut.conjNormal (v : H)
  have hvT : (v : H) ∈ T := hQT (mem_map_of_mem M.subtype hv)
  have ha : (S : Subgroup K).map a.toMonoidHom = S := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hS] at hx ⊢
      exact (T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem hvT hx)
        ((T : Subgroup H).inv_mem hvT)
    · rw [card_map_of_injective (f := a.toMonoidHom) (K := (S : Subgroup K)) a.injective]
  have hfix : ∀ x ∈ normalizer (S : Set K), x⁻¹ * a x ∈ S := by
    intro x hx
    have hxM : (x : H) ∈ M := hB.ge hx
    let xx : M := ⟨x,hxM⟩
    have hd : xx⁻¹ * v * xx * v⁻¹ ∈ pCore 2 M :=
      (pCore 2 M).mul_mem (by simpa only [inv_inv] using (inferInstance : (pCore 2 M).Normal).conj_mem v hv xx⁻¹)
        ((pCore 2 M).inv_mem hv)
    have ht := hQT (mem_map_of_mem M.subtype hd)
    change x⁻¹ * a x ∈ (S : Subgroup K)
    rw [hS]
    change (x : H)⁻¹ * ((v : H) * (x : H) * (v : H)⁻¹) ∈ (T : Subgroup H)
    change ((x : H)⁻¹ * (v : H) * (x : H) * (v : H)⁻¹) ∈ (T : Subgroup H) at ht
    simpa only [mul_assoc] using ht
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : (Q : Subgroup PSL(2,F)).map b.toMonoidHom = Q := by
    change ((S : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = _
    have hh : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e (a (e.symm (e x))) = e (a x)
      rw [e.symm_apply_apply]
    rw [Subgroup.map_map,hh,←Subgroup.map_map,ha]
    rfl
  have hNb : (normalizer (S : Set K)).map e.toMonoidHom = normalizer (Q : Set PSL(2,F)) := by
    change (normalizer ((S : Subgroup K) : Set K)).map e.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective (S : Subgroup K) e.bijective]
    rfl
  have hbfix : ∀x ∈ normalizer (Q : Set PSL(2,F)), x⁻¹ * b x ∈ Q := by
    intro x hx
    rw [← hNb] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem e.toMonoidHom (hfix y hy)
    change e (y⁻¹ * a y) ∈ (Q : Subgroup PSL(2,F)) at hh
    change (e y)⁻¹ * e (a (e.symm (e y))) ∈ (Q : Subgroup PSL(2,F))
    simpa only [map_mul,map_inv,e.symm_apply_apply] using hh
  obtain ⟨g,hg⟩ := EvenBorelResidual.Semilinear.inner_of_sylow_borel_quotient_fixed hF Q b hb hbfix
  have hinner : a = MulAut.conj (e.symm g) := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hg
  have hin : (v : H) ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal :=
    ⟨e.symm g,hinner.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup,hC,sup_bot_eq] at hin
  exact hin
end Matrix.ProjectiveSpecialLinearGroup
