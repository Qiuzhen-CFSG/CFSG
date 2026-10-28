module
public import Theory.SpecificGroups.SL2.NormalBorelCore

/-!
# Inner actions of a normalizing maximal two-core on binary SL₂

A two-core element which normalizes the component preserves its actual
Sylow intersection. Commutators with the actual Borel lie in that Sylow,
so the proved semilinear Borel-quotient detector makes its action inner.
The original element therefore lies in the component times its centralizer.
Ambient normality of the component and faithfulness are not assumed.

Source: Aschbacher–Smith E.2.7, printed p.219, paired Bender placement.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
theorem normalizing_borel_twoCore_le_sup_centralizer {n : ℕ} (hF : Nat.card F = 2^n)
    (K : Subgroup H) (e : K ≃* PSL(2,F))
    (T : Sylow 2 H) (M : Subgroup H) (hTM : (T : Subgroup H) ≤ M)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = (T : Subgroup H).subgroupOf K)
    (hB : M.subgroupOf K = normalizer (S : Set K))
    (hQN : M.pCoreIn 2 ≤ normalizer (K : Set H)) :
    M.pCoreIn 2 ≤ K ⊔ centralizer (K : Set H) := by
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup H) := by
    have h := pCoreIn_le_sylow M (T.subtype hTM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using h
  rintro v ⟨v,hv,rfl⟩
  let vn : normalizer (K : Set H) := ⟨v,hQN (mem_map_of_mem M.subtype hv)⟩
  let a : MulAut K := K.normalizerMonoidHom vn
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
  have hcentral : (v : H) * (e.symm g : H)⁻¹ ∈ centralizer (K : Set H) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hh := congrArg (fun z : MulAut K => (z ((e.symm g)⁻¹ * ⟨y,hy⟩ * (e.symm g)) : H)) hinner
    change (v : H) * ((e.symm g : H)⁻¹ * y * (e.symm g : H)) * (v : H)⁻¹ =
      (e.symm g : H) * ((e.symm g : H)⁻¹ * y * (e.symm g : H)) * (e.symm g : H)⁻¹ at hh
    have he : ((v:H) * (e.symm g : H)⁻¹) * y * ((v:H) * (e.symm g : H)⁻¹)⁻¹ = y := by
      calc
        _ = (v:H) * ((e.symm g : H)⁻¹ * y * (e.symm g : H)) * (v:H)⁻¹ := by group
        _ = (e.symm g : H) * ((e.symm g : H)⁻¹ * y * (e.symm g : H)) * (e.symm g : H)⁻¹ := hh
        _ = y := by group
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  have hh := (K ⊔ centralizer (K : Set H)).mul_mem
    (mem_sup_right hcentral) (mem_sup_left (e.symm g).property)
  change (v:H) ∈ K ⊔ centralizer (K : Set H)
  simpa only [inv_mul_cancel_right] using hh
end Matrix.ProjectiveSpecialLinearGroup
