module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticField

/-!
# The two-core of a quintic Sylow supplement in a faithful rank-one extension

Inside a group with a normal self-centralizing PSL₂(16), a subgroup containing
the full Sylow and an actual quintic subgroup of the inner Borel has its
whole two-core inside the normal layer. The quintic displacement detector
removes the field part of every element of that core. If the subgroup
normalizes the inner Sylow, that Sylow is exactly its two-core.

Source: the assertion S=O₂(XT)=T_L Q in Aschbacher--Smith 6.1.4, printed p.665.
The later application must retain the original quotient map and its kernel.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]

/-- A quintic inner-Borel subgroup detects all outer elements of the two-core. -/
theorem normal_quintic_twoCore_le
    (hF : Nat.card F = 16) (K : Subgroup H) [K.Normal] (e : K ≃* PSL(2,F))
    (T : Sylow 2 H) (M : Subgroup H) (hTM : (T : Subgroup H) ≤ M)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = (T : Subgroup H).subgroupOf K)
    (D : Subgroup K) (hD : Nat.card D = 5) (hDN : D ≤ normalizer (S : Set K))
    (hDM : D.map K.subtype ≤ M) (hC : centralizer (K : Set H) = ⊥) :
    M.pCoreIn 2 ≤ K := by
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup H) := by
    have hh := pCoreIn_le_sylow M (T.subtype hTM)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hh
  rintro v ⟨v,hv,rfl⟩
  let a : MulAut K := MulAut.conjNormal (v : H)
  have hvT : (v : H) ∈ T := hQT (mem_map_of_mem M.subtype hv)
  have ha : (S : Subgroup K).map a.toMonoidHom = S := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hS] at hx ⊢
      exact (T : Subgroup H).mul_mem ((T : Subgroup H).mul_mem hvT hx)
        ((T : Subgroup H).inv_mem hvT)
    · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
  have hfix : ∀ d ∈ D, d⁻¹ * a d ∈ S := by
    intro d hd
    let dd : M := ⟨d,hDM (mem_map_of_mem K.subtype hd)⟩
    have hdq : dd⁻¹ * v * dd * v⁻¹ ∈ pCore 2 M :=
      (pCore 2 M).mul_mem (by simpa only [inv_inv] using
        (inferInstance : (pCore 2 M).Normal).conj_mem v hv dd⁻¹)
        ((pCore 2 M).inv_mem hv)
    have ht := hQT (mem_map_of_mem M.subtype hdq)
    change d⁻¹ * a d ∈ (S : Subgroup K)
    rw [hS]
    change (d : H)⁻¹ * ((v : H) * (d : H) * (v : H)⁻¹) ∈ (T : Subgroup H)
    change (d : H)⁻¹ * (v : H) * (d : H) * (v : H)⁻¹ ∈ (T : Subgroup H) at ht
    simpa only [mul_assoc] using ht
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have hb : (Q : Subgroup PSL(2,F)).map b.toMonoidHom = Q := by
    change ((S : Subgroup K).map e.toMonoidHom).map b.toMonoidHom = _
    have he : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
      ext x
      change e (a (e.symm (e x))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [Subgroup.map_map,he,←Subgroup.map_map,ha]
    rfl
  have hBQ : D.map e.toMonoidHom ≤ normalizer (Q : Set PSL(2,F)) :=
    (map_mono hDN).trans ((S : Subgroup K).le_normalizer_map e.toMonoidHom)
  have hbc : Nat.card (D.map e.toMonoidHom) = 5 := by
    rw [card_map_of_injective e.injective,hD]
  have hbf : ∀ x ∈ D.map e.toMonoidHom, x⁻¹ * b x ∈ (Q : Subgroup PSL(2,F)) := by
    rintro _ ⟨d,hd,rfl⟩
    have hh := mem_map_of_mem e.toMonoidHom (hfix d hd)
    change (e d)⁻¹ * e (a (e.symm (e d))) ∈ (S : Subgroup K).map e.toMonoidHom
    simpa only [map_mul,map_inv,e.symm_apply_apply,MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨g,hg⟩ := quintic_sylow_displacements_inner hF Q (D.map e.toMonoidHom) hbc hBQ b hb hbf
  have hinner : a = MulAut.conj (e.symm g) := by
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj,e.apply_symm_apply]
    exact hg
  have hin : (v : H) ∈ (MulAut.innerSubgroup K).comap MulAut.conjNormal :=
    ⟨e.symm g,hinner.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup,hC,sup_bot_eq] at hin
  exact hin

/-- In the same faithful extension, normalizing the inner Sylow identifies
the exact two-core of the quintic supplement. -/
theorem normal_quintic_twoCore_eq
    (hF : Nat.card F = 16) (K : Subgroup H) [K.Normal] (e : K ≃* PSL(2,F))
    (T : Sylow 2 H) (M : Subgroup H) (hTM : (T : Subgroup H) ≤ M)
    (S : Sylow 2 K) (hS : (S : Subgroup K) = (T : Subgroup H).subgroupOf K)
    (D : Subgroup K) (hD : Nat.card D = 5) (hDN : D ≤ normalizer (S : Set K))
    (hDM : D.map K.subtype ≤ M) (hC : centralizer (K : Set H) = ⊥)
    (hMN : M ≤ normalizer (((T : Subgroup H) ⊓ K : Subgroup H) : Set H)) :
    M.pCoreIn 2 = (T : Subgroup H) ⊓ K := by
  apply le_antisymm
  · apply le_inf
    · have hh := pCoreIn_le_sylow M (T.subtype hTM)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM] using hh
    · exact normal_quintic_twoCore_le hF K e T M hTM S hS D hD hDN hDM hC
  · exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans hTM) hMN

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
