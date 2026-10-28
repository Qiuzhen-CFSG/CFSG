module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.TorusSplitting
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.InvolutiveAction

/-!
# One field marking for an original outer involution

An involution in T outside the original S normalizes both original root
planes. It moves Z(S), by the proved equality C_T(Z(S))=S. Applying the
intrinsic coordinate normalization therefore produces a single marking of S
in which this actual involution acts by the same nontrivial field involution
on all three coordinates. Both original root planes retain their identities,
up to the orientation already allowed in the source comparison.

This discharges the field-action premise for the exceptional Sylow construction;
it assumes no full-normalizer or ambient model realization.
Source: Aschbacher--Smith §5.3.7 and F.4.29(2), printed pp.660 and 289
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

theorem Preparation.linear_mark_outer_involution
    (t : G) (ht : t ∈ (T : Subgroup G)) (ht2 : orderOf t=2)
    (htS : t ∉ sourceS L H) :
    ∃ (e : U F ≃* sourceS L H) (σ : F ≃+* F),
      σ ≠ 1 ∧ Function.Involutive σ ∧
      (((V₁ F).map (markedHom F (sourceS L H) e) = L.pCoreIn 2 ∧
        (V₂ F).map (markedHom F (sourceS L H) e) = (residual H).pCoreIn 2) ∨
       ((V₁ F).map (markedHom F (sourceS L H) e) = (residual H).pCoreIn 2 ∧
        (V₂ F).map (markedHom F (sourceS L H) e) = L.pCoreIn 2)) ∧
      ∀ u : U F, t * markedHom F (sourceS L H) e u * t⁻¹ =
        markedHom F (sourceS L H) e ⟨σ u.x,σ u.y,σ u.c⟩ := by
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  let j := markedHom F (sourceS L H) e
  have hj : Function.Injective j := markedHom_injective F (sourceS L H) e
  have htN : t ∈ normalizer (sourceS L H : Set G) :=
    sylow_normalizes_sourceS h.sylow_normalizes hH.1.1.2 ht
  let a : MulAut (U F) := MulAut.congr e.symm
    ((sourceS L H).normalizerMonoidHom ⟨t,htN⟩)
  have ha (u : U F) : j (a u) = t*j u*t⁻¹ := by
    change (e (e.symm ((sourceS L H).normalizerMonoidHom ⟨t,htN⟩ (e u)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have ha2 : a^2=1 := by
    apply MulEquiv.ext
    intro u
    apply hj
    change j (a (a u))=j u
    rw [ha,ha]
    have htt : t*t=1 := by
      have hh := pow_orderOf_eq_one t
      rwa [ht2,pow_two] at hh
    calc
      _ = (t*t)*j u*(t*t)⁻¹ := by group
      _ = j u := by rw [htt,one_mul,inv_one,mul_one]
  have hn := d.linear_root_normalizers h hH hp F hm hF he hmax
  have ht₁ : t ∈ normalizer (L.pCoreIn 2 : Set G) := hn.1.symm ▸ h.sylow_normalizes ht
  have ht₂ : t ∈ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hn.2.1.symm ▸ le_normalizer_residual H (hH.1.1.2 ht)
  have hnorm (V : Subgroup (U F))
      (hv : V.map j = L.pCoreIn 2 ∨ V.map j = (residual H).pCoreIn 2) :
      ∀ u ∈ V, a u ∈ V := by
    intro u hu
    apply (mem_map_iff_mem hj).mp
    rw [ha]
    have htn : t ∈ normalizer (V.map j : Set G) := by
      rcases hv with hv | hv
      · rw [hv]; exact ht₁
      · rw [hv]; exact ht₂
    exact (mem_normalizer_iff.mp htn _).mp (mem_map_of_mem j hu)
  have h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F := hnorm _ (hplanes.elim (fun hh=>Or.inl hh.1) (fun hh=>Or.inr hh.1))
  have h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F := hnorm _ (hplanes.elim (fun hh=>Or.inr hh.2) (fun hh=>Or.inl hh.2))
  have hmove : ∃ u ∈ Z F, a u≠u := by
    by_contra hh
    push Not at hh
    apply htS
    have hc : t ∈ centralizer (centerIn (sourceS L H) : Set G) := by
      rw [centerIn_eq_map_center,marked_center F (sourceS L H) e]
      rintro _ ⟨u,hu,rfl⟩
      have hcomm := (ha u).symm.trans (congrArg j (hh u hu))
      exact (mul_inv_eq_iff_eq_mul.mp hcomm).symm
    have htC : t ∈ (T : Subgroup G) ⊓ centralizer (centerIn (sourceS L H) : Set G) := ⟨ht,hc⟩
    rwa [d.linear_sylow_center_centralizer h hH hp F hm hF he hmax] at htC
  obtain ⟨σ,b,hσ,hσσ,hb₁,hb₂,hb⟩ := involution_marked_field_coordinates a h₁ h₂ ha2 hmove
  let e' := b.trans e
  have he' (u : U F) : markedHom F (sourceS L H) e' u=j (b u) := rfl
  have hmap (V : Subgroup (U F)) (hv : ∀ u, b u∈V ↔ u∈V) :
      V.map (markedHom F (sourceS L H) e')=V.map j := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨b u,(hv u).mpr hu,rfl⟩
    · rintro x ⟨u,hu,rfl⟩
      refine ⟨b.symm u,(hv (b.symm u)).mp (by simpa using hu),?_⟩
      rw [he',b.apply_symm_apply]
  refine ⟨e',σ,hσ,hσσ,?_,?_⟩
  · rw [hmap _ hb₁,hmap _ hb₂]
    exact hplanes
  · intro u
    rw [he',he',←ha,hb]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
