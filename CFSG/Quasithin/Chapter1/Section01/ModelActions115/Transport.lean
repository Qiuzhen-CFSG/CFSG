module
public import CFSG.Quasithin.Chapter1.Section01.ModelActions115
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-! Transport the six actual 1.1.5 model-action alternatives along a literal
component equivalence. Central and two-core quotients use their canonical
quotient maps; alternating actions retain the same marked permutation.
Source: Aschbacher--Smith 1.1.5(3), used in original Chapter 2 components. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels Chapter1.Section02.LocalModels
variable {L K : Type*} [Group L] [Group K]
private theorem map_center (e : K ≃* L) : (center K).map e.toMonoidHom = center L := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (centerCongr e ⟨x,hx⟩).property
  · intro x hx
    exact ⟨e.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,e.apply_symm_apply x⟩

private theorem rankTwo_congr (h : RankTwoTheoremC L) (e : K ≃* L) : RankTwoTheoremC K := by
  cases h with
  | linear f hf hm => exact .linear f hf (hm.of_mulEquiv e)
  | symplectic f hf hm => exact .symplectic f hf (hm.of_mulEquiv e)
  | g2 f hf hm => exact .g2 f hf (hm.of_mulEquiv e)
  | triality f hf hm => exact .triality f hf (hm.of_mulEquiv e)
  | ree m hm hm' =>
    obtain ⟨d,⟨f⟩⟩ := hm'
    exact .ree m hm ⟨d,⟨e.trans f⟩⟩
  | symplectic_derived hm => exact .symplectic_derived (hm.map (e.trans ·))
  | g2_derived hm => exact .g2_derived (hm.map (e.trans ·))
  | tits hm => exact .tits (hm.map (e.trans ·))

private theorem alternating_congr {α : MulAut L} {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : AlternatingAction α n σ) (e : K ≃* L) :
    AlternatingAction (MulAut.congr e.symm α) n σ := by
  rcases h with ⟨f,hf⟩ | ⟨hq,hz,f,hf⟩
  · refine .inl ⟨e.trans f,fun x => ?_⟩
    simpa only [MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply, e.apply_symm_apply] using hf (e x)
  · let := hq
    let q := QuotientGroup.congr _ _ e (map_center e)
    refine .inr ⟨IsQuasisimple.of_mulEquiv e.symm,
      hz.map ((centerCongr e).trans ·),q.trans f,fun x => ?_⟩
    change (f (QuotientGroup.mk' (center L) (e (e.symm (α (e x))))) : Equiv.Perm (Fin n)) = _
    change (f (QuotientGroup.mk' (center L) (e (e.symm (α (e x))))) : Equiv.Perm (Fin n)) = σ * f (QuotientGroup.mk' (center L) (e x)) * σ⁻¹
    simpa only [e.apply_symm_apply] using hf (e x)

variable [Finite L]

theorem ModelAction115.of_mulEquiv {α : MulAut L} (h : ModelAction115 L α)
    (e : K ≃* L) : ModelAction115 K (MulAut.congr e.symm α) := by
  have hi (h : α ∈ (MulAut.conj (G := L)).range) :
      MulAut.congr e.symm α ∈ (MulAut.conj (G := K)).range := by
    obtain ⟨t,rfl⟩ := h
    exact ⟨e.symm t, by ext x; simp⟩
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  cases h with
  | lie hs hm hin =>
    apply ModelAction115.lie ((MulEquiv.isSimpleGroup_congr e).mpr hs) _ (hi hin)
    rcases hm with hm | hm | ⟨n,hn,hm⟩
    · exact .inl (hm.of_mulEquiv e)
    · exact .inr (.inl (rankTwo_congr hm e))
    · exact .inr (.inr ⟨n,hn,hm.of_mulEquiv e⟩)
  | two_cover hn hc hm hin =>
    have hck : center K = pCore 2 K := by
      apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_center, pCore_map_iso,hc]
    have hkn : center K ≠ ⊥ := by
      intro hh
      apply hn
      rw [← map_center e,hh,Subgroup.map_bot]
    apply ModelAction115.two_cover hkn hck _ (hi hin)
    exact hm.elim (fun h => .inl (h.of_mulEquiv q)) (fun h => .inr (h.of_mulEquiv q))
  | six σ hσ ha => exact .six σ hσ (alternating_congr ha e)
  | seven σ hσ ha => exact .seven σ hσ (alternating_congr ha e)
  | odd hm hin =>
    apply ModelAction115.odd _ (hi hin)
    exact hm.elim (fun h => .inl (h.of_mulEquiv e))
      (fun ⟨p,hp,hm⟩ => .inr ⟨p,hp,hm.of_mulEquiv e⟩)
  | sporadic n hn hm ha =>
    refine .sporadic n hn (hm.map (q.trans ·)) ⟨hi ha.1,?_,?_⟩
    · exact (orderOf_injective (MulAut.congr e.symm).toMonoidHom (MulAut.congr e.symm).injective α).trans ha.2.1
    · obtain ⟨P,hP⟩ := ha.2.2
      refine ⟨P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective,?_⟩
      rintro ⟨x,⟨y,hy,rfl⟩⟩
      change e.symm (α (e (e.symm y))) = e.symm y
      rw [e.apply_symm_apply,hP ⟨y,hy⟩]
end CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
