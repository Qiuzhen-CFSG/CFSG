module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.AutomorphismCartan

/-!
# Common coordinates for the source field subgroup

In GLS III, Definition 2.5.13, a field automorphism is a conjugate in the full
automorphism group of a coefficient automorphism. Different elements may
initially come with different conjugating maps. For a cyclic subgroup, choose
a generator and its conjugating map: its powers then all act coefficientwise
in the same model coordinates. Inner conjugations and preservation of a
subgroup transport along this same change of coordinates.

These facts supply the field realization in the raw A.3.15(5) argument;
no universal inner–field decomposition of the automorphism group is used.

Source: GLS III, §§2.5.10–2.5.13; Aschbacher–Smith, combined 1 March 2004
manuscript, A.3.15(5), printed pp.50–51, and its use on p.511.
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.LieAutomorphismExtensions
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source.RawCartan
variable {K E : Type*} [Group K] [Field E]

/-- The source's field convention allows conjugation in the full automorphism group. -/
def IsField (e : K ≃* Model E) (f : MulAut K) : Prop :=
  ∃ (c : MulAut (Model E)) (σ : E ≃+* E),
    MulAut.congr e f = c * fieldAction σ * c⁻¹

/-- A generator's field coordinates work simultaneously for a cyclic field subgroup. -/
theorem common_field_coordinates (e : K ≃* Model E) (F : Subgroup (MulAut K))
    (hcyc : IsCyclic F) (hfield : ∀ f ∈ F, IsField e f) :
    ∃ e' : K ≃* Model E,
      F.map (MulAut.congr e').toMonoidHom ≤ (fieldAction (F := E)).range := by
  obtain ⟨g, hg⟩ := F.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  obtain ⟨c, σ, hσ⟩ := hfield g (hg ▸ mem_zpowers g)
  refine ⟨e.trans c.symm, ?_⟩
  rw [← hg, MonoidHom.map_zpowers]
  apply zpowers_le.mpr
  refine ⟨σ, ?_⟩
  apply MulEquiv.ext
  intro x
  have h := congrArg c.symm (MulEquiv.congr_fun hσ (c x))
  simpa [MulAut.congr, MulEquiv.trans_apply] using h.symm

/-- Changing coordinates preserves actual inner conjugation. -/
theorem congr_conj (e : K ≃* Model E) (x : K) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr, MulAut.conj_apply]

/-- Inner containment can be transferred to the common field coordinates. -/
theorem inner_in_any_coordinates (e e' : K ≃* Model E) (H : Subgroup (MulAut K))
    (hH : H.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : Model E →* MulAut (Model E)).range) :
    H.map (MulAut.congr e').toMonoidHom ≤
      (MulAut.conj : Model E →* MulAut (Model E)).range := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨d, hd⟩ := hH (mem_map_of_mem (MulAut.congr e).toMonoidHom hh)
  have he : h = MulAut.conj (e.symm d) := by
    apply (MulAut.congr e).injective
    rw [congr_conj, e.apply_symm_apply]
    exact hd.symm
  change MulAut.congr e' h ∈ _
  rw [he, congr_conj]
  exact ⟨_, rfl⟩

/-- Transport an automorphism's preservation of the actual Sylow intersection. -/
theorem map_preserved (e : K ≃* Model E) (U : Subgroup K) (h : MulAut K)
    (hh : U.map h.toMonoidHom = U) :
    (U.map e.toMonoidHom).map (MulAut.congr e h).toMonoidHom = U.map e.toMonoidHom := by
  have he : (MulAut.congr e h).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp h.toMonoidHom := by
    ext x
    simp [MulAut.congr]
  rw [map_map, he, ← map_map, hh]
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.G2.Source.RawCartan
