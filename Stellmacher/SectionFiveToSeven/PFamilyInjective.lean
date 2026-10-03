module
public import Stellmacher.SectionFiveToSeven.PFamilyBridge

/-!
# Native local-family data under injective homomorphisms

An injective homomorphism from a finite group transports its given Sylow
two-subgroup, nontrivial proper two-core, and unique maximal overgroup to
membership of its range in the Section Five local family over that Sylow
image. The ambient target group need not be finite.

The equivalence between the native group and the homomorphism range carries
the Sylow and two-core data. For unique maximal containment, compose it
with the top-subgroup equivalence and transport coatoms in the subgroup
lattice. Injectivity reflects the required containment conditions and both
nontriviality assertions. The existing `PFamily`/`PSet` bridge then assembles
the original local-family predicate without replacing the supplied Sylow.

This is the injective local-group transport used for the selected factor
in Stellmacher (6.1), Journal of Algebra 190 (1997), p.30,
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionsFiveToSeven

private theorem uniqueMaximalContaining_range_of_injective
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (T : Subgroup G)
    (h : IsUniqueMaximalContaining T (⊤ : Subgroup G)) :
    IsUniqueMaximalContaining (T.map f) f.range := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let e0 : (⊤ : Subgroup G) ≃* f.range := Subgroup.topEquiv.trans e
  have hmap (N : Subgroup (⊤ : Subgroup G)) :
      (N.map e0.toMonoidHom).map f.range.subtype =
        (N.map (⊤ : Subgroup G).subtype).map f := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  obtain ⟨M, hM, hTM, hunique⟩ := h
  refine ⟨M.map e0.toMonoidHom,
    (OrderIso.isCoatom_iff e0.mapSubgroup M).mpr hM, ?_, ?_⟩
  · rw [hmap]
    exact Subgroup.map_mono hTM
  · intro N hN hTN
    let M' := N.map e0.symm.toMonoidHom
    have hM' : IsCoatom M' := (OrderIso.isCoatom_iff e0.symm.mapSubgroup N).mpr hN
    have hforward : M'.map e0.toMonoidHom = N := by
      change (N.map e0.symm.toMonoidHom).map e0.toMonoidHom = N
      rw [Subgroup.map_map]
      have he : e0.toMonoidHom.comp e0.symm.toMonoidHom = MonoidHom.id f.range := by
        ext x
        simp
      rw [he, Subgroup.map_id]
    have hTM' : T ≤ M'.map (⊤ : Subgroup G).subtype := by
      apply (Subgroup.map_le_map_iff_of_injective hf).mp
      rw [← hmap, hforward]
      exact hTN
    have hEq : M' = M := hunique M' hM' hTM'
    rw [← hforward, hEq]

/-- Native local-family data gives the range local-family membership under
an injection, preserving the supplied Sylow subgroup's ambient image. -/
public theorem pFamily_range_of_injective
    {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (T : Sylow 2 G)
    (B : Subgroup H) (hT : (T : Subgroup G).map f = B)
    (hcore : pCore 2 G ≠ ⊥) (hnot : (T : Subgroup G) ≠ pCore 2 G)
    (hunique : IsUniqueMaximalContaining (T : Subgroup G) (⊤ : Subgroup G)) :
    f.range ∈ PFamily (⊤ : Subgroup H) B := by
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  let U : Sylow 2 f.range := T.mapSurjective e.surjective
  have hU : (U : Subgroup f.range).map f.range.subtype = B := by
    change ((T : Subgroup G).map e.toMonoidHom).map f.range.subtype = B
    rw [Subgroup.map_map]
    exact hT
  have hcoremap : twoCoreAmbient f.range = (pCore 2 G).map f := by
    change (pCore 2 f.range).map f.range.subtype = (pCore 2 G).map f
    rw [← pCore_map_iso 2 e, Subgroup.map_map]
    rfl
  rw [pFamily_iff_pSet]
  refine ⟨⟨le_top, ⟨U, hU⟩, ?_, ?_⟩, ?_⟩
  · rw [hcoremap]
    exact fun hb => hcore ((Subgroup.map_eq_bot_iff_of_injective _ hf).mp hb)
  · rw [hcoremap, ← hT]
    exact fun he => hnot (Subgroup.map_injective hf he)
  · rw [← hT]
    exact uniqueMaximalContaining_range_of_injective f hf (T : Subgroup G) hunique

end Stellmacher.SectionsFiveToSeven
