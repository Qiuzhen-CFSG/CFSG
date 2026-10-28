module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.LargeFamily
public import CFSG.Quasithin.ChapterE.Section01.Inheritance

/-!
# Transport of the prime-square local escape calculation

Isomorphisms carry the family and its weak closure to the literal image
family. The E-member transport preserves the intrinsic quotients, local tau
and Sylow intersection. Sylow conjugacy then lets each concrete calculation
choose convenient coordinates for one Sylow subgroup.

This is used by `SquareGeometry` to transfer from the faithful semilinear
image back to the original group. It supplies no local E-member by itself.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--E.1.5 and E.1.14(6), printed pp.209--210 and 214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry
open Subgroup
variable {G J : Type*} [Group G] [Finite G] [Group J] [Finite J]

/-- Transport the literal family, normalizer, and escaping E-member. -/
theorem largeFamilyEscapeAt_map_equiv {T : Sylow 2 G}
    (h : LargeFamilyEscapeAt T) (e : G ≃* J) :
    LargeFamilyEscapeAt (T.mapSurjective (f := e.toMonoidHom) e.surjective) := by
  intro Ω hΩ hlarge M hTM hM hNM
  have hTM' : (T : Subgroup G) ≤ M.comap e.toMonoidHom :=
    map_le_iff_le_comap.mp hTM
  have hM' : M.comap e.toMonoidHom ≠ ⊤ := by
    intro heq
    apply hM
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    exact (show x ∈ M.comap e.toMonoidHom by rw [heq]; trivial)
  have hNM' : normalizer (weakClosure (T : Subgroup G)
      {A | A.map e.toMonoidHom ∈ Ω} : Set G) ≤ M.comap e.toMonoidHom := by
    apply map_le_iff_le_comap.mp
    rw [map_normalizer_eq_of_bijective _ e.bijective, map_weakClosure_equiv]
    exact hNM
  have hlarge' : ∀ A ∈ {A : Subgroup G | A.map e.toMonoidHom ∈ Ω},
      A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A := by
    intro A hA hAT hne
    have hne' : A.map e.toMonoidHom ≠ ⊥ := by
      intro heq
      apply hne
      apply map_injective (f := e.toMonoidHom) e.injective
      simpa using heq
    have hr := hlarge (A.map e.toMonoidHom) hA (map_mono hAT) hne'
    rwa [← Group.rank_congr (A.equivMapOfInjective e.toMonoidHom e.injective)] at hr
  obtain ⟨A, hA, hAT, H, hH, hHM⟩ :=
    h _ (hΩ.comap_equiv e) hlarge' _ hTM' hM' hNM'
  exact ⟨A.map e.toMonoidHom, hA, map_mono hAT, H.map e.toMonoidHom,
    hH.map_equiv e, fun hm => hHM (map_le_iff_le_comap.mp hm)⟩

/-- One Sylow subgroup suffices, by conjugation of the entire local witness. -/
theorem largeFamilyEscapeAt_of_sylow {T : Sylow 2 G}
    (h : LargeFamilyEscapeAt T) (U : Sylow 2 G) : LargeFamilyEscapeAt U := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T U
  have he : T.mapSurjective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).surjective = g • T := by
    apply Sylow.ext
    rfl
  rw [← hg, ← he]
  exact largeFamilyEscapeAt_map_equiv h (MulAut.conj g)

/-- Transfer a calculation on an actual model to an isomorphic ambient group. -/
theorem largeFamilyEscape_of_equiv (e : G ≃* J)
    (h : ∀ T : Sylow 2 G, LargeFamilyEscapeAt T) :
    ∀ T : Sylow 2 J, LargeFamilyEscapeAt T := by
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 G))
  exact largeFamilyEscapeAt_of_sylow (largeFamilyEscapeAt_map_equiv (h T) e)
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry
