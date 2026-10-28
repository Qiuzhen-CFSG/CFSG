module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Coordinates
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Action
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration

/-!
# The alternating-five family and its moving inner actor

Conjugation transports both maximum order and the actual permutation-action
image. A lift of `(0 2)(1 3)` therefore exchanges the two extra members of an
exhaustive four-member family, since their images are the two transposition
lines. This proves that neither extra member is normalized by the Sylow group.

The final theorem constructs the actual permutation coordinates and the
exhaustive family using `Action.actionInput` and `enumerationInput`, then
applies the conjugation calculation. This completes `AlternatingFamilyInput`
with its stated factorization and trivial-Frattini hypotheses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
C.5.6(5), printed pp.157–158, and C.5.7, printed p.160.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily

open Subgroup
universe u
variable {G : Type u} [Group G]

private theorem map_symm_map (e : G ≃* G) (B : Subgroup G) :
    (B.map e.toMonoidHom).map e.symm.toMonoidHom = B := by
  rw [map_map]
  have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
    ext g
    simp
  rw [he, map_id]

private theorem maxFamily_map {T E : Subgroup G} (e : G ≃* G)
    (hT : T.map e.toMonoidHom = T)
    (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups T) :
    E.map e.toMonoidHom ∈ Stellmacher.elementaryAbelianMaxSubgroups T := by
  refine ⟨hT ▸ map_mono hE.1, hE.2.1.map e.toMonoidHom, ?_⟩
  intro Y hY hYe
  have hback : Y.map e.symm.toMonoidHom ≤ T := by
    have hm := map_mono (f := e.symm.toMonoidHom) hY
    have he : T.map e.symm.toMonoidHom = T := by
      calc
        T.map e.symm.toMonoidHom = (T.map e.toMonoidHom).map e.symm.toMonoidHom :=
          congrArg (fun B : Subgroup G => B.map e.symm.toMonoidHom) hT.symm
        _ = T := map_symm_map e T
    rwa [he] at hm
  have hc := hE.2.2 _ hback (hYe.map e.symm.toMonoidHom)
  simpa only [card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective,
    card_map_of_injective (f := e.toMonoidHom) e.injective] using hc

/-- From an exhaustive family with the two distinct transposition images,
the actual inner actor conjugates the extra members and moves both of them.
This supplies the outside-S and nonnormality clauses without an index premise. -/
theorem family_of_enumeration [Finite G] {K : GroupClass.{u}}
    {A H R L : Subgroup G} {x : G}
    (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (hp : Factorization R L x) (c : ActionCoordinates R L)
    {E₀ E₁ : Subgroup G}
    (hfam : Stellmacher.elementaryAbelianMaxSubgroups (S R) =
      {Q R L, opposite R L x, E₀, E₁})
    (h0 : actionImage c.action E₀ = line 0)
    (h1 : actionImage c.action E₁ = line 1) :
    ∃ (E : Subgroup G) (r : G), r ∈ R ⊓ L ∧ r ∉ S R ∧
      E ≠ E.map (MulAut.conj r).toMonoidHom ∧
      Stellmacher.elementaryAbelianMaxSubgroups (S R) =
        {Q R L, opposite R L x, E, E.map (MulAut.conj r).toMonoidHom} ∧
      ¬ R ≤ normalizer (E : Set G) ∧
      ¬ R ≤ normalizer (E.map (MulAut.conj r).toMonoidHom : Set G) := by
  have hm0 : E₀ ∈ Stellmacher.elementaryAbelianMaxSubgroups (S R) := by
    rw [hfam]
    simp
  have hm1 : E₁ ∈ Stellmacher.elementaryAbelianMaxSubgroups (S R) := by
    rw [hfam]
    simp
  have h0R : E₀ ≤ R := hm0.1.trans inf_le_left
  have h1R : E₁ ≤ R := hm1.1.trans inf_le_left
  obtain ⟨r, hrL, hrS, hr⟩ := c.exists_exchange
  have hS : (S R).map (MulAut.conj (r : G)).toMonoidHom = S R :=
    mem_normalizer_iff_map_conj_eq.mp (h.normalizes_S (h.le_A r.property))
  have hmove := moved_of_line_zero c.action h0R h0 r hr
  have hswap : E₀.map (MulAut.conj (r : G)).toMonoidHom = E₁ := by
    have hm := maxFamily_map (MulAut.conj (r : G)) hS hm0
    have hi : actionImage c.action (E₀.map (MulAut.conj (r : G)).toMonoidHom) = line 1 := by
      rw [actionImage_conj c.action h0R r, h0, hr, exchange_line_zero]
    rw [hfam] at hm
    rcases Set.mem_insert_iff.mp hm with he | hm
    · rw [he, c.core_image hb] at hi
      exact False.elim (line_ne_bot 1 hi.symm)
    rcases Set.mem_insert_iff.mp hm with he | hm
    · rw [he, c.opposite_image hb hp] at hi
      exact False.elim (line_ne_actor 1 hi.symm)
    rcases Set.mem_insert_iff.mp hm with he | hm
    · exact False.elim (hmove he.symm)
    · exact Set.mem_singleton_iff.mp hm
  have hn0 : ¬ R ≤ normalizer (E₀ : Set G) := by
    intro hn
    exact hmove (mem_normalizer_iff_map_conj_eq.mp (hn r.property)).symm
  have hn1 : ¬ R ≤ normalizer (E₁ : Set G) := by
    intro hn
    exact moved_of_line_one c.action h1R h1 r hr
      (mem_normalizer_iff_map_conj_eq.mp (hn r.property)).symm
  refine ⟨E₀, r, ⟨r.property, hrL⟩, hrS, hmove, ?_, hn0, ?_⟩
  · simpa only [hswap] using hfam
  · simpa only [hswap] using hn1

/-- Conditional assembly of the exact alternating-family contract. The action
and exhaustive enumeration inputs are discharged in `alternatingFamilyInput`. -/
theorem alternatingFamilyInput_of_action_and_enumeration [Finite G]
    (K : GroupClass.{u}) (ha : ActionInput (G := G) K)
    (he : EnumerationInput (G := G) K) : AlternatingFamilyInput (G := G) K := by
  intro A H R L h hb hL x hx hnc hp hf
  obtain ⟨c⟩ := ha A H R L h hb hL x hx hnc hp hf
  obtain ⟨E₀, E₁, hfamily, h0, h1⟩ := he A H R L h hb hL x hx hnc hp hf c
  exact family_of_enumeration h hb hp c hfamily h0 h1

/-- The full four-member maximum elementary family for the genuine
alternating-five module, with an element of `R ∩ L` outside `S` exchanging
the two extra members. Neither extra member is normalized by `R`.
The factorization and `F = ⊥` remain exactly the published contract's premises. -/
theorem alternatingFamilyInput [Finite G] (K : GroupClass.{u}) :
    AlternatingFamilyInput (G := G) K :=
  alternatingFamilyInput_of_action_and_enumeration K
    (Action.actionInput K) (enumerationInput K)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
end
