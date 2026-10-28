module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Commutator

/-!
# C.5.6(1)–(4) for the actual rank-one or A₃ block

The original right conjugator supplies both symmetric Baumann spans. Their
commutators coincide and conjugation preserves that common subgroup. Together
with the core factorization and central elementary Frattini calculation this
assembles the four source conclusions. Every natural-cover and pair-generation
input is proved; the only input is the preceding C.5.3–4 marked setup.

Source: Aschbacher–Smith, C.5.6(1)–(4), printed pp.156–157.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
private theorem map_centralizer (U : Subgroup G) (e : G ≃* G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro g hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    intro u hu
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hg (e u) (mem_map_of_mem _ hu)

omit [Finite G] in
private theorem inverse_conjugate_map (B : Subgroup G) (x : G) :
    (B.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = B := by
  rw [map_map]
  have he : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id G := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

omit [Finite G] in
theorem Setup.conjugate_core (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G)) :
    (Q R L).map (MulAut.conj x⁻¹).toMonoidHom =
      S R ⊓ centralizer ((U L).map (MulAut.conj x⁻¹).toMonoidHom : Set G) := by
  rw [h.core, map_inf _ _ _ (MulAut.conj x⁻¹).injective, h.stable hx, map_centralizer]

theorem Setup.second_span (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    S R = U L ⊔ (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  have hi := inverse_not_centralizing (U L) x⁻¹ hnc
  simp only [inv_inv] at hi
  have hs := (h.factorization ((normalizer (R : Set G)).inv_mem hx)
    (by simpa only [inv_inv] using hi)).span
  simp only [inv_inv] at hs
  have hm := congrArg (map (MulAut.conj x⁻¹).toMonoidHom) hs
  rwa [h.stable hx, Subgroup.map_sup, inverse_conjugate_map] at hm

theorem Setup.core_span (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    S R = Q R L ⊔ (Q R L).map (MulAut.conj x⁻¹).toMonoidHom := by
  apply le_antisymm
  · exact (h.factorization hx hnc).span.le.trans
      (sup_le ((map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) h.module_le_core).trans
        le_sup_right) le_sup_left)
  · exact sup_le (h.core ▸ inf_le_left) ((h.conjugate_core hx).le.trans inf_le_left)

theorem Setup.commutator_structure (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
    let E := ⁅U L, S R⁆
    E = ⁅U L, V⁆ ∧ E = U L ⊓ centralizer (V : Set G) ∧ E = U L ⊓ V ∧
      E.map (MulAut.conj x⁻¹).toMonoidHom = E := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let Q' := (Q R L).map (MulAut.conj x⁻¹).toMonoidHom
  have hcomm : ⁅U L, S R⁆ = ⁅U L, V⁆ :=
    (commutator_eq_of_centralizing_sup
      ((sup_comm (Q R L) V).trans (h.factorization hx hnc).span.symm)
      (h.core ▸ inf_le_right) ((h.conjugate_le hx).trans h.coordinates.normalizes)).symm
  have hcomm' : ⁅V, S R⁆ = ⁅V, U L⁆ :=
    (commutator_eq_of_centralizing_sup
      ((sup_comm Q' (U L)).trans (h.second_span hx hnc).symm)
      ((h.conjugate_core hx).le.trans inf_le_right)
      (h.module_le.trans (h.conjugate_normalized hx))).symm
  have he := h.commutator_eq_fixed hx hnc
  refine ⟨hcomm, hcomm.trans he.1, hcomm.trans he.2, ?_⟩
  rw [map_commutator, h.stable hx]
  exact hcomm'.trans ((commutator_comm V (U L)).trans hcomm.symm)

/-- The four literal rank-one/A₃ conclusions of C.5.6 for the original x.
All cover facts, indices, generation, intersections and Frattini invariance
are proved from the preceding marked source data. -/
theorem Setup.source_conclusions (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
    let E := ⁅U L, S R⁆
    Q R L = U L ⊔ D R L ∧ D R L ≤ centralizer (V : Set G) ∧
    S R = V ⊔ Q R L ∧ S R = Q R L ⊔ (Q R L).map (MulAut.conj x⁻¹).toMonoidHom ∧
    E = ⁅U L, V⁆ ∧ E = U L ⊓ centralizer (V : Set G) ∧ E = U L ⊓ V ∧
    E.map (MulAut.conj x⁻¹).toMonoidHom = E ∧
    ((frattini (D R L)).map (D R L).subtype).map (MulAut.conj x⁻¹).toMonoidHom =
      (frattini (D R L)).map (D R L).subtype := by
  have hf := h.factorization hx hnc
  have hc := h.commutator_structure hx hnc
  exact ⟨hf.core, hf.centralizes, hf.span, h.core_span hx hnc,
    hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, h.frattini_invariant hx hnc⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
