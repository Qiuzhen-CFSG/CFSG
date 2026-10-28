module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateDefs
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.MaximalAction

/-!
# The ordinary centralizer alternative in 6.1.13

If C_M(U) = C_M(B) and r(G,B) > 1, an escaping C_G(U) would enlarge U
to a maximal obstruction. The proved E.6.11 moving-element theorem then
forces a hyperplane obstruction and r(G,B) = 1, a contradiction. This
proves the E.6.12 implication used in 6.1.13 without a structural callback.

Under C_G(Z_S) ≤ M, the TI property also forces every centralizer of an
L-conjugate of Z_S to normalize B. Transport by the original conjugator
g proves the literal line alternative needed with B^g in the role of B.
Neither argument assumes the escape disjunction of 6.1.12(1).

Source: Aschbacher--Smith, E.6.12, printed p.250, and 6.1.13--15,
printed pp.670--672.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V U : Subgroup G} {n : ℕ}

/-- The genuine E.6.12 implication used in the first case of 6.1.13. -/
theorem centralizer_le_normalizer_of_local_equality
    {B : Subgroup G}
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M B)
    (hr : 1 < ChapterE.globalR B) (hU : U ≠ ⊥) (hUB : U ≤ B)
    (hC : M ⊓ centralizer (U : Set G) = M ⊓ centralizer (B : Set G)) :
    centralizer (U : Set G) ≤ normalizer (B : Set G) := by
  apply (hE.centralizer_le_iff hU hUB).mp
  by_contra he
  obtain ⟨W, _, _, _, _, hrone⟩ := hE.hyperplane_escape_of_maximal_action
    (fun W hW hmax hn =>
      ChapterE.Section06.maximal_escape_action_knownSimple hE hW hmax hn) hU hUB hC he
  rw [hrone] at hr
  exact (lt_irrefl _ hr)

/-- Specialize the ordinary alternative to the actual Chapter 6 layer.
Only the earlier-source lower bound on r is retained. -/
theorem source_ordinary_fixed_space_centralizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hr : (n : ℕ∞) ≤ ChapterE.globalR (layer L V))
    (hU : U ≠ ⊥) (hUB : U ≤ layer L V)
    (hC : M ⊓ centralizer (U : Set G) =
      M ⊓ centralizer (layer L V : Set G)) :
    centralizer (U : Set G) ≤ normalizer (layer L V : Set G) := by
  apply centralizer_le_normalizer_of_local_equality hE _ hU hUB hC
  exact lt_of_lt_of_le (by exact_mod_cast h.n_gt_one) hr

omit [Finite G] in
private theorem centralizer_map_equiv (B : Subgroup G) (e : G ≃* G) :
    (centralizer (B : Set G)).map e.toMonoidHom =
      centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The line case of 6.1.13 after conjugating the entire configuration.
With left conjugation, an L^g-conjugate of Z_S^g is (Z_S^l)^g for l ∈ L.
The same g occurs in the target normalizer. -/
theorem conjugate_line_centralizer_le_normalizer
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hnatural : IsNaturalModule L (layer L V) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L V))
    (hI : centralizer (ZS (T : Subgroup G) L V : Set G) ≤ M)
    (g l : G) (hl : l ∈ L) :
    centralizer (((ZS (T : Subgroup G) L V).map
      (MulAut.conj l).toMonoidHom).map (MulAut.conj g).toMonoidHom : Set G) ≤
      normalizer ((layer L V).map (MulAut.conj g).toMonoidHom : Set G) := by
  have hc : centralizer (ZS (T : Subgroup G) L V : Set G) ≤
      normalizer (layer L V : Set G) :=
    (hE.centralizer_le_iff h.ZS_ne_bot inf_le_left).mp hI
  obtain ⟨F, _, _, _, _, hmodel⟩ := hnatural
  have he : (layer L V).map (MulAut.conj l).toMonoidHom = layer L V :=
    mem_normalizer_iff_map_conj_eq.mp (hmodel.normalizes hl)
  have hc' := map_mono (f := (MulAut.conj g).toMonoidHom)
    (map_mono (f := (MulAut.conj l).toMonoidHom) hc)
  simpa only [centralizer_map_equiv, map_equiv_normalizer_eq, he] using hc'

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
