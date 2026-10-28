module
public import Theory.Representation.SmallDisplacementParabolics.Models
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner

/-!
# Transport and residual movement for marked parabolics

A subgroup containing a Sylow that fixes a vector moves that vector if and
only if its embedded two-residual does: the residual and Sylow generate the
subgroup. A prime relative index gives the required absence of intermediate
subgroups. Finally actual actor and module equivalences transport all three
clauses of the moving-parabolic contract, including its literal residual map.

Source application: Aschbacher--Smith, original 15.2.27(2), printed p.1119.
These are general transport tools; model existence is proved separately.
-/

public section
open Subgroup Representation
namespace Representation.SmallDisplacementParabolics
variable {D E W V : Type*} [Group D] [Finite D] [Group E]
  [AddCommGroup W] [Module (ZMod 2) W] [AddCommGroup V] [Module (ZMod 2) V]

/-- Movement by an overgroup of a vector-fixing Sylow is already movement by its residual. -/
theorem residual_moves_of_moves (ρ : Representation (ZMod 2) D W)
    (S : Sylow 2 D) (w : W) (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
    (hfix : ∀ g ∈ (S : Subgroup D), ρ g w = w)
    (hmove : ∃ g ∈ P, ρ g w ≠ w) :
    ∃ g ∈ (pResidual 2 P).map P.subtype, ρ g w ≠ w := by
  classical
  by_contra hn
  push Not at hn
  let C := BinaryNaturalDual.VectorStabilizers.representationStabilizer ρ w
  have hr : (pResidual 2 P).map P.subtype ≤ C := hn
  have hs : (S : Subgroup D) ≤ C := hfix
  have he := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (S.subtype hSP))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hSP] at he
  obtain ⟨g,hg,hm⟩ := hmove
  exact hm ((he ▸ sup_le hr hs) hg)

omit [Finite D] in
/-- Prime relative index rules out intermediate overgroups of the marked Sylow. -/
theorem proper_normalizes_of_prime_index (S : Sylow 2 D) (P : Subgroup D)
    (_hSP : (S : Subgroup D) ≤ P) (hi : ((S : Subgroup D).relIndex P).Prime) :
    ∀ Y : Subgroup D, (S : Subgroup D) ≤ Y → Y < P →
      Y ≤ normalizer (S : Set D) := by
  intro Y hSY hYP
  have he := relIndex_mul_relIndex (S : Subgroup D) Y P hSY hYP.le
  have hp : ((S : Subgroup D).relIndex Y * Y.relIndex P).Prime := he.symm ▸ hi
  rcases Nat.prime_mul_iff.mp hp with ⟨_, hYP1⟩ | ⟨_, hSY1⟩
  · exact (hYP.not_ge (relIndex_eq_one.mp hYP1)).elim
  · exact (relIndex_eq_one.mp hSY1).trans (S : Subgroup D).le_normalizer

/-- Transport of the complete output contract along an actual actor and module marking. -/
noncomputable def MovingParabolic.comap
    (ρ : Representation (ZMod 2) D W) (σ : Representation (ZMod 2) E V)
    (e : D ≃* E) (f : W ≃ₗ[ZMod 2] V)
    (hf : ∀ g v, f (ρ g v) = σ (e g) (f v))
    (S : Sylow 2 D) (w : W)
    (d : MovingParabolic σ (S.mapSurjective (f := e.toMonoidHom) e.surjective) (f w)) :
    MovingParabolic ρ S w := by
  let P := d.subgroup.comap e.toMonoidHom
  have hP : P.map e.toMonoidHom = d.subgroup := map_comap_eq_self_of_surjective e.surjective _
  refine ⟨P, ?_, ?_, ?_⟩
  · intro g hg
    exact d.sylow_le (mem_map_of_mem e.toMonoidHom hg)
  · intro Y hSY hYP
    have hSY' : ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 E) : Subgroup E) ≤
        Y.map e.toMonoidHom := map_mono hSY
    have hlt : Y.map e.toMonoidHom < d.subgroup := by
      apply lt_of_le_not_ge (hP ▸ map_mono hYP.le)
      intro hn
      apply hYP.not_ge
      intro g hg
      obtain ⟨a,ha,hea⟩ := hn hg
      exact e.injective hea ▸ ha
    have hn := map_le_iff_le_comap.mp (d.proper _ hSY' hlt)
    have hn' := ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 E) : Subgroup E).le_normalizer_comap e.toMonoidHom
    have hS : (((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 E) : Subgroup E)).comap e.toMonoidHom = S := by
      ext g
      exact mem_map_iff_mem e.injective
    rw [hS] at hn'
    exact hn.trans hn'
  · obtain ⟨g,hg,hm⟩ := d.moves
    have he := map_embedded_pResidual 2 P e.toMonoidHom
    rw [hP] at he
    obtain ⟨a,ha,rfl⟩ := he.symm ▸ hg
    refine ⟨a,ha,fun hh => hm ?_⟩
    exact (hf a w).symm.trans (congrArg f hh)

end Representation.SmallDisplacementParabolics
