module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Comparison
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Normalization
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.LocalComputation
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation

/-!
# The terminal Thompson obstruction in §16.3

The compatible 16.3.11 marking and the dihedral/semidihedral shape of T_C
construct the permitted conjugate and its local Sylow group P. The actual
isomorphism P ≃ C₂ × (D₈ wreath C₂) supplies rank five and a noncentral action
on the four-group Ω₁(Φ(J(P))). The ambient calculation proves both cases of
16.3.12 and centrality of Ω₁(Φ(J(T))), with the local rank premise discharged.

Equal maximum elementary ranks embed J(P) into the Thompson subgroup of a
conjugate of T containing P itself. First-omega Frattini monotonicity produces
an ambient Sylow subgroup centralizing Ω₁(Φ(J(P))). Since P normalizes this
subgroup, the Sylow normalizer/centralizer obstruction contradicts its computed
noncentral action. `terminal_counterexample_false` has only the earlier
counterexample, centralizer shape, and marked enlargement as inputs. Producing
those earlier outputs and deducing standardness belong to the section assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1181–1182 / PDF pp.1198–1199. In the last paragraph on p.1182 the abbreviated
Frattini equalities must be replaced by first-omega inclusions; the whole
Frattini subgroup of the variable dihedral factor can have order greater than two.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction

open Subgroup ChapterB AmbientComputation

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Lemma 16.3.12 and its central Frattini-omega consequence, with the local
rank computed from the constructed model. `Decomposition` contains the
characteristic rotation, maximizing candidate, both action alternatives, and
the compatible internal product for the actual elementary Thompson subgroup. -/
theorem lemma_16_3_12 (d : Prepared T z t L) :
    ∃ c : Decomposition d,
      (∀ (a : c.R) (b : componentSylow T L) (e : zpowers c.w),
        (c.product (a, b, e) : G) = (a : G) * (b : G) * (e : G)) ∧
      twoRank (T : Subgroup G) = 5 ∧
      Nonempty (componentSylow T L ≃* DihedralGroup 4) ∧
      ∃ v : G, orderOf v = 2 ∧
        ambientCenter (componentSylow T L) = zpowers v ∧
        thompsonFrattiniOmega (T : Subgroup G) = zpowers z ⊔ zpowers v ∧
        thompsonFrattiniOmega (T : Subgroup G) ≤ ambientCenter (T : Subgroup G) ∧
        (T : Subgroup G) ≤
          centralizer (thompsonFrattiniOmega (T : Subgroup G) : Set G) := by
  have hP := (LocalComputation.local_calculation (localSylow d.P) d.model).1
  obtain ⟨c, v, hproduct, hT, _, _, _, hv, hvC, hOmega, hZ, hC⟩ :=
    exists_ambient_calculation d hP
  exact ⟨c, hproduct, hT, (rankGeometry_of_prepared d hP).component_dihedral,
    v, hv, hvC, hOmega, hZ, hC⟩

/-- The terminal Thompson contradiction after normalization. The ranks,
ambient centrality, and local noncentrality are all calculated here; none
is a premise of this result. The comparison constructs the maximal-rank
Thompson embedding and the centralizing ambient Sylow subgroup. -/
theorem impossible_prepared (d : Prepared T z t L) : False := by
  obtain ⟨hP, _, hnoncentral⟩ := LocalComputation.local_calculation (localSylow d.P) d.model
  obtain ⟨_, _, hT, _, _, _, _, _, _, hcentral⟩ := lemma_16_3_12 d
  exact impossible_noncentral_thompsonFrattiniOmega T (localSylow d.P)
    (localSylow_isPGroup d) (hP.trans hT.symm) hcentral hnoncentral

/-- The final contradiction of Theorem 16.3.7 from the genuine earlier
outputs. Normalization selects the permitted conjugate of t and constructs
every `Prepared` field before the Thompson calculations are applied. -/
theorem terminal_counterexample_false (h : TerminalCounterexample T z L t)
    (shape : NonterminalCentralizerShape T z L t)
    (d : MarkedEnlargement z t L) : False := by
  obtain ⟨_, _, ⟨prepared⟩⟩ := exists_prepared h shape d
  exact impossible_prepared prepared

end CFSG.Quasithin.Chapter16.ThompsonObstruction
