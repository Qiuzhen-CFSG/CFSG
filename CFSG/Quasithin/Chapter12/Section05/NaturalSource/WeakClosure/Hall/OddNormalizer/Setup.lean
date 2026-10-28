module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.Inputs
public import CFSG.Quasithin.Chapter4.Section04.OddActorResidual
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorNormalizer.Graph

/-!
# The section-centralizer input for the exterior odd-normalizer argument

The actual marked PSL₅(2) quotient is simple, so the chosen conjugation
module has kernel O₂(L). Since L normalizes V, it also normalizes C_G(V).
Consequently an actor in N_G(L) centralizing V has [A,L] inside O₂(L).
The literal perfect residual of C_L(A) then covers L and retains the same
V in its two-core. These are inputs to pushing up, not a uniqueness claim.

Source: Aschbacher--Smith, 12.2.11(a), pp.798--799; 4.4.2 and 4.4.5,
pp.619--620. The quotient projection and conjugation conventions are those
of the original exterior marking.
-/

public section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- The literal component kernel on the marked exterior module. -/
theorem ExteriorMarking.centralizer_eq_core (a : ExteriorMarking D) :
    L ⊓ centralizer (V : Set G) = L.pCoreIn 2 := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  have hs : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (a.quotientEquiv.trans Representation.SL5TenDimensional.projectiveEquiv).isSimpleGroup
  have he := congrArg (Subgroup.map L.subtype) (D.centralizer_eq_core_of_simple hs)
  simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using he

/-- Centralization on V implies centralization of the actual L/O₂(L). -/
theorem ExteriorMarking.centralizing_actor_commutator (a : ExteriorMarking D)
    {A : Subgroup G} (hAM : A ≤ a.M) (hAV : A ≤ centralizer (V : Set G)) :
    ⁅A, L⁆ ≤ L.pCoreIn 2 := by
  rw [← a.centralizer_eq_core]
  refine le_inf (le_normalizer_iff_commutator_le_right.mp hAM) ?_
  have hn : L ≤ normalizer (centralizer (V : Set G) : Set G) :=
    D.normalizes.trans (normalizer_le_normalizer_centralizer V)
  exact (commutator_mono hAV le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp hn)

/-- The section-centralizer in the original maximal local group. -/
theorem ExteriorMarking.centralizing_actor_section (a : ExteriorMarking D)
    {A : Subgroup G} (hAM : A ≤ a.M) (hAV : A ≤ centralizer (V : Set G)) :
    A ≤ sectionCentralizerIn a.M L := by
  exact le_inf hAM ((le_sectionCentralizer_iff A L).mpr
    ⟨hAM, a.centralizing_actor_commutator hAM hAV⟩)

/-- Apply 4.4.5 to the original fixed residual, with its premises discharged. -/
theorem ExteriorMarking.centralizing_actor_cover (a : ExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hAM : A ≤ a.M) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G)) :
    (L : Set G) = (Chapter4.Section04.oddActorResidual L A : Set G) *
      (L.pCoreIn 2 : Set G) ∧
    V = ⁅V, Chapter4.Section04.oddActorResidual L A⁆ ∧
    V ≤ (Chapter4.Section04.oddActorResidual L A).pCoreIn 2 ∧
    (Chapter4.Section04.oddActorResidual L A).pCoreIn 2 ≠ ⊥ :=
  Chapter4.Section04.chosen_oddActorResidual_cover h.toHypothesis1221 D A hAM
    (a.centralizing_actor_commutator hAM hAV) hodd hAV

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
