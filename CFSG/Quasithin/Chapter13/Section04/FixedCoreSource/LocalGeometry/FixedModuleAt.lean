module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerSupplementAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.QuotientRows
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNonsplit
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentGeneration

/-!
# Original fixed-core geometry from guarded earlier results at G,T

Start with the literal Hypothesis 13.3.1, the chosen V and its nonzero
fixed part. The earlier 13.3.2 list supplies maximal faithful applicability
and a quasisimple two-core quotient; its guarded fixed-module clause
constructs the actual augmentation marking. The ambient-local 12.2
arguments then construct normalizer control, the escaping omega point,
Thompson movement, the omega decomposition and its index two.

The full original quotient is retained as ordinary A6 or its triple cover.
The normalizer factorization retains O^2(C_M(V)); it does not assume M=LT.
In the ordinary row the full omega-centralizer has the original L1 as
its prime-to-three residual, and the remaining normalizer residual acts
trivially on L/O2(L). All maps and normality are on the literal subgroups.

These are source inputs for the continuing fixed-core recognition assembly,
not full 13.4.1. In particular the ordinary residual must still be killed,
the covered-row argument completed, and the remaining recognition chain
adapted to the same-G,T earlier inputs. Source: Aschbacher--Smith
13.3.2,13.3.4--5 and 13.4.1--6, printed pp.884--886,896--898.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem source_applicability (h₀ : Hypothesis1331 T L)
    (h1332 : Source1332OneTwo T) : Hypothesis1223 KnownSimple.IsKnownSimple T L := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  exact h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
      h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)

/-- Construct the common source geometry in both genuine quotient rows.
The guards are retained at every actual component, so this theorem also
applies to a reciprocal core once its own Hypothesis 13.3.1 is proved. -/
theorem original_fixed_core_geometry_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L) :
    ∃ m : CoreMarking D,
      (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
        Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L)) ∧
      normalizer (L : Set G) = normalizer (V : Set G) ∧
      centralizer (V ⊓ centralizer (L : Set G) : Set G) = normalizer (L : Set G) ∧
      normalizer (L : Set G) = (L ⊔ (T : Subgroup G)) ⊔ normalizerActionResidual L V ∧
      normalizer (L : Set G) ≤ normalizer (normalizerActionResidual L V : Set G) ∧
      normalizerActionResidual L V ≤ centralizer (V : Set G) ∧
      IsPPerfect 2 (normalizerActionResidual L V) ∧
      ⁅L,normalizerActionResidual L V⁆ ≤ (centralCore L).map L.subtype ∧
      ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ = L ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ⊔
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
        (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
        z.val ∉ centralizer (L : Set G) ∧
        ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
        Nat.card (V ⊓ omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) = 4 ∧
        (m.weight z = 2 ∨ m.weight z = 4) := by
  have h := source_applicability h₀ h1332
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  obtain ⟨hM,hnY,hY,hpY,_⟩ := normalizer_action_residual_at h structural D m
  obtain ⟨z,hz1,hzT,hzL,hzout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  exact ⟨m,original_quotient_rows D m h.quasisimple,
    normalizer_component_eq_module_at h structural D m,
    fixed_centralizer_eq_normalizer_at h structural D m,hM,hnY,hY,hpY,
    normalizer_action_residual_commutator_at h structural D m,
    original_core_thompson_generation_at h₀ h structural D m earlier,
    original_omega_decomposition_at h₀ h structural D m earlier,
    original_omega_fixed_index_at h₀ h structural D m earlier,
    z,hz1,hzT,hzL,hzout,m.central_four_card_eq_four_at h structural z hz1 hzT hzout,
    m.nonfixed_weight z hzL⟩

/-- The ordinary residual identities at the actual escaping point, with
initial marking, applicability and omega geometry all constructed. -/
theorem ordinary_fixed_module_residuals_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) :
    (primeToResidual 3 (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype = L ∧
      ⁅L,normalizerActionResidual L V⁆ ≤ L.pCoreIn 2 ∧
      ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
        z.val ∉ centralizer (L : Set G) ∧
        ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ∧
        (primeToResidual 3 (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).map
          (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)).subtype =
            Solvable.firstCentralizerResidual L z.val := by
  have h := source_applicability h₀ h1332
  obtain ⟨m,_,_,_,_,_,_,_,hcomm,_,_,_,z,hz1,hzT,hzL,hzout,_⟩ :=
    original_fixed_core_geometry_at h₀ D hfixed structural earlier h1332 fixed
  rw [Solvable.centralCore_eq_twoCore_of_ordinary eL] at hcomm
  exact ⟨normalizer_primeToThree_residual_at h structural eL,hcomm,z,hz1,hzT,hzL,hzout,
    ordinary_omega_residual_at h₀ h structural D m earlier eL z hzT hzL⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
