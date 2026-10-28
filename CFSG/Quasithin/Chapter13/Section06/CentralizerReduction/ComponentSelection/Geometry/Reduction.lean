module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reconstruction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration
public import CFSG.Quasithin.Chapter6.SourceDefs

/-!
# Assembling the geometric and Thompson reductions of 13.6.8–9

Failure of C_G(v) ≤ N_G(V), together with quadratic fusion in the actual
marked A₅ module, makes V_v relatively nonnormal: its nonsingular polar
hyperplanes generate V and would be permuted under hypothetical normality.
The earlier M_v ≤ N_G(V) gives both M_v < G_v and M_v-normalization of V_v.
The Sylow-central seed and characteristic two then place U_v in R₂(G_v)
and Z(Q_v). The Baumann–Frattini argument forces nontrivial images of both
J(T_v) and J(G_v), yielding the faithful binary FF representation.

`GeometricThompsonReduction` packages conclusions, never assumptions of the
construction. The final adapter uses the actual `FlagMarking` and
`LocalReductions` from the earlier configuration, and derives centrality of
z in T_v from centrality in T. Fusion 13.2.6(2) and characteristic two
13.6.6 remain explicit earlier-source premises. This conditional result
neither constructs those inputs nor replaces genuine Hypothesis 13.3.1:
the component-selection/Section 13.6 assembly owner retains all its ambient
clauses, including the uniform-A₅ implication, and discharges these premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.928,
the reduction before 13.6.8, 13.6.8–9 and the following FF-module assertion;
Definition B.2.11 and the used clauses of B.2.14, printed pp.77–78.
-/

public section

open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- Membership in the actual B.2.11 family, with normality inside G_v,
elementary abelianity of the ambient subgroup, and the literal relative
centralizer quotient. These are the B.2.14 clauses used on printed p.928. -/
theorem Uv_mem_reducedFamily (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv v) = pCore 2 (Gv v)) :
    Uv z v ∈ Chapter6.Source.reducedFamily (Gv v) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzmem := (mem_omegaOneCenterAmbient_iff (Tv T v) z).mp hz
  let := internalUv_elementary T z v hSylow hz hchar
  have hE : IsElementaryAbelian 2 (Uv z v) := by
    have hm : (internalUv z v).map (Gv v).subtype = Uv z v :=
      map_subgroupOf_eq_of_le (Uv_le_Gv z v hzmem.1.2)
    rw [← hm]
    exact IsElementaryAbelian.map (Gv v).subtype
  refine ⟨Uv_le_Gv z v hzmem.1.2, hE, inferInstanceAs (internalUv z v).Normal, ?_⟩
  exact internalUv_twoReduced T z v hSylow hzmem.1.2
    (fun t ht => mem_centralizer_singleton_iff.mpr (hzmem.2.2 t ht))

/-- Constructed conclusions of the conditional 13.6.8–9 reduction.
The two Thompson images have their distinct source domains, and the
faithful FF representation agrees with the original star action. -/
structure GeometricThompsonReduction (L T M : Subgroup G) (z v : G) : Prop where
  proper : Mv M v < Gv v
  nonnormal : ¬ ((Vv L z v).subgroupOf (Gv v)).Normal
  seed_mem : z ∈ Gv v
  module_nontrivial : Uv z v ≠ ⊥
  module_reduced : Uv z v ∈ Chapter6.Source.reducedFamily (Gv v)
  module_coreOmega : Uv z v ≤ omegaOneCenterAmbient (Qv v)
  module_central : Uv z v ≤ (center (Qv v)).map (Qv v).subtype
  star_twoCore : pCore 2 (Gstar z v) = ⊥
  sylowThompson : starImage z v (elementaryAbelianMaxJ (Tv T v)) ≠ ⊥
  globalThompson : starImage z v (elementaryAbelianMaxJ (Gv v)) ≠ ⊥
  elementary : IsElementaryAbelian 2 (internalUv z v)
  faithful : letI := elementary
    Function.Injective (uvRepresentation z v seed_mem)
  action_agrees : letI := elementary
    ∀ (g : Gstar z v) (u : Additive (internalUv z v)),
      (((uvRepresentation z v seed_mem g u).toMul : Gv v) : G) =
        (starAction z v g ⟨((u.toMul : Gv v) : G), u.toMul.property⟩ : G)
  ff : letI := elementary
    Representation.BinaryOffender.IsFFModule (uvRepresentation z v seed_mem)

/-- The complete conditional reduction from failure of G_v ≤ N_G(V).
No relative nonnormality, reconstruction, Thompson-image or FF conclusion
is assumed. All geometric inputs to the downstream branch are discharged
using the actual marked A₅ module and earlier quadratic fusion. -/
theorem geometric_thompson_reduction_of_failure
    (s : A5Module.Marking L V) (T M S : Subgroup G)
    (hfusion : FusionPreservesForm s)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T (A5Module.markedV s)) (Gv (A5Module.markedV s)))
    (hz : A5Module.markedZ s ∈ omegaOneCenterAmbient (Tv T (A5Module.markedV s)))
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (A5Module.markedV s)) =
      pCore 2 (Gv (A5Module.markedV s)))
    (hS : S = ChapterB.baumann (Tv T (A5Module.markedV s)))
    (hcontrol : Gv (A5Module.markedV s) ⊓ normalizer (S : Set G) ≤ Mv M (A5Module.markedV s))
    (hMv : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G))
    (hfailure : ¬ Gv (A5Module.markedV s) ≤ normalizer (V : Set G)) :
    GeometricThompsonReduction L T M (A5Module.markedZ s) (A5Module.markedV s) := by
  have hn := Vv_not_normal_of_failure s hfusion hfailure
  obtain ⟨hcore, hstar, hE, hfaith, hJ, hJG, hFF⟩ :=
    thompson_reduction_of_nonnormal L T M S (A5Module.markedZ s) (A5Module.markedV s)
      hSylow hz hchar hS hcontrol (Mv_normalizes_marked_Vv s hfusion M hMv) hn
  let := hE
  exact {
    proper := Mv_lt_Gv_of_failure M V _ hMv hfailure
    nonnormal := hn
    seed_mem := A5Module.markedZ_mem_Gv s
    module_nontrivial := fun he => A5Module.markedZ_ne_one s
      (mem_bot.mp (he ▸ z_mem_Uv (A5Module.markedZ s) (A5Module.markedV s)))
    module_reduced := Uv_mem_reducedFamily T _ _ hSylow hz hchar
    module_coreOmega := hcore
    module_central := Uv_le_center_Qv T _ _ hSylow hz hchar
    star_twoCore := hstar
    sylowThompson := hJ
    globalThompson := hJG
    elementary := hE
    faithful := hfaith
    action_agrees := uvRepresentation_eq_starAction _ _ _
    ff := hFF }

/-- Application to the genuine earlier marked configuration. The supplied
13.6.2–5 outputs give the literal Sylow witness, 13.6.4 Baumann identity and
13.6.5 normalizer control. The marking places the same z in Ω₁(Z(T_v)).
The parent supplies 13.2.6(2) and 13.6.6 on this configuration; it need not
reprove any geometric nonnormality or Thompson/FF premise. -/
theorem geometric_thompson_reduction_of_localReductions
    {T : Sylow 2 G} {M V₁ V₂ : Subgroup G}
    (f : A5Module.FlagMarking T L V V₁ V₂)
    (d : LocalReductions T L M V (A5Module.markedZ f.module) (A5Module.markedV f.module))
    (hfusion : FusionPreservesForm f.module)
    (hchar : Theory.GroupTheory.generalizedFitting (Gv (A5Module.markedV f.module)) =
      pCore 2 (Gv (A5Module.markedV f.module)))
    (hfailure : ¬ Gv (A5Module.markedV f.module) ≤ normalizer (V : Set G)) :
    GeometricThompsonReduction L (T : Subgroup G) M
      (A5Module.markedZ f.module) (A5Module.markedV f.module) := by
  have hzmem := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) _).mp f.z_central
  have hz : A5Module.markedZ f.module ∈
      omegaOneCenterAmbient (Tv (T : Subgroup G) (A5Module.markedV f.module)) := by
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨hzmem.1, A5Module.markedZ_mem_Gv f.module⟩, hzmem.2.1,
        fun t ht => hzmem.2.2 t ht.1⟩
  exact geometric_thompson_reduction_of_failure f.module (T : Subgroup G) M
    (ChapterB.baumann (T : Subgroup G)) hfusion ⟨d.centralizerSylow, d.sylow_image⟩
    hz hchar d.baumann_eq d.normalizer_baumann
    (d.local_centralizer.le.trans inf_le_left) hfailure

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
