module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ModuleIntersections
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# The actual Sylow subgroup of the A₅ seed centralizer

The local two-core R is C_T(V). Normality of C_G(V) inside N_G(V)
makes R Sylow there. The module intersection calculation identifies
C_M(V₃) with C_G(V), while uniqueness over LT traps N_G(R) in M.
The normalizer-index criterion therefore makes that same R Sylow in
the full C_G(V₃), as required before the common-normal argument.

Source: Aschbacher–Smith 13.2.3(2), printed p.879.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem core_ne_bot : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
  intro h
  exact d.chosen.ne_bot (bot_unique (d.chosen.le_core.trans_eq h))

theorem core_normalizer : normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) ≤
    normalizer (L : Set G) :=
  normalizer_le_of_unique_maximalTwoLocal d.unique_maximal_overgroup
    (isPGroup_pCoreIn 2 _) d.core_ne_bot
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

theorem core_le_sylow : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
  rw [← d.sylow_centralizer d.normalizes_L]
  exact inf_le_left

theorem core_le_seed_centralizer : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    centralizer (V₃ : Set G) :=
  d.chosen.core_centralizes.trans (centralizer_le d.third_le)

/-- The same core is Sylow in C_G(V), as an intersection with a normal subgroup. -/
theorem core_module_centralizer_index :
    ¬ 2 ∣ ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (centralizer (V : Set G)) := by
  let N := normalizer (V : Set G)
  let C := (centralizer (V : Set G)).subgroupOf N
  let P := T.subtype d.flag.T_normalizes
  let : C.Normal := normal_subgroupOf_centralizer_normalizer (V : Set G)
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_normal C
  have hi := Q.not_dvd_index
  rw [hQ] at hi
  change ¬ 2 ∣ (P : Subgroup N).relIndex C at hi
  change ¬ 2 ∣ ((T : Subgroup G).subgroupOf N).relIndex
    ((centralizer (V : Set G)).subgroupOf N) at hi
  rw [relIndex_subgroupOf (Subgroup.centralizer_le_normalizer _)] at hi
  rw [← d.sylow_centralizer d.normalizes_L,inf_relIndex_right]
  exact hi

/-- The global Sylow promotion preceding the common-normal argument. -/
theorem core_seed_centralizer_index :
    ¬ 2 ∣ ((L ⊔ (T : Subgroup G)).pCoreIn 2).relIndex (centralizer (V₃ : Set G)) := by
  apply not_dvd_relIndex_of_normalizer_inf_le
    ((L ⊔ (T : Subgroup G)).pCoreIn 2) (centralizer (V : Set G))
    (centralizer (V₃ : Set G)) (isPGroup_pCoreIn 2 _) d.core_le_seed_centralizer
    d.core_module_centralizer_index
  rw [← d.third_centralizer_local]
  exact inf_le_inf d.core_normalizer le_rfl

/-- The Sylow witness retains the exact source core, without conjugate rechoice. -/
theorem core_seed_sylow : ∃ P : Sylow 2 (centralizer (V₃ : Set G)),
    (P : Subgroup (centralizer (V₃ : Set G))).map (centralizer (V₃ : Set G)).subtype =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := ((isPGroup_pCoreIn 2 (L ⊔ (T : Subgroup G))).comap_subtype
    (K := centralizer (V₃ : Set G))).toSylow d.core_seed_centralizer_index
  exact ⟨P,map_subgroupOf_eq_of_le d.core_le_seed_centralizer⟩

/-- Once C_G(V₃) is local, Frattini's argument makes its full normalizer local. -/
theorem seed_normalizer_of_centralizer
    (hC : centralizer (V₃ : Set G) ≤ normalizer (L : Set G)) :
    normalizer (V₃ : Set G) ≤ normalizer (V : Set G) := by
  obtain ⟨P,hP⟩ := d.core_seed_sylow
  have hfr := le_normalizer_sylow_sup (centralizer (V₃ : Set G))
    (normalizer (V₃ : Set G)) (Subgroup.centralizer_le_normalizer _)
    (normalizer_le_normalizer_centralizer V₃) P
  rw [hP] at hfr
  exact (le_inf (hfr.trans (sup_le d.core_normalizer hC)) le_rfl).trans
    d.third_normalizer_local

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
