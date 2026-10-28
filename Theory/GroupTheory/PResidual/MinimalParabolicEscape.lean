module

public import Theory.GroupTheory.MinimalParabolicGeneration
public import Theory.GroupTheory.PResidual.CentralizerEscape

/-!
# Minimal parabolics retaining residual movement

Suppose the two-residual of C escapes the join of M ∩ C and its centralizer
of W, and N_C(T) lies in M. Select an overgroup of T minimal outside this
join. It is a minimal parabolic, and its two-residual still moves W:
otherwise its residual and Sylow supplement both lie in the join.

The minimality is relative to the larger join. In particular, this result
does not assert minimality among overgroups outside M. This is the precise
finite-minimality consequence of the displayed escape in Aschbacher--Smith,
15.1.14(1), printed p.1091.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem exists_minimalParabolic_of_residual_escape
    (T : Sylow 2 G) (C M W : Subgroup G)
    (hTC : (T : Subgroup G) ≤ C) (hTM : (T : Subgroup G) ≤ M)
    (hNT : C ⊓ normalizer (T : Set G) ≤ M)
    (hescape : ¬ (pResidual 2 C).map C.subtype ≤
      (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓ centralizer (W : Set G))) :
    ∃ P : Subgroup G, P ≤ C ∧
      P ∈ nonNormalUniqueMaximalOvergroups (T : Subgroup G) ∧
      ¬ P ≤ M ∧
      ¬ (pResidual 2 P).map P.subtype ≤ centralizer (W : Set G) ∧
      ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < P →
        Y ≤ (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓ centralizer (W : Set G)) := by
  classical
  let K := (M ⊓ C) ⊔ ((pResidual 2 C).map C.subtype ⊓ centralizer (W : Set G))
  have hTK : (T : Subgroup G) ≤ K := (le_inf hTM hTC).trans le_sup_left
  have hCK : ¬ C ≤ K := fun h => hescape ((map_subtype_le _).trans h)
  let S : Set (Subgroup G) := {P | (T : Subgroup G) ≤ P ∧ P ≤ C ∧ ¬ P ≤ K}
  obtain ⟨P, hP⟩ := (Set.toFinite S).exists_minimalFor id S ⟨C, hTC, le_rfl, hCK⟩
  have hTP : (T : Subgroup G) ≤ P := hP.1.1
  have hPC : P ≤ C := hP.1.2.1
  have hPK : ¬ P ≤ K := hP.1.2.2
  have hproper : ∀ Y : Subgroup G, (T : Subgroup G) ≤ Y → Y < P → Y ≤ K := by
    intro Y hTY hYP
    by_contra hn
    exact hYP.not_ge (hP.2 ⟨hTY, hYP.le.trans hPC, hn⟩ hYP.le)
  have hlt : P ⊓ K < P := lt_of_le_of_ne inf_le_left (by
    intro he
    exact hPK (he ▸ inf_le_right))
  have hcov : P ⊓ K ⋖ P := ⟨hlt, by
    intro Y hBY hYP
    exact hBY.not_ge (le_inf hYP.le (hproper Y
      ((le_inf hTP hTK).trans hBY.le) hYP))⟩
  have hu : Order.HasUniqueMaximalOver (T : Subgroup G) P := by
    refine ⟨(le_inf hTP hTK).trans_lt hlt, P ⊓ K, ⟨le_inf hTP hTK, hcov⟩, ?_⟩
    intro Y hY
    have hYB : Y ≤ P ⊓ K := le_inf hY.2.le (hproper Y hY.1 hY.2.lt)
    exact ((hY.2.eq_or_eq hYB inf_le_left).resolve_right hlt.ne).symm
  have hPM : ¬ P ≤ M := fun h => hPK ((le_inf h hPC).trans le_sup_left)
  refine ⟨P, hPC, ⟨hu, fun hn => hPM ((le_inf hPC hn).trans hNT)⟩, hPM, ?_, hproper⟩
  intro hres
  have hRK : (pResidual 2 P).map P.subtype ≤ K :=
    (le_inf (embedded_pResidual_mono 2 hPC) hres).trans le_sup_right
  have he := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTP))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTP] at he
  exact hPK (he ▸ sup_le hRK hTK)

end Subgroup
