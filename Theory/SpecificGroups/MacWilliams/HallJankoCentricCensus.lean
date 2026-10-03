module

public import Theory.SpecificGroups.MacWilliams.HallJankoCentricNodes
public import Theory.SpecificGroups.MacWilliams.HallJankoCentricCoverage
public import Theory.SpecificGroups.MacWilliams.HallJankoCentricNodeChecks
public import Theory.GroupTheory.SubgroupEnumerationDescending
public import Theory.GroupTheory.PGroup.Omega
public import Theory.Frattini.PGroup

/-!
# Certificate assembly for the Hall–Janko centric census

The explicit node family lists subgroups themselves, so maximal descent needs
no conjugacy transport. Centricity is upward closed. Starting at the whole
group and covering every centric maximal child therefore covers every centric
subgroup, including children of nodes later excluded by Frattini witnesses.
Separate local checks supply either an outside Frattini witness or one of the
three structural alternatives involving the marked normal four.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.4, p.386 and application
p.395; MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.HallJankoCoordinates.CentricCensus

/-- The exact alternatives needed from a centric subgroup of the coordinate group. -/
@[expose] public def Outcome (U : Subgroup Code) : Prop :=
  (∃ g : Subgroup.normalizer (U : Set Code), (g : Code) ∉ U ∧
    ∀ x : U, x⁻¹ * U.normalizerMonoidHom g x ∈ frattini U) ∨
  (four ≤ U ∧
    ((((omega₁ (Subgroup.center U) (p := 2)).map (Subgroup.center U).subtype).map
          U.subtype = four) ∨
      (Subgroup.center U).map U.subtype = Subgroup.center Code ∨
      (IsElementaryAbelian 2 U ∧ Nat.card U = 16)))

/-- An exact maximal-child certificate exhausts all centric subgroups.
Only centricity is used to prune descent. -/
public theorem eq_node_of_maximal_checks
    (hstep : ∀ (i : Fin 142) (H : Subgroup Code), H ⋖ node i →
      Subgroup.centralizer (H : Set Code) ≤ H → ∃ j : Fin 142, H = node j)
    (H : Subgroup Code) (hH : Subgroup.centralizer (H : Set Code) ≤ H) :
    ∃ i : Fin 142, H = node i := by
  classical
  let : Finite (Subgroup Code) := Finite.of_injective
    (fun K : Subgroup Code => (K : Set Code)) SetLike.coe_injective
  induction H using (wellFounded_gt (α := Subgroup Code)).induction with
  | h H ih =>
    by_cases ht : H = ⊤
    · exact ⟨0, ht.trans node_zero.symm⟩
    · obtain ⟨V, hHV, _⟩ := exists_covBy_le_of_lt (lt_top_iff_ne_top.mpr ht)
      obtain ⟨i, rfl⟩ := ih V hHV.lt
        (Theory.GroupTheory.SubgroupEnumeration.centralizer_le_of_le hHV.le hH)
      exact hstep i H hHV hH

/-- Coverage and node checks together imply the requested centric census. -/
public theorem census_of_checks
    (hstep : ∀ (i : Fin 142) (H : Subgroup Code), H ⋖ node i →
      Subgroup.centralizer (H : Set Code) ≤ H → ∃ j : Fin 142, H = node j)
    (hnode : ∀ i : Fin 142, Outcome (node i))
    (U : Subgroup Code) (hcent : Subgroup.centralizer (U : Set Code) ≤ U) :
    Outcome U := by
  obtain ⟨i, rfl⟩ := eq_node_of_maximal_checks hstep U hcent
  exact hnode i

/-- The certified finite centric-subgroup census for the Hall--Janko
coordinate group. -/
public theorem centric_census (U : Subgroup Code)
    (hcent : Subgroup.centralizer (U : Set Code) ≤ U) : Outcome U := by
  apply census_of_checks (U := U)
  · intro i H hmax hH
    exact maximal_coverage i H hmax hH
  · intro i
    simpa only [Outcome] using node_alternative i
  · exact hcent

end MacWilliamsSylow.HallJankoCoordinates.CentricCensus
