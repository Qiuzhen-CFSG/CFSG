module

public import ABG.Recognition.ThreeLinearMSubgroup
public import ABG.Recognition.ThreeLinearIndex39
public import ABG.Recognition.ThreeLinearCosetAction

/-!
# Wong's faithful doubly transitive action on thirteen cosets

The actual subgroup `K = M ⊔ C_G(τ)` is proper by the fixed-space dimensions
`3 + 2 > 4`. Its index is thirteen or thirty-nine; the GL₂(3) centralizer
obstruction excludes thirty-nine. The independent coset-character theorem
then identifies its genuine permutation character with `1 + χ₆`, for the
same catalog used to construct `M`. Simplicity gives faithfulness, and the
character norm gives double transitivity.

The package retains the original local data and the order-thirty-six
subgroup, so all character values and the four-line fixed sets refer to one
and the same action. Every input is constructed from the original recognition
hypotheses in `exists_threeLinearPermutationData`.

Source: W. J. Wong, “On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2” (1964), Theorem 6(b), printed pp.110–111.
-/

namespace ABG
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

variable {G : Type*} [Group G] [Finite G]

/-- The join from Wong's actual fixed-space configuration has index thirteen. -/
public theorem ThreeLinearLocalData.MSubgroupConfiguration.sup_index
    [IsSimpleGroup G] {c : ThreeLinearLocalData G} {M : Subgroup G}
    (hM : c.MSubgroupConfiguration M) :
    (M ⊔ Subgroup.centralizer ({c.involution} : Set G)).index = 13 := by
  have halt := index_thirteen_or_thirtynine_of_subgroup_orders c.group_order
    M (Subgroup.centralizer ({c.involution} : Set G))
    (M ⊔ Subgroup.centralizer ({c.involution} : Set G))
    hM.card hM.centralizer_card le_sup_left le_sup_right hM.sup_ne_top
  exact halt.resolve_right (index_ne_thirtynine_of_glTwoThree_centralizer
    c.group_order c.involution c.order_involution c.centralizerEquiv _ le_sup_right)

/-- The original character catalog together with Wong's constructed `M`.
The index and action properties are consequences, rather than extra inputs. -/
public structure ThreeLinearPermutationData (G : Type*) [Group G] [Finite G]
    extends ThreeLinearLocalData G where
  M : Subgroup G
  configuration : toThreeLinearLocalData.MSubgroupConfiguration M

namespace ThreeLinearPermutationData

variable (c : ThreeLinearPermutationData G)

/-- The stabilizer is the actual join of `M` with the involution centralizer. -/
@[expose] public def subgroup : Subgroup G :=
  c.M ⊔ Subgroup.centralizer ({c.involution} : Set G)

/-- The constructed stabilizer has index thirteen. -/
public theorem subgroup_index [IsSimpleGroup G] : c.subgroup.index = 13 :=
  c.configuration.sup_index

/-- The line action has thirteen cosets. -/
public theorem coset_card [IsSimpleGroup G] : Nat.card (G ⧸ c.subgroup) = 13 := by
  rw [← Subgroup.index_eq_card, c.subgroup_index]

/-- The genuine permutation representation has character `1 + χ₆` of the
original local catalog. -/
public theorem permutation_character [IsSimpleGroup G] :
    (ThreeGlobalDegreeData.cosetRepresentation c.subgroup).character =
      1 + c.decomposition.χ 5 :=
  c.toThreeGlobalDegreeData.cosetRepresentation_character c.group_order _ c.subgroup_index

/-- The action on the actual constructed cosets is faithful. -/
public theorem faithful [IsSimpleGroup G] : FaithfulSMul G (G ⧸ c.subgroup) :=
  ThreeGlobalDegreeData.cosetAction_faithful _ c.subgroup_index

/-- The action on the actual constructed cosets is doubly transitive. -/
public theorem two_pretransitive [IsSimpleGroup G] :
    MulAction.IsMultiplyPretransitive G (G ⧸ c.subgroup) 2 :=
  c.toThreeGlobalDegreeData.cosetAction_two_pretransitive c.group_order _ c.subgroup_index

/-- The character identity counts fixed cosets for every group element. -/
public theorem fixedPoint_count [IsSimpleGroup G] (g : G) :
    (Nat.card (MulAction.fixedBy (G ⧸ c.subgroup) g) : ℂ) =
      1 + c.decomposition.χ 5 g :=
  c.toThreeGlobalDegreeData.coset_fixedPoint_count c.group_order _ c.subgroup_index g

/-- Wong's complete fixed-coset table, expressed as natural-number counts. -/
public theorem fixedPoint_counts [IsSimpleGroup G] (g : G) :
    Nat.card (MulAction.fixedBy (G ⧸ c.subgroup) g) =
      if g = 1 then 13 else if orderOf g = 2 then 5 else
      if ThreeLinearPlane.IsPointElement G g then 4 else
      if orderOf g = 6 then 2 else if orderOf g = 13 then 0 else 1 := by
  classical
  have h := c.fixedPoint_count g
  rw [c.sixth_values] at h
  split_ifs at h ⊢ <;> norm_num at h ⊢ <;> exact_mod_cast h

/-- An eligible order-three element fixes exactly four lines. -/
public theorem fixedPoint_count_pointElement [IsSimpleGroup G]
    (g : G) (hg : ThreeLinearPlane.IsPointElement G g) :
    Nat.card (MulAction.fixedBy (G ⧸ c.subgroup) g) = 4 := by
  have hne : g ≠ 1 := by
    intro h
    simpa [h] using hg.1
  rw [c.fixedPoint_counts]
  simp [hne, hg, hg.1]

/-- Every other order-three element fixes exactly one line. -/
public theorem fixedPoint_count_other_order_three [IsSimpleGroup G]
    (g : G) (hg : orderOf g = 3) (hn : ¬ ThreeLinearPlane.IsPointElement G g) :
    Nat.card (MulAction.fixedBy (G ⧸ c.subgroup) g) = 1 := by
  have hne : g ≠ 1 := by
    intro h
    simp [h] at hg
  rw [c.fixedPoint_counts]
  simp [hne, hg, hn]

/-- An involution fixes exactly five lines. -/
public theorem fixedPoint_count_involution [IsSimpleGroup G]
    (g : G) (hg : orderOf g = 2) :
    Nat.card (MulAction.fixedBy (G ⧸ c.subgroup) g) = 5 := by
  have hne : g ≠ 1 := by
    intro h
    simp [h] at hg
  rw [c.fixedPoint_counts]
  simp [hne, hg]

end ThreeLinearPermutationData

/-- Construct the action data without changing the supplied local catalog. -/
public theorem ThreeLinearLocalData.exists_permutationData
    (c : ThreeLinearLocalData G)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1) :
    ∃ d : ThreeLinearPermutationData G, d.toThreeLinearLocalData = c := by
  obtain ⟨M, hM⟩ := c.exists_mSubgroup_configuration hC
  exact ⟨{ toThreeLinearLocalData := c, M := M, configuration := hM }, rfl⟩

/-- Wong's thirteen-coset action follows from the original simple-group,
semidihedral Sylow-two and actual GL₂(3) centralizer hypotheses. -/
public theorem exists_threeLinearPermutationData [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S) (hcard : Nat.card S = 16)
    (hC : ∀ t : G, orderOf t = 2 →
      Subgroup.centralizer ({t} : Set G) ≃* GL2 3 1)
    (hG : Nat.card G = 5616) : Nonempty (ThreeLinearPermutationData G) := by
  obtain ⟨c⟩ := exists_threeLinearLocalData S hS hcard hC hG
  obtain ⟨d, _⟩ := c.exists_permutationData hC
  exact ⟨d⟩

end
end ABG
