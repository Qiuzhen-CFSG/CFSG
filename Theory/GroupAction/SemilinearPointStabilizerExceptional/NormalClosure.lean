module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.Coordinates
public import Theory.PGroupCore
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
# Restriction to the normal closure of the scalars

A subgroup containing the scalars inherits the semilinear coordinates. If it
is transitive, its scalar subgroup makes it doubly transitive. Consequently
the normal closure of the scalars inherits the full action hypotheses at
degree at least four. Its two-core is trivial whenever the ambient two-core
is trivial, since a characteristic subgroup of a normal subgroup is normal.

This supplies the proper-normal-subgroup step in GLS, Volume 4, Chapter 1,
Lemma 3.8(c). It does not assume the resulting normal closure equals the
ambient group; that equality belongs to the minimal-counterexample argument.
-/

@[expose] public section

namespace MulAction.SemilinearPointStabilizer

variable {X F : Type*} [Group X] [Field F] [MulAction X F] [FaithfulSMul X F]

namespace Coordinates

variable (c : Coordinates X F)

include c

/-- Restriction retains precisely the same scalar and semilinear formulas. -/
theorem restrict (H : Subgroup X) (hH : c.scalarSubgroup ≤ H) : Coordinates H F where
  scalars a := ⟨⟨c.scalar a, hH ⟨a, rfl⟩⟩, c.scalar_smul a⟩
  semilinear g hg := c.semilinear g hg

/-- Transitivity and all field scalars suffice for double transitivity. -/
theorem two_pretransitive_of_pretransitive [IsPretransitive X F] :
    IsMultiplyPretransitive X F 2 := by
  apply is_two_pretransitive_iff.mpr
  intro a b d e hab hde
  obtain ⟨u, hu⟩ := exists_smul_eq X a (0 : F)
  obtain ⟨v, hv⟩ := exists_smul_eq X d (0 : F)
  have hub : u • b ≠ (0 : F) := by
    intro hb
    exact hab ((MulAction.injective u) (hu.trans hb.symm))
  have hve : v • e ≠ (0 : F) := by
    intro he
    exact hde ((MulAction.injective v) (hv.trans he.symm))
  let t : Fˣ := Units.mk0 ((v • e) / (u • b)) (div_ne_zero hve hub)
  refine ⟨v⁻¹ * c.scalar t * u, ?_, ?_⟩
  · simp only [mul_smul, hu, scalar_smul, mul_zero]
    exact (congrArg (fun x : F => v⁻¹ • x) hv).symm.trans (inv_smul_smul v d)
  · simp only [mul_smul, scalar_smul]
    have ht : (t : F) * (u • b) = v • e := div_mul_cancel₀ _ hub
    rw [ht, inv_smul_smul]

/-- At field cardinality at least three the scalar subgroup is nontrivial. -/
theorem scalarSubgroup_ne_bot [Finite F] (hF : 3 ≤ Nat.card F) :
    c.scalarSubgroup ≠ ⊥ := by
  intro hbot
  have hunit (a : Fˣ) : a = 1 := by
    apply c.scalar_injective
    have hmem : c.scalar a ∈ c.scalarSubgroup := ⟨a, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    simpa using hmem
  have hcard : Nat.card Fˣ = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨1, hunit⟩
  rw [Nat.card_units] at hcard
  omega

/-- The literal normal closure used for the source minimality step. -/
noncomputable def scalarClosure : Subgroup X :=
  Subgroup.normalClosure (c.scalarSubgroup : Set X)

instance scalarClosure_normal : c.scalarClosure.Normal :=
  Subgroup.normalClosure_normal

theorem scalarSubgroup_le_scalarClosure : c.scalarSubgroup ≤ c.scalarClosure :=
  Subgroup.le_normalClosure

theorem scalarClosure_ne_bot [Finite F] (hF : 3 ≤ Nat.card F) :
    c.scalarClosure ≠ ⊥ := by
  intro hbot
  apply c.scalarSubgroup_ne_bot hF
  exact bot_unique (hbot ▸ c.scalarSubgroup_le_scalarClosure)

/-- The normal closure is transitive by primitivity, then doubly transitive
because it still contains every scalar. -/
theorem scalarClosure_two_pretransitive [Finite F] (hF : 3 ≤ Nat.card F)
    (htwo : IsMultiplyPretransitive X F 2) :
    IsMultiplyPretransitive c.scalarClosure F 2 := by
  let : IsPreprimitive X F := isPreprimitive_of_is_two_pretransitive htwo
  let : IsPretransitive c.scalarClosure F :=
    Atlas.GroupTheory.normal_pretransitive c.scalarClosure (c.scalarClosure_ne_bot hF)
  exact (c.restrict c.scalarClosure c.scalarSubgroup_le_scalarClosure).two_pretransitive_of_pretransitive

end Coordinates

/-- Trivial p-core is inherited by normal subgroups, via their characteristic
p-cores and the actual subgroup inclusion. -/
theorem normal_subgroup_pCore_eq_bot {G : Type*} [Group G]
    (p : ℕ) (hcore : pCore p G = ⊥) (H : Subgroup G) [H.Normal] :
    pCore p H = ⊥ := by
  have hle : (pCore p H).map H.subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map H.subtype⟩
  apply eq_bot_iff.mpr
  intro g hg
  have hmem : H.subtype g ∈ pCore p G := hle ⟨g, hg, rfl⟩
  rw [hcore, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end MulAction.SemilinearPointStabilizer
