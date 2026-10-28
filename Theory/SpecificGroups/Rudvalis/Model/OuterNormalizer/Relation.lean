module

public import Theory.SpecificGroups.Rudvalis.Model.Primitive

/-!
# A concrete binary relation for the Rudvalis normalizer calculation

Transport the forest component rooted at 1 along the checked transitivity
forest. This defines a computable relation on the actual 4060 letters.
The transport and the component sizes are proved here. Invariance under the
ATLAS generators and rigidity of the relation are separate calculations.

Source: GLS3, Table 5.3r, printed p.279, and the ATLAS tables documented in
`Model.PermutationData`. No order or simplicity certificate is used.
-/

namespace Rudvalis.OuterNormalizer
open PrimitiveData

/-- Follow the transitivity tree backwards, with a bound on the path length. -/
@[expose] public def toBase : Nat → Fin 4060 → Model
  | 0, _ => 1
  | n + 1, x =>
    if x = 0 then 1
    else if Data.aMap (transParent x) = x then toBase n (transParent x) * a⁻¹
    else toBase n (transParent x) * b⁻¹

private theorem toBase_smul_aux (n : Nat) (x : Fin 4060) (hx : transDepth x ≤ n) :
    toBase n x • x = 0 := by
  induction n generalizing x with
  | zero =>
    rcases trans_edge x with rfl | ⟨hd, _⟩
    · rfl
    · omega
  | succ n ih =>
    by_cases h0 : x = 0
    · subst x
      simp [toBase]
    rcases trans_edge x with he | ⟨hd, he⟩
    · exact (h0 he).elim
    have hp : transDepth (transParent x) ≤ n := by omega
    by_cases ha : Data.aMap (transParent x) = x
    · have ha' : a • transParent x = x := ha
      simp only [toBase, if_neg h0, if_pos ha, mul_smul]
      rw [show a⁻¹ • x = transParent x from inv_smul_eq_iff.mpr ha'.symm]
      exact ih _ hp
    · have hb : b • transParent x = x := he.resolve_left ha
      simp only [toBase, if_neg h0, if_neg ha, mul_smul]
      rw [show b⁻¹ • x = transParent x from inv_smul_eq_iff.mpr hb.symm]
      exact ih _ hp

/-- A word in the actual generators taking `x` to the base point. -/
public theorem toBase_smul (x : Fin 4060) :
    toBase (transDepth x) x • x = 0 := toBase_smul_aux _ _ le_rfl

/-- The forest root seen after transporting the first argument to zero. -/
@[expose] public def label (x y : Fin 4060) : Fin 4060 :=
  root (toBase (transDepth x) x • y)

/-- The candidate orbital of subdegree 1755. -/
@[expose] public def adj (x y : Fin 4060) : Prop := label x y = 1

public instance (x y : Fin 4060) : Decidable (adj x y) :=
  inferInstanceAs (Decidable (_ = _))

public theorem label_zero (y : Fin 4060) : label 0 y = root y := by
  have h : transDepth 0 = 0 := by decide +kernel
  simp [label, h, toBase]

public theorem adj_zero (y : Fin 4060) : adj 0 y ↔ root y = 1 := by
  simp only [adj, label_zero]

/-- Every candidate row is a translate of the first forest component. -/
public theorem adj_translate (x y : Fin 4060) :
    adj x y ↔ adj 0 (toBase (transDepth x) x • y) := by
  rw [adj_zero]
  rfl

/-- The existing forest supplies actual elements of the point stabilizer. -/
public theorem root_reachable (x : Fin 4060) :
    ∃ g : Model, g • (0 : Fin 4060) = 0 ∧ g • root x = x := by
  induction x using (measure stabDepth).wf.induction with
  | h x ih =>
    rcases stab_edge x with hr | ⟨hd, hr, he⟩
    · exact ⟨1, one_smul _ _, (one_smul _ _).trans hr.symm⟩
    obtain ⟨g, hg0, hg⟩ := ih (stabParent x) hd
    rw [hr] at hg
    rcases he with hs | ht
    · exact ⟨s * g, by rw [mul_smul, hg0, s_fix],
        by rw [mul_smul, hg, ← sMap_eq]; exact hs⟩
    · exact ⟨t * g, by rw [mul_smul, hg0, t_fix],
        by rw [mul_smul, hg, ← tMap_eq]; exact ht⟩

public theorem root_one_card : {x : Fin 4060 | root x = 1}.ncard = 1755 := by
  have he : {x : Fin 4060 | root x = 0 ∨ root x = 1} =
      insert 0 {x | root x = 1} := by
    ext x
    simp only [Set.mem_ofPred, Set.mem_insert_iff, root_zero]
  have hn : (0 : Fin 4060) ∉ {x | root x = 1} := by decide +kernel
  have hc := first_union_card
  rw [he, Set.ncard_insert_of_notMem hn] at hc
  omega

public theorem root_six_card : {x : Fin 4060 | root x = 6}.ncard = 2304 := by
  have he : {x : Fin 4060 | root x = 0 ∨ root x = 6} =
      insert 0 {x | root x = 6} := by
    ext x
    simp only [Set.mem_ofPred, Set.mem_insert_iff, root_zero]
  have hn : (0 : Fin 4060) ∉ {x | root x = 6} := by decide +kernel
  have hc := second_union_card
  rw [he, Set.ncard_insert_of_notMem hn] at hc
  omega

/-- All permutations preserving the concrete binary relation. -/
@[expose] public def relationAut : Subgroup (Equiv.Perm (Fin 4060)) where
  carrier := {p | ∀ x y, adj (p x) (p y) ↔ adj x y}
  one_mem' := fun _ _ => Iff.rfl
  mul_mem' := by
    intro p q hp hq x y
    exact (hp (q x) (q y)).trans (hq x y)
  inv_mem' := by
    intro p hp x y
    simpa using (hp (p⁻¹ x) (p⁻¹ y)).symm

/-- The two generator checks imply invariance under the whole model. -/
public theorem model_le_relationAut (ha : aPerm ∈ relationAut) (hb : bPerm ∈ relationAut) :
    modelSubgroup ≤ relationAut := by
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | hg)
  · exact ha
  · exact Set.mem_singleton_iff.mp hg ▸ hb

end Rudvalis.OuterNormalizer
