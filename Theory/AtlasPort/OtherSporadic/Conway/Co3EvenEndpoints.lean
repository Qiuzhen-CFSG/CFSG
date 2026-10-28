/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/Co3EvenEndpoints.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.Co3DecompositionBounds
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu23Witt
/-!
The norm-six stabilizer acting on decompositions into minimum Leech vectors.
The proofs connect the concrete coordinate action with Mathieu incidence geometry.

Source: Gerald Höhn, `Atlas/Conway/Co3EvenEndpoints.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Co3EvenEndpoint (a : Omega) := {y : leech //
  integerDot y.val y.val = 32 ∧
  integerDot (normSixVector a-y).val (normSixVector a-y).val = 32 ∧
  ∀ i, y.val i % 2 = 0}

abbrev Co3PointHeptad (a : Omega) :=
  Mathieu23Points a ⊕ {B // B ∈ mathieu23Blocks a}

theorem constantSupport_injective (k : ℤ) (hk : k ≠ 0) :
    Function.Injective (constantSupportVector k) := by
  intro S T he
  ext i
  have h := congrFun he i
  by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
    simp_all [constantSupportVector]

theorem constantSupport_norm (k : ℤ) (T : Finset Omega) :
    integerDot (constantSupportVector k T) (constantSupportVector k T) = k*k*T.card := by
  simp [integerDot,constantSupportVector,ite_mul]
  ring

theorem constantSupport_two_mem (T : Finset Omega) (hT : T ∈ octads) :
    constantSupportVector 2 T ∈ leech := by
  have hc : supportWord T ∈ golay := by
    obtain ⟨c,_,he⟩ := (octads_mem T).mp hT
    have hh : supportWord T = c.val := by
      rw [← he]; exact binarySupportEquiv.left_inv c.val
    rw [hh]; exact c.prop
  have h := (twoFour_mem_iff T ∅ (fun _ => 0) (fun _ => 0) hc).mpr (by simp)
  convert h using 1
  funext i
  by_cases hi : i ∈ T <;> simp [constantSupportVector,twoFourVector,signedSupport,hi]

theorem normSix_complement_norm (a : Omega) (y : leech)
    (hy : integerDot y.val y.val = 32)
    (hd : integerDot (normSixVector a).val y.val = 24) :
    integerDot (normSixVector a-y).val (normSixVector a-y).val = 32 := by
  have he : integerDot (normSixVector a-y).val (normSixVector a-y).val =
      integerDot (normSixVector a).val (normSixVector a).val + integerDot y.val y.val -
        2*integerDot (normSixVector a).val y.val := by
    change (∑ i, ((normSixVector a).val i-y.val i)*((normSixVector a).val i-y.val i)) = _
    simp only [integerDot,Finset.mul_sum]
    rw [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; ring
  rw [he,normSixVector_norm,hy,hd]
  norm_num

def co3PointEndpoint (a : Omega) (b : Mathieu23Points a) : Co3EvenEndpoint a :=
  ⟨minimumPairPlus a b.val,minimumPairPlus_norm a b.val (show b.val ≠ a from b.prop).symm,by
    have he := normSix_point_decomposition a b.val (show b.val ≠ a from b.prop).symm
    have hh : normSixVector a-minimumPairPlus a b.val = oddMinimumVector b.val 0 := by
      rw [← he]; abel
    rw [hh]; exact oddMinimumVector_norm b.val,by
    intro i
    simp only [minimumPairPlus,coordinateVector,Pi.single_apply,Pi.add_apply]
    split_ifs <;> norm_num⟩

def co3OctadEndpoint (a : Omega) (T : Finset Omega) (hT : T ∈ octads) (ha : a ∈ T) :
    Co3EvenEndpoint a := by
  let y : leech := ⟨constantSupportVector 2 T,constantSupport_two_mem T hT⟩
  have hn : integerDot y.val y.val = 32 := by
    rw [constantSupport_norm,octad_size T hT]; norm_num
  refine ⟨y,hn,normSix_complement_norm a y hn ?_,?_⟩
  · rw [integerDot_normSix]
    change (∑ i, constantSupportVector 2 T i) + 4*constantSupportVector 2 T a = 24
    simp [constantSupportVector,ha,octad_size T hT]
  · intro i; change (if i ∈ T then (2 : ℤ) else 0) % 2 = 0
    split_ifs <;> norm_num

def co3EvenEndpointMap (a : Omega) : Co3PointHeptad a → Co3EvenEndpoint a
  | Sum.inl b => co3PointEndpoint a b
  | Sum.inr B => co3OctadEndpoint a (insert a (mathieu23BlockLift a B.val))
      ((mathieu23Blocks_mem a B.val).mp B.prop) (Finset.mem_insert_self _ _)

theorem co3PointEndpoint_coordinates (a : Omega) (b : Mathieu23Points a) :
    (co3PointEndpoint a b).val.val = constantSupportVector 4 {a,b.val} := by
  funext i
  change coordinateVector a 4 i + coordinateVector b.val 4 i = _
  by_cases hi : i = a
  · subst i; simp [coordinateVector,constantSupportVector,(show b.val ≠ a from b.prop).symm]
  by_cases hj : i = b.val
  · subst i; simp [coordinateVector,constantSupportVector,(show b.val ≠ a from b.prop)]
  simp [coordinateVector,constantSupportVector,hi,hj]

theorem co3EvenEndpointMap_surjective (a : Omega) : Function.Surjective (co3EvenEndpointMap a) := by
  intro y
  rcases normSix_even_decomposition_positive a y.val y.prop.1 y.prop.2.1 y.prop.2.2 with
    ⟨T,hT,ha,hy⟩ | ⟨T,hT,ha,hy⟩
  · obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (show (T.erase a).card = 1 by
      rw [Finset.card_erase_of_mem ha,hT])
    have hba : b ≠ a := by
      have hm : b ∈ T.erase a := by rw [hb]; simp
      exact (Finset.mem_erase.mp hm).1
    have ht : T = {a,b} := by rw [← Finset.insert_erase ha,hb]
    refine ⟨Sum.inl ⟨b,hba⟩,Subtype.ext (Subtype.ext ?_)⟩
    change (co3PointEndpoint a ⟨b,hba⟩).val.val = y.val.val
    rw [co3PointEndpoint_coordinates,hy,ht]
  · let B : {B // B ∈ mathieu23Blocks a} := ⟨mathieu23BlockRestrict a T,by
      rw [mathieu23Blocks_mem,mathieu23Block_restore a T ha]; exact hT⟩
    refine ⟨Sum.inr B,Subtype.ext (Subtype.ext ?_)⟩
    change constantSupportVector 2 (insert a (mathieu23BlockLift a (mathieu23BlockRestrict a T))) = y.val.val
    rw [mathieu23Block_restore a T ha,hy]

theorem co3EvenEndpointMap_injective (a : Omega) : Function.Injective (co3EvenEndpointMap a) := by
  intro p q he
  have hv := congrArg (fun y : Co3EvenEndpoint a => y.val.val) he
  cases p with
  | inl b =>
    cases q with
    | inl c =>
      change (co3PointEndpoint a b).val.val = (co3PointEndpoint a c).val.val at hv
      rw [co3PointEndpoint_coordinates,co3PointEndpoint_coordinates] at hv
      have ht := constantSupport_injective 4 (by decide) hv
      have hb : b.val ∈ ({a,c.val} : Finset Omega) := by rw [← ht]; simp
      have heq : b.val = c.val := by
        rcases Finset.mem_insert.mp hb with h | h
        · exact ((show b.val ≠ a from b.prop) h).elim
        · exact Finset.mem_singleton.mp h
      exact congrArg Sum.inl (Subtype.ext heq)
    | inr C =>
      have h := congrFun hv a
      change (co3PointEndpoint a b).val.val a = constantSupportVector 2 _ a at h
      rw [co3PointEndpoint_coordinates] at h
      norm_num [constantSupportVector] at h
  | inr B =>
    cases q with
    | inl c =>
      have h := congrFun hv a
      change constantSupportVector 2 _ a = (co3PointEndpoint a c).val.val a at h
      rw [co3PointEndpoint_coordinates] at h
      norm_num [constantSupportVector] at h
    | inr C =>
      change constantSupportVector 2 (insert a (mathieu23BlockLift a B.val)) =
        constantSupportVector 2 (insert a (mathieu23BlockLift a C.val)) at hv
      have ht := constantSupport_injective 2 (by decide) hv
      apply congrArg Sum.inr
      apply Subtype.ext
      ext i
      have h := Iff.of_eq (congrArg (fun T : Finset Omega => i.val ∈ T) ht)
      simpa [mathieu23BlockLift,(show i.val ≠ a from i.prop)] using h

def co3PointHeptadEvenEquiv (a : Omega) : Co3PointHeptad a ≃ Co3EvenEndpoint a :=
  Equiv.ofBijective (co3EvenEndpointMap a)
    ⟨co3EvenEndpointMap_injective a,co3EvenEndpointMap_surjective a⟩

theorem co3PointHeptad_card (a : Omega) : Nat.card (Co3PointHeptad a) = 276 := by
  rw [Nat.card_sum,mathieu23_degree,Nat.card_eq_fintype_card,Fintype.card_coe,mathieu23Blocks_card]

theorem co3EvenEndpoint_card (a : Omega) : Nat.card (Co3EvenEndpoint a) = 276 := by
  rw [← Nat.card_congr (co3PointHeptadEvenEquiv a),co3PointHeptad_card]

end Atlas.Conway
