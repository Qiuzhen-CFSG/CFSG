module

public import Theory.Mathieu.M11.Properties.Centralizer
public import Theory.Mathieu.M11.Properties.InvolutionClasses
public import Theory.Mathieu.M11.Properties.PowersetStabilizer

set_option maxHeartbeats 800000
set_option maxRecDepth 100000

namespace Sporadic.Mathieu

/-!
## Maximality of the standard involution centralizer

The finite certificate is restricted to the 48-element centralizer normal
form; it never enumerates the 7920 elements of M11.
-/

private abbrev M11TripleSet := Set.powersetCard (Fin 11) 3

private abbrev m11FixedTriple : M11TripleSet :=
  ⟨{1, 3, 6}, by change ({1, 3, 6} : Finset (Fin 11)).card = 3; decide⟩

private def m11MaximalRep : Fin 8 → M11TripleSet := ![
  ⟨{1, 3, 6}, by change ({1, 3, 6} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{0, 2, 7}, by change ({0, 2, 7} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{3, 8, 9}, by change ({3, 8, 9} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{0, 1, 2}, by change ({0, 1, 2} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{1, 2, 3}, by change ({1, 2, 3} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{4, 8, 9}, by change ({4, 8, 9} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{4, 5, 8}, by change ({4, 5, 8} : Finset (Fin 11)).card = 3; decide⟩,
  ⟨{3, 4, 10}, by change ({3, 4, 10} : Finset (Fin 11)).card = 3; decide⟩
]

private theorem m11_fixedPoints_eq_fixedTriple :
    Function.fixedPoints m11GeneratorA =
      (m11FixedTriple : Set (Fin 11)) := by
  ext x
  fin_cases x <;>
    change m11GeneratorA _ = _ ↔ _ ∈ (m11FixedTriple : Finset (Fin 11)) <;> decide

private theorem m11_ambient_centralizer_mem
    (g : m11InvolutionCentralizer) :
    ((g : M11) : Equiv.Perm (Fin 11)) ∈
      Subgroup.centralizer ({m11GeneratorA} : Set (Equiv.Perm (Fin 11))) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg (fun z : M11 => (z : Equiv.Perm (Fin 11)))
    ((m11_mem_involutionCentralizer_iff (g : M11)).mp g.property)

open scoped Pointwise in
private theorem m11_centralizer_le_fixedTriple_stabilizer :
    m11InvolutionCentralizer ≤
      MulAction.stabilizer M11 m11FixedTriple := by
  intro g hg
  apply m11_mem_powersetCard_stabilizer_of_set_eq (g : M11) m11FixedTriple
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  rw [← m11_fixedPoints_eq_fixedTriple]
  let g' : m11InvolutionCentralizer :=
    ⟨g⁻¹, m11InvolutionCentralizer.inv_mem hg⟩
  have hiff :=
    Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
      (m11_ambient_centralizer_mem g')
      (x := x)
  change
    Function.IsFixedPt m11GeneratorA ((g⁻¹ : M11) • x) ↔
      Function.IsFixedPt m11GeneratorA x
  simpa [g', Subgroup.smul_def, Equiv.Perm.smul_def] using hiff

private theorem m11_fixedTriple_stabilizer_card :
    Nat.card (MulAction.stabilizer M11 m11FixedTriple) = 48 := by
  let _ : MulAction.IsMultiplyPretransitive M11 (Fin 11) 4 :=
    m11_isFourPretransitive
  let _ : MulAction.IsMultiplyPretransitive M11 (Fin 11) 3 :=
    MulAction.isMultiplyPretransitive_of_le
      (m := 3) (n := 4) (by norm_num) (by norm_num)
  let _ : MulAction.IsPretransitive M11 M11TripleSet :=
    Set.powersetCard.isPretransitive_of_isMultiplyPretransitive
      (G := M11) (α := Fin 11) (n := 3) inferInstance
  have hmul := Subgroup.card_mul_index
    (MulAction.stabilizer M11 m11FixedTriple)
  rw [MulAction.index_stabilizer_of_transitive M11 m11FixedTriple,
    Set.powersetCard.card, Nat.card_fin, m11_order] at hmul
  norm_num [Nat.choose] at hmul ⊢
  omega

private theorem m11_involutionCentralizer_eq_fixedTriple_stabilizer :
    m11InvolutionCentralizer =
      MulAction.stabilizer M11 m11FixedTriple := by
  apply Subgroup.eq_of_le_of_card_ge
    m11_centralizer_le_fixedTriple_stabilizer
  rw [m11_fixedTriple_stabilizer_card, m11_involutionCentralizer_card]

private noncomputable def m11MaximalNF
    (p : Fin 3 × Fin 8 × Fin 2) : M11 :=
  m11CentralizerV ^ (p.1 : Nat) *
    (m11CentralizerU ^ (p.2.1 : Nat) *
      m11CentralizerW ^ (p.2.2 : Nat))

private theorem m11MaximalNF_mem
    (p : Fin 3 × Fin 8 × Fin 2) :
    m11MaximalNF p ∈ m11InvolutionCentralizer := by
  apply m11InvolutionCentralizer.mul_mem
  · exact m11InvolutionCentralizer.pow_mem m11CentralizerV_mem p.1
  · apply m11InvolutionCentralizer.mul_mem
    · exact m11InvolutionCentralizer.pow_mem m11CentralizerU_mem p.2.1
    · exact m11InvolutionCentralizer.pow_mem
        (m11InvolutionCentralizer.mul_mem
          (m11InvolutionCentralizer.pow_mem
            (m11InvolutionCentralizer.mul_mem
              m11CentralizerU_mem m11CentralizerV_mem) 2)
          m11CentralizerU_mem) p.2.2

private def m11MaximalUPerm : Equiv.Perm (Fin 11) :=
  List.formPerm [2, 7, 4, 8, 10, 5, 11, 9] *
    Equiv.swap (3 : Fin 11) 6

private def m11MaximalVPerm : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 3, 6] * List.formPerm [2, 7, 11] *
    List.formPerm [4, 10, 5]

private def m11MaximalWPerm : Equiv.Perm (Fin 11) :=
  Equiv.swap (3 : Fin 11) 6 * Equiv.swap (4 : Fin 11) 11 *
    Equiv.swap (5 : Fin 11) 9 * Equiv.swap (7 : Fin 11) 8

private def m11MaximalNFPerm
    (p : Fin 3 × Fin 8 × Fin 2) : Equiv.Perm (Fin 11) :=
  m11MaximalVPerm ^ (p.1 : Nat) *
    (m11MaximalUPerm ^ (p.2.1 : Nat) *
      m11MaximalWPerm ^ (p.2.2 : Nat))

private def m11MaximalNFAction_0_0_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 4
    | 5 => 5
    | 6 => 6
    | 7 => 7
    | 8 => 8
    | 9 => 9
    | 10 => 10

private def m11MaximalNFAction_0_0_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 1
    | 2 => 2
    | 3 => 6
    | 4 => 0
    | 5 => 9
    | 6 => 3
    | 7 => 8
    | 8 => 7
    | 9 => 5
    | 10 => 10

private def m11MaximalNFAction_0_1_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 1
    | 2 => 7
    | 3 => 6
    | 4 => 8
    | 5 => 0
    | 6 => 3
    | 7 => 4
    | 8 => 10
    | 9 => 2
    | 10 => 5

private def m11MaximalNFAction_0_1_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 1
    | 2 => 7
    | 3 => 3
    | 4 => 9
    | 5 => 2
    | 6 => 6
    | 7 => 10
    | 8 => 4
    | 9 => 0
    | 10 => 5

private def m11MaximalNFAction_0_2_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 1
    | 2 => 4
    | 3 => 3
    | 4 => 10
    | 5 => 9
    | 6 => 6
    | 7 => 8
    | 8 => 5
    | 9 => 7
    | 10 => 0

private def m11MaximalNFAction_0_2_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 1
    | 2 => 4
    | 3 => 6
    | 4 => 2
    | 5 => 7
    | 6 => 3
    | 7 => 5
    | 8 => 8
    | 9 => 9
    | 10 => 0

private def m11MaximalNFAction_0_3_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 1
    | 2 => 8
    | 3 => 6
    | 4 => 5
    | 5 => 2
    | 6 => 3
    | 7 => 10
    | 8 => 0
    | 9 => 4
    | 10 => 9

private def m11MaximalNFAction_0_3_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 1
    | 2 => 8
    | 3 => 3
    | 4 => 7
    | 5 => 4
    | 6 => 6
    | 7 => 0
    | 8 => 10
    | 9 => 2
    | 10 => 9

private def m11MaximalNFAction_0_4_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 1
    | 2 => 10
    | 3 => 3
    | 4 => 0
    | 5 => 7
    | 6 => 6
    | 7 => 5
    | 8 => 9
    | 9 => 8
    | 10 => 2

private def m11MaximalNFAction_0_4_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 1
    | 2 => 10
    | 3 => 6
    | 4 => 4
    | 5 => 8
    | 6 => 3
    | 7 => 9
    | 8 => 5
    | 9 => 7
    | 10 => 2

private def m11MaximalNFAction_0_5_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 1
    | 2 => 5
    | 3 => 6
    | 4 => 9
    | 5 => 4
    | 6 => 3
    | 7 => 0
    | 8 => 2
    | 9 => 10
    | 10 => 7

private def m11MaximalNFAction_0_5_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 1
    | 2 => 5
    | 3 => 3
    | 4 => 8
    | 5 => 10
    | 6 => 6
    | 7 => 2
    | 8 => 0
    | 9 => 4
    | 10 => 7

private def m11MaximalNFAction_0_6_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 1
    | 2 => 0
    | 3 => 3
    | 4 => 2
    | 5 => 8
    | 6 => 6
    | 7 => 9
    | 8 => 7
    | 9 => 5
    | 10 => 4

private def m11MaximalNFAction_0_6_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 1
    | 2 => 0
    | 3 => 6
    | 4 => 10
    | 5 => 5
    | 6 => 3
    | 7 => 7
    | 8 => 9
    | 9 => 8
    | 10 => 4

private def m11MaximalNFAction_0_7_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 1
    | 2 => 9
    | 3 => 6
    | 4 => 7
    | 5 => 10
    | 6 => 3
    | 7 => 2
    | 8 => 4
    | 9 => 0
    | 10 => 8

private def m11MaximalNFAction_0_7_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 1
    | 2 => 9
    | 3 => 3
    | 4 => 5
    | 5 => 0
    | 6 => 6
    | 7 => 4
    | 8 => 2
    | 9 => 10
    | 10 => 8

private def m11MaximalNFAction_1_0_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 3
    | 2 => 7
    | 3 => 6
    | 4 => 10
    | 5 => 4
    | 6 => 1
    | 7 => 0
    | 8 => 8
    | 9 => 9
    | 10 => 5

private def m11MaximalNFAction_1_0_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 3
    | 2 => 7
    | 3 => 1
    | 4 => 2
    | 5 => 9
    | 6 => 6
    | 7 => 8
    | 8 => 0
    | 9 => 4
    | 10 => 5

private def m11MaximalNFAction_1_1_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 3
    | 2 => 0
    | 3 => 1
    | 4 => 8
    | 5 => 2
    | 6 => 6
    | 7 => 10
    | 8 => 5
    | 9 => 7
    | 10 => 4

private def m11MaximalNFAction_1_1_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 3
    | 2 => 0
    | 3 => 6
    | 4 => 9
    | 5 => 7
    | 6 => 1
    | 7 => 5
    | 8 => 10
    | 9 => 2
    | 10 => 4

private def m11MaximalNFAction_1_2_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 3
    | 2 => 10
    | 3 => 6
    | 4 => 5
    | 5 => 9
    | 6 => 1
    | 7 => 8
    | 8 => 4
    | 9 => 0
    | 10 => 2

private def m11MaximalNFAction_1_2_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 3
    | 2 => 10
    | 3 => 1
    | 4 => 7
    | 5 => 0
    | 6 => 6
    | 7 => 4
    | 8 => 8
    | 9 => 9
    | 10 => 2

private def m11MaximalNFAction_1_3_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 3
    | 2 => 8
    | 3 => 1
    | 4 => 4
    | 5 => 7
    | 6 => 6
    | 7 => 5
    | 8 => 2
    | 9 => 10
    | 10 => 9

private def m11MaximalNFAction_1_3_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 3
    | 2 => 8
    | 3 => 6
    | 4 => 0
    | 5 => 10
    | 6 => 1
    | 7 => 2
    | 8 => 5
    | 9 => 7
    | 10 => 9

private def m11MaximalNFAction_1_4_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 3
    | 2 => 5
    | 3 => 6
    | 4 => 2
    | 5 => 0
    | 6 => 1
    | 7 => 4
    | 8 => 9
    | 9 => 8
    | 10 => 7

private def m11MaximalNFAction_1_4_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 3
    | 2 => 5
    | 3 => 1
    | 4 => 10
    | 5 => 8
    | 6 => 6
    | 7 => 9
    | 8 => 4
    | 9 => 0
    | 10 => 7

private def m11MaximalNFAction_1_5_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 3
    | 2 => 4
    | 3 => 1
    | 4 => 9
    | 5 => 10
    | 6 => 6
    | 7 => 2
    | 8 => 7
    | 9 => 5
    | 10 => 0

private def m11MaximalNFAction_1_5_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 3
    | 2 => 4
    | 3 => 6
    | 4 => 8
    | 5 => 5
    | 6 => 1
    | 7 => 7
    | 8 => 2
    | 9 => 10
    | 10 => 0

private def m11MaximalNFAction_1_6_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 3
    | 2 => 2
    | 3 => 6
    | 4 => 7
    | 5 => 8
    | 6 => 1
    | 7 => 9
    | 8 => 0
    | 9 => 4
    | 10 => 10

private def m11MaximalNFAction_1_6_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 3
    | 2 => 2
    | 3 => 1
    | 4 => 5
    | 5 => 4
    | 6 => 6
    | 7 => 0
    | 8 => 9
    | 9 => 8
    | 10 => 10

private def m11MaximalNFAction_1_7_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 3
    | 2 => 9
    | 3 => 1
    | 4 => 0
    | 5 => 5
    | 6 => 6
    | 7 => 7
    | 8 => 10
    | 9 => 2
    | 10 => 8

private def m11MaximalNFAction_1_7_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 3
    | 2 => 9
    | 3 => 6
    | 4 => 4
    | 5 => 2
    | 6 => 1
    | 7 => 10
    | 8 => 7
    | 9 => 5
    | 10 => 8

private def m11MaximalNFAction_2_0_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 6
    | 2 => 0
    | 3 => 1
    | 4 => 5
    | 5 => 10
    | 6 => 3
    | 7 => 2
    | 8 => 8
    | 9 => 9
    | 10 => 4

private def m11MaximalNFAction_2_0_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 6
    | 2 => 0
    | 3 => 3
    | 4 => 7
    | 5 => 9
    | 6 => 1
    | 7 => 8
    | 8 => 2
    | 9 => 10
    | 10 => 4

private def m11MaximalNFAction_2_1_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 6
    | 2 => 2
    | 3 => 3
    | 4 => 8
    | 5 => 7
    | 6 => 1
    | 7 => 5
    | 8 => 4
    | 9 => 0
    | 10 => 10

private def m11MaximalNFAction_2_1_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 6
    | 2 => 2
    | 3 => 1
    | 4 => 9
    | 5 => 0
    | 6 => 3
    | 7 => 4
    | 8 => 5
    | 9 => 7
    | 10 => 10

private def m11MaximalNFAction_2_2_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 6
    | 2 => 5
    | 3 => 1
    | 4 => 4
    | 5 => 9
    | 6 => 3
    | 7 => 8
    | 8 => 10
    | 9 => 2
    | 10 => 7

private def m11MaximalNFAction_2_2_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 6
    | 2 => 5
    | 3 => 3
    | 4 => 0
    | 5 => 2
    | 6 => 1
    | 7 => 10
    | 8 => 8
    | 9 => 9
    | 10 => 7

private def m11MaximalNFAction_2_3_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 6
    | 2 => 8
    | 3 => 3
    | 4 => 10
    | 5 => 0
    | 6 => 1
    | 7 => 4
    | 8 => 7
    | 9 => 5
    | 10 => 9

private def m11MaximalNFAction_2_3_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 6
    | 2 => 8
    | 3 => 1
    | 4 => 2
    | 5 => 5
    | 6 => 3
    | 7 => 7
    | 8 => 4
    | 9 => 0
    | 10 => 9

private def m11MaximalNFAction_2_4_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 5
    | 1 => 6
    | 2 => 4
    | 3 => 1
    | 4 => 7
    | 5 => 2
    | 6 => 3
    | 7 => 10
    | 8 => 9
    | 9 => 8
    | 10 => 0

private def m11MaximalNFAction_2_4_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 7
    | 1 => 6
    | 2 => 4
    | 3 => 3
    | 4 => 5
    | 5 => 8
    | 6 => 1
    | 7 => 9
    | 8 => 10
    | 9 => 2
    | 10 => 0

private def m11MaximalNFAction_2_5_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 8
    | 1 => 6
    | 2 => 10
    | 3 => 3
    | 4 => 9
    | 5 => 5
    | 6 => 1
    | 7 => 7
    | 8 => 0
    | 9 => 4
    | 10 => 2

private def m11MaximalNFAction_2_5_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 9
    | 1 => 6
    | 2 => 10
    | 3 => 1
    | 4 => 8
    | 5 => 4
    | 6 => 3
    | 7 => 0
    | 8 => 7
    | 9 => 5
    | 10 => 2

private def m11MaximalNFAction_2_6_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 4
    | 1 => 6
    | 2 => 7
    | 3 => 1
    | 4 => 0
    | 5 => 8
    | 6 => 3
    | 7 => 9
    | 8 => 2
    | 9 => 10
    | 10 => 5

private def m11MaximalNFAction_2_6_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 0
    | 1 => 6
    | 2 => 7
    | 3 => 3
    | 4 => 4
    | 5 => 10
    | 6 => 1
    | 7 => 2
    | 8 => 9
    | 9 => 8
    | 10 => 5

private def m11MaximalNFAction_2_7_0 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 10
    | 1 => 6
    | 2 => 9
    | 3 => 3
    | 4 => 2
    | 5 => 4
    | 6 => 1
    | 7 => 0
    | 8 => 5
    | 9 => 7
    | 10 => 8

private def m11MaximalNFAction_2_7_1 : Fin 11 → Fin 11 :=
  fun x =>
    match x with
    | 0 => 2
    | 1 => 6
    | 2 => 9
    | 3 => 1
    | 4 => 10
    | 5 => 7
    | 6 => 3
    | 7 => 5
    | 8 => 0
    | 9 => 4
    | 10 => 8

private def m11MaximalNFAction :
    Fin 3 → Fin 8 → Fin 2 → Fin 11 → Fin 11 :=
  fun i j k x =>
    match (i, j, k) with
    | (0, 0, 0) => m11MaximalNFAction_0_0_0 x
    | (0, 0, 1) => m11MaximalNFAction_0_0_1 x
    | (0, 1, 0) => m11MaximalNFAction_0_1_0 x
    | (0, 1, 1) => m11MaximalNFAction_0_1_1 x
    | (0, 2, 0) => m11MaximalNFAction_0_2_0 x
    | (0, 2, 1) => m11MaximalNFAction_0_2_1 x
    | (0, 3, 0) => m11MaximalNFAction_0_3_0 x
    | (0, 3, 1) => m11MaximalNFAction_0_3_1 x
    | (0, 4, 0) => m11MaximalNFAction_0_4_0 x
    | (0, 4, 1) => m11MaximalNFAction_0_4_1 x
    | (0, 5, 0) => m11MaximalNFAction_0_5_0 x
    | (0, 5, 1) => m11MaximalNFAction_0_5_1 x
    | (0, 6, 0) => m11MaximalNFAction_0_6_0 x
    | (0, 6, 1) => m11MaximalNFAction_0_6_1 x
    | (0, 7, 0) => m11MaximalNFAction_0_7_0 x
    | (0, 7, 1) => m11MaximalNFAction_0_7_1 x
    | (1, 0, 0) => m11MaximalNFAction_1_0_0 x
    | (1, 0, 1) => m11MaximalNFAction_1_0_1 x
    | (1, 1, 0) => m11MaximalNFAction_1_1_0 x
    | (1, 1, 1) => m11MaximalNFAction_1_1_1 x
    | (1, 2, 0) => m11MaximalNFAction_1_2_0 x
    | (1, 2, 1) => m11MaximalNFAction_1_2_1 x
    | (1, 3, 0) => m11MaximalNFAction_1_3_0 x
    | (1, 3, 1) => m11MaximalNFAction_1_3_1 x
    | (1, 4, 0) => m11MaximalNFAction_1_4_0 x
    | (1, 4, 1) => m11MaximalNFAction_1_4_1 x
    | (1, 5, 0) => m11MaximalNFAction_1_5_0 x
    | (1, 5, 1) => m11MaximalNFAction_1_5_1 x
    | (1, 6, 0) => m11MaximalNFAction_1_6_0 x
    | (1, 6, 1) => m11MaximalNFAction_1_6_1 x
    | (1, 7, 0) => m11MaximalNFAction_1_7_0 x
    | (1, 7, 1) => m11MaximalNFAction_1_7_1 x
    | (2, 0, 0) => m11MaximalNFAction_2_0_0 x
    | (2, 0, 1) => m11MaximalNFAction_2_0_1 x
    | (2, 1, 0) => m11MaximalNFAction_2_1_0 x
    | (2, 1, 1) => m11MaximalNFAction_2_1_1 x
    | (2, 2, 0) => m11MaximalNFAction_2_2_0 x
    | (2, 2, 1) => m11MaximalNFAction_2_2_1 x
    | (2, 3, 0) => m11MaximalNFAction_2_3_0 x
    | (2, 3, 1) => m11MaximalNFAction_2_3_1 x
    | (2, 4, 0) => m11MaximalNFAction_2_4_0 x
    | (2, 4, 1) => m11MaximalNFAction_2_4_1 x
    | (2, 5, 0) => m11MaximalNFAction_2_5_0 x
    | (2, 5, 1) => m11MaximalNFAction_2_5_1 x
    | (2, 6, 0) => m11MaximalNFAction_2_6_0 x
    | (2, 6, 1) => m11MaximalNFAction_2_6_1 x
    | (2, 7, 0) => m11MaximalNFAction_2_7_0 x
    | (2, 7, 1) => m11MaximalNFAction_2_7_1 x
    | (_, _, _) => 0

private theorem m11MaximalUPerm_apply_table (x : Fin 11) :
    m11MaximalUPerm x = m11MaximalNFAction_0_1_0 x := by
  fin_cases x <;>
    simp [m11MaximalUPerm, m11MaximalNFAction_0_1_0, Equiv.swap_apply_def]

private theorem m11MaximalVPerm_apply_table (x : Fin 11) :
    m11MaximalVPerm x = m11MaximalNFAction_1_0_0 x := by
  fin_cases x <;>
    simp [m11MaximalVPerm, m11MaximalNFAction_1_0_0, Equiv.swap_apply_def]

private theorem m11MaximalWPerm_apply_table (x : Fin 11) :
    m11MaximalWPerm x = m11MaximalNFAction_0_0_1 x := by
  fin_cases x <;>
    simp [m11MaximalWPerm, m11MaximalNFAction_0_0_1, Equiv.swap_apply_def]
private theorem m11MaximalNFPerm_apply_0_0_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (0 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      m11MaximalNFAction,
      m11MaximalNFAction_0_0_0]

private theorem m11MaximalNFPerm_apply_0_0_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (0 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_1_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (1 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_1_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (1 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_1_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_2_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (2 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_2_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_2_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (2 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_2_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_3_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (3 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_3_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_3_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (3 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_3_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_4_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (4 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_4_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_4_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (4 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_4_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_5_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (5 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_5_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_5_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (5 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_5_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_6_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (6 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_6_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_6_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (6 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_6_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_0_7_0 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (7 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_7_0,
      m11MaximalNFAction_0_1_0]

private theorem m11MaximalNFPerm_apply_0_7_1 (x : Fin 11) :
    m11MaximalNFPerm ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (0 : Fin 3) (7 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_0_7_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_0_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (0 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_0_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (0 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_0_1,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_1_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (1 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_1_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_1_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (1 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_1_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_2_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (2 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_2_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_2_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (2 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_2_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_3_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (3 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_3_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_3_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (3 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_3_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_4_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (4 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_4_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_4_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (4 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_4_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_5_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (5 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_5_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_5_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (5 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_5_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_6_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (6 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_6_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_6_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (6 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_6_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_1_7_0 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (7 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_7_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_1_7_1 (x : Fin 11) :
    m11MaximalNFPerm ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (1 : Fin 3) (7 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_1_7_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_0_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (0 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_0_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_0_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (0 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_0_1,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_1_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (1 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_1_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_1_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (1 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_1_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_2_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (2 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_2_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_2_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (2 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_2_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_3_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (3 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_3_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_3_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (3 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_3_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_4_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (4 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_4_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_4_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (4 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_4_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_5_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (5 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_5_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_5_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (5 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_5_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_6_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (6 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_6_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_6_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (6 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_6_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]

private theorem m11MaximalNFPerm_apply_2_7_0 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (7 : Fin 8) (0 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_7_0,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0]

private theorem m11MaximalNFPerm_apply_2_7_1 (x : Fin 11) :
    m11MaximalNFPerm ((2 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) x =
      m11MaximalNFAction (2 : Fin 3) (7 : Fin 8) (1 : Fin 2) x := by
  fin_cases x <;>
    simp [m11MaximalNFPerm,
      pow_succ,
      m11MaximalUPerm_apply_table,
      m11MaximalVPerm_apply_table,
      m11MaximalWPerm_apply_table,
      m11MaximalNFAction,
      m11MaximalNFAction_2_7_1,
      m11MaximalNFAction_0_1_0,
      m11MaximalNFAction_1_0_0,
      m11MaximalNFAction_0_0_1]


private theorem m11MaximalNFPerm_apply :
    ∀ i j k x, m11MaximalNFPerm (i, (j, k)) x =
      m11MaximalNFAction i j k x := by
  intro i j k x
  fin_cases i <;> fin_cases j <;> fin_cases k
  · simpa using (m11MaximalNFPerm_apply_0_0_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_0_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_1_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_1_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_2_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_2_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_3_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_3_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_4_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_4_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_5_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_5_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_6_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_6_1 x)
  · simpa using (m11MaximalNFPerm_apply_0_7_0 x)
  · simpa using (m11MaximalNFPerm_apply_0_7_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_0_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_0_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_1_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_1_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_2_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_2_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_3_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_3_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_4_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_4_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_5_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_5_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_6_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_6_1 x)
  · simpa using (m11MaximalNFPerm_apply_1_7_0 x)
  · simpa using (m11MaximalNFPerm_apply_1_7_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_0_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_0_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_1_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_1_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_2_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_2_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_3_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_3_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_4_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_4_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_5_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_5_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_6_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_6_1 x)
  · simpa using (m11MaximalNFPerm_apply_2_7_0 x)
  · simpa using (m11MaximalNFPerm_apply_2_7_1 x)

private theorem m11MaximalNFPerm_eq_0_0_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_0_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_0_0 x)

private theorem m11MaximalNFPerm_eq_0_0_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_0_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_0_1 x)

private theorem m11MaximalNFPerm_eq_0_1_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_1_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_1_0 x)

private theorem m11MaximalNFPerm_eq_0_1_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_1_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_1_1 x)

private theorem m11MaximalNFPerm_eq_0_2_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_2_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_2_0 x)

private theorem m11MaximalNFPerm_eq_0_2_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_2_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_2_1 x)

private theorem m11MaximalNFPerm_eq_0_3_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_3_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_3_0 x)

private theorem m11MaximalNFPerm_eq_0_3_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_3_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_3_1 x)

private theorem m11MaximalNFPerm_eq_0_4_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_4_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_4_0 x)

private theorem m11MaximalNFPerm_eq_0_4_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_4_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_4_1 x)

private theorem m11MaximalNFPerm_eq_0_5_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_5_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_5_0 x)

private theorem m11MaximalNFPerm_eq_0_5_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_5_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_5_1 x)

private theorem m11MaximalNFPerm_eq_0_6_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_6_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_6_0 x)

private theorem m11MaximalNFPerm_eq_0_6_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_6_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_6_1 x)

private theorem m11MaximalNFPerm_eq_0_7_0 :
    m11MaximalNFPerm ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_0_7_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_7_0 x)

private theorem m11MaximalNFPerm_eq_0_7_1 :
    m11MaximalNFPerm ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_0_7_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_0_7_1 x)

private theorem m11MaximalNFPerm_eq_1_0_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_0_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_0_0 x)

private theorem m11MaximalNFPerm_eq_1_0_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_0_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_0_1 x)

private theorem m11MaximalNFPerm_eq_1_1_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_1_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_1_0 x)

private theorem m11MaximalNFPerm_eq_1_1_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_1_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_1_1 x)

private theorem m11MaximalNFPerm_eq_1_2_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_2_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_2_0 x)

private theorem m11MaximalNFPerm_eq_1_2_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_2_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_2_1 x)

private theorem m11MaximalNFPerm_eq_1_3_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_3_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_3_0 x)

private theorem m11MaximalNFPerm_eq_1_3_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_3_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_3_1 x)

private theorem m11MaximalNFPerm_eq_1_4_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_4_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_4_0 x)

private theorem m11MaximalNFPerm_eq_1_4_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_4_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_4_1 x)

private theorem m11MaximalNFPerm_eq_1_5_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_5_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_5_0 x)

private theorem m11MaximalNFPerm_eq_1_5_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_5_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_5_1 x)

private theorem m11MaximalNFPerm_eq_1_6_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_6_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_6_0 x)

private theorem m11MaximalNFPerm_eq_1_6_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_6_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_6_1 x)

private theorem m11MaximalNFPerm_eq_1_7_0 :
    m11MaximalNFPerm ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_1_7_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_7_0 x)

private theorem m11MaximalNFPerm_eq_1_7_1 :
    m11MaximalNFPerm ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_1_7_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_1_7_1 x)

private theorem m11MaximalNFPerm_eq_2_0_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_0_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_0_0 x)

private theorem m11MaximalNFPerm_eq_2_0_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_0_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_0_1 x)

private theorem m11MaximalNFPerm_eq_2_1_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_1_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_1_0 x)

private theorem m11MaximalNFPerm_eq_2_1_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((1 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_1_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_1_1 x)

private theorem m11MaximalNFPerm_eq_2_2_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_2_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_2_0 x)

private theorem m11MaximalNFPerm_eq_2_2_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_2_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_2_1 x)

private theorem m11MaximalNFPerm_eq_2_3_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_3_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_3_0 x)

private theorem m11MaximalNFPerm_eq_2_3_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_3_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_3_1 x)

private theorem m11MaximalNFPerm_eq_2_4_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((4 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_4_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_4_0 x)

private theorem m11MaximalNFPerm_eq_2_4_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((4 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_4_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_4_1 x)

private theorem m11MaximalNFPerm_eq_2_5_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_5_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_5_0 x)

private theorem m11MaximalNFPerm_eq_2_5_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((5 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_5_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_5_1 x)

private theorem m11MaximalNFPerm_eq_2_6_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((6 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_6_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_6_0 x)

private theorem m11MaximalNFPerm_eq_2_6_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((6 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_6_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_6_1 x)

private theorem m11MaximalNFPerm_eq_2_7_0 :
    m11MaximalNFPerm ((2 : Fin 3), ((7 : Fin 8), (0 : Fin 2))) =
      m11MaximalNFAction_2_7_0 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_7_0 x)

private theorem m11MaximalNFPerm_eq_2_7_1 :
    m11MaximalNFPerm ((2 : Fin 3), ((7 : Fin 8), (1 : Fin 2))) =
      m11MaximalNFAction_2_7_1 := by
  funext x
  simpa [m11MaximalNFAction] using (m11MaximalNFPerm_apply_2_7_1 x)

private theorem m11MaximalNF_perm
    (p : Fin 3 × Fin 8 × Fin 2) :
    ((m11MaximalNF p : M11) : Equiv.Perm (Fin 11)) =
      m11MaximalNFPerm p := by
  simp [m11MaximalNF, m11MaximalNFPerm, m11MaximalUPerm,
    m11MaximalVPerm, m11MaximalWPerm, m11CentralizerU_perm,
    m11CentralizerV_perm, m11CentralizerW_perm]

private def m11MaximalWitness : Fin 11 → Fin 11 → Fin 11 → Fin 8 × (Fin 3 × Fin 8 × Fin 2) := fun x y z =>
match x, y, z with
  | 0, 1, 2 => (3, (0, 0, 0))
  | 0, 1, 3 => (4, (0, 2, 0))
  | 0, 1, 4 => (2, (1, 1, 0))
  | 0, 1, 5 => (7, (1, 3, 1))
  | 0, 1, 6 => (4, (0, 6, 1))
  | 0, 1, 7 => (7, (1, 4, 0))
  | 0, 1, 8 => (7, (1, 7, 0))
  | 0, 1, 9 => (7, (1, 0, 1))
  | 0, 1, 10 => (3, (0, 2, 0))
  | 0, 2, 3 => (7, (0, 4, 0))
  | 0, 2, 4 => (5, (1, 5, 0))
  | 0, 2, 5 => (6, (0, 3, 1))
  | 0, 2, 6 => (7, (0, 2, 1))
  | 0, 2, 7 => (1, (0, 0, 0))
  | 0, 2, 8 => (6, (1, 3, 1))
  | 0, 2, 9 => (6, (1, 5, 0))
  | 0, 2, 10 => (5, (1, 3, 1))
  | 0, 3, 4 => (2, (0, 1, 1))
  | 0, 3, 5 => (7, (2, 7, 0))
  | 0, 3, 6 => (4, (2, 3, 0))
  | 0, 3, 7 => (7, (2, 2, 1))
  | 0, 3, 8 => (3, (1, 3, 0))
  | 0, 3, 9 => (3, (1, 4, 1))
  | 0, 3, 10 => (7, (0, 6, 0))
  | 0, 4, 5 => (5, (0, 5, 0))
  | 0, 4, 6 => (2, (0, 1, 0))
  | 0, 4, 7 => (5, (0, 1, 0))
  | 0, 4, 8 => (5, (0, 1, 1))
  | 0, 4, 9 => (5, (0, 5, 1))
  | 0, 4, 10 => (5, (1, 1, 0))
  | 0, 5, 6 => (3, (1, 7, 1))
  | 0, 5, 7 => (5, (0, 0, 1))
  | 0, 5, 8 => (1, (0, 3, 0))
  | 0, 5, 9 => (6, (1, 6, 0))
  | 0, 5, 10 => (6, (1, 7, 0))
  | 0, 6, 7 => (3, (1, 0, 0))
  | 0, 6, 8 => (7, (2, 3, 1))
  | 0, 6, 9 => (7, (2, 6, 0))
  | 0, 6, 10 => (7, (0, 0, 1))
  | 0, 7, 8 => (6, (1, 2, 1))
  | 0, 7, 9 => (6, (0, 0, 1))
  | 0, 7, 10 => (6, (1, 1, 1))
  | 0, 8, 9 => (5, (0, 4, 0))
  | 0, 8, 10 => (6, (0, 1, 1))
  | 0, 9, 10 => (1, (0, 2, 0))
  | 1, 2, 3 => (4, (0, 0, 0))
  | 1, 2, 4 => (3, (0, 0, 1))
  | 1, 2, 5 => (7, (1, 5, 0))
  | 1, 2, 6 => (4, (0, 0, 1))
  | 1, 2, 7 => (7, (1, 2, 1))
  | 1, 2, 8 => (7, (1, 2, 0))
  | 1, 2, 9 => (7, (1, 5, 1))
  | 1, 2, 10 => (2, (1, 3, 0))
  | 1, 3, 4 => (4, (0, 6, 0))
  | 1, 3, 5 => (4, (0, 1, 1))
  | 1, 3, 6 => (0, (0, 0, 0))
  | 1, 3, 7 => (4, (0, 5, 1))
  | 1, 3, 8 => (4, (0, 7, 1))
  | 1, 3, 9 => (4, (0, 3, 1))
  | 1, 3, 10 => (4, (0, 4, 0))
  | 1, 4, 5 => (7, (1, 0, 0))
  | 1, 4, 6 => (4, (0, 2, 1))
  | 1, 4, 7 => (7, (1, 7, 1))
  | 1, 4, 8 => (7, (1, 4, 1))
  | 1, 4, 9 => (7, (1, 3, 0))
  | 1, 4, 10 => (3, (0, 2, 1))
  | 1, 5, 6 => (4, (0, 3, 0))
  | 1, 5, 7 => (2, (1, 0, 1))
  | 1, 5, 8 => (3, (0, 3, 0))
  | 1, 5, 9 => (3, (0, 1, 0))
  | 1, 5, 10 => (7, (1, 6, 1))
  | 1, 6, 7 => (4, (0, 7, 0))
  | 1, 6, 8 => (4, (0, 5, 0))
  | 1, 6, 9 => (4, (0, 1, 0))
  | 1, 6, 10 => (4, (0, 4, 1))
  | 1, 7, 8 => (3, (0, 5, 0))
  | 1, 7, 9 => (3, (0, 3, 1))
  | 1, 7, 10 => (7, (1, 1, 0))
  | 1, 8, 9 => (2, (1, 0, 0))
  | 1, 8, 10 => (7, (1, 1, 1))
  | 1, 9, 10 => (7, (1, 6, 0))
  | 2, 3, 4 => (7, (0, 2, 0))
  | 2, 3, 5 => (3, (1, 1, 0))
  | 2, 3, 6 => (4, (2, 1, 0))
  | 2, 3, 7 => (3, (1, 6, 1))
  | 2, 3, 8 => (7, (2, 4, 1))
  | 2, 3, 9 => (7, (2, 5, 0))
  | 2, 3, 10 => (2, (0, 3, 1))
  | 2, 4, 5 => (6, (1, 5, 1))
  | 2, 4, 6 => (7, (0, 4, 1))
  | 2, 4, 7 => (6, (1, 3, 0))
  | 2, 4, 8 => (1, (0, 0, 1))
  | 2, 4, 9 => (6, (0, 3, 0))
  | 2, 4, 10 => (5, (1, 3, 0))
  | 2, 5, 6 => (7, (2, 5, 1))
  | 2, 5, 7 => (5, (0, 2, 0))
  | 2, 5, 8 => (6, (1, 4, 1))
  | 2, 5, 9 => (1, (0, 1, 0))
  | 2, 5, 10 => (5, (0, 3, 1))
  | 2, 6, 7 => (7, (2, 4, 0))
  | 2, 6, 8 => (3, (1, 6, 0))
  | 2, 6, 9 => (3, (1, 1, 1))
  | 2, 6, 10 => (2, (0, 3, 0))
  | 2, 7, 8 => (6, (0, 2, 0))
  | 2, 7, 9 => (6, (1, 4, 0))
  | 2, 7, 10 => (5, (0, 7, 1))
  | 2, 8, 9 => (5, (0, 2, 1))
  | 2, 8, 10 => (5, (0, 7, 0))
  | 2, 9, 10 => (5, (0, 3, 0))
  | 3, 4, 5 => (7, (2, 6, 1))
  | 3, 4, 6 => (4, (2, 3, 1))
  | 3, 4, 7 => (7, (2, 3, 0))
  | 3, 4, 8 => (3, (1, 0, 1))
  | 3, 4, 9 => (3, (1, 7, 0))
  | 3, 4, 10 => (7, (0, 0, 0))
  | 3, 5, 6 => (4, (2, 2, 1))
  | 3, 5, 7 => (2, (0, 2, 0))
  | 3, 5, 8 => (7, (0, 3, 1))
  | 3, 5, 9 => (7, (0, 5, 1))
  | 3, 5, 10 => (3, (1, 2, 1))
  | 3, 6, 7 => (4, (2, 0, 0))
  | 3, 6, 8 => (4, (2, 0, 1))
  | 3, 6, 9 => (4, (2, 2, 0))
  | 3, 6, 10 => (4, (2, 5, 0))
  | 3, 7, 8 => (7, (0, 1, 1))
  | 3, 7, 9 => (7, (0, 7, 1))
  | 3, 7, 10 => (3, (1, 5, 0))
  | 3, 8, 9 => (2, (0, 0, 0))
  | 3, 8, 10 => (7, (2, 1, 0))
  | 3, 9, 10 => (7, (2, 0, 1))
  | 4, 5, 6 => (3, (1, 4, 0))
  | 4, 5, 7 => (5, (0, 4, 1))
  | 4, 5, 8 => (6, (0, 0, 0))
  | 4, 5, 9 => (6, (1, 6, 1))
  | 4, 5, 10 => (1, (0, 2, 1))
  | 4, 6, 7 => (3, (1, 3, 1))
  | 4, 6, 8 => (7, (2, 2, 0))
  | 4, 6, 9 => (7, (2, 7, 1))
  | 4, 6, 10 => (7, (0, 6, 1))
  | 4, 7, 8 => (6, (1, 2, 0))
  | 4, 7, 9 => (1, (0, 3, 1))
  | 4, 7, 10 => (6, (0, 1, 0))
  | 4, 8, 9 => (5, (0, 0, 0))
  | 4, 8, 10 => (6, (1, 1, 0))
  | 4, 9, 10 => (6, (1, 7, 1))
  | 5, 6, 7 => (2, (0, 0, 1))
  | 5, 6, 8 => (7, (0, 7, 0))
  | 5, 6, 9 => (7, (0, 5, 0))
  | 5, 6, 10 => (7, (2, 0, 0))
  | 5, 7, 8 => (5, (1, 2, 0))
  | 5, 7, 9 => (5, (1, 0, 1))
  | 5, 7, 10 => (5, (0, 6, 0))
  | 5, 8, 9 => (5, (1, 0, 0))
  | 5, 8, 10 => (6, (1, 0, 0))
  | 5, 9, 10 => (6, (0, 6, 0))
  | 6, 7, 8 => (7, (0, 1, 0))
  | 6, 7, 9 => (7, (0, 3, 0))
  | 6, 7, 10 => (7, (2, 1, 1))
  | 6, 8, 9 => (2, (0, 2, 1))
  | 6, 8, 10 => (3, (1, 5, 1))
  | 6, 9, 10 => (3, (1, 2, 0))
  | 7, 8, 9 => (5, (1, 2, 1))
  | 7, 8, 10 => (1, (0, 5, 0))
  | 7, 9, 10 => (6, (1, 0, 1))
  | 8, 9, 10 => (5, (0, 6, 1))
  | _, _, _ => (0, (0, 0, 0))

private theorem m11MaximalCase_0_1_2 :
    ({(0 : Fin 11), (1 : Fin 11), (2 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_0_1_3 :
    ({(0 : Fin 11), (1 : Fin 11), (3 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_0_1_4 :
    ({(0 : Fin 11), (1 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_0, m11MaximalRep]

private theorem m11MaximalCase_0_1_5 :
    ({(0 : Fin 11), (1 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_1, m11MaximalRep]

private theorem m11MaximalCase_0_1_6 :
    ({(0 : Fin 11), (1 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_1, m11MaximalRep]

private theorem m11MaximalCase_0_1_7 :
    ({(0 : Fin 11), (1 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_0, m11MaximalRep]

private theorem m11MaximalCase_0_1_8 :
    ({(0 : Fin 11), (1 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_0, m11MaximalRep]

private theorem m11MaximalCase_0_1_9 :
    ({(0 : Fin 11), (1 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_1, m11MaximalRep]

private theorem m11MaximalCase_0_1_10 :
    ({(0 : Fin 11), (1 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_0_2_3 :
    ({(0 : Fin 11), (2 : Fin 11), (3 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_0, m11MaximalRep]

private theorem m11MaximalCase_0_2_4 :
    ({(0 : Fin 11), (2 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_0, m11MaximalRep]

private theorem m11MaximalCase_0_2_5 :
    ({(0 : Fin 11), (2 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_0_2_6 :
    ({(0 : Fin 11), (2 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_0_2_7 :
    ({(0 : Fin 11), (2 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_0_2_8 :
    ({(0 : Fin 11), (2 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_1, m11MaximalRep]

private theorem m11MaximalCase_0_2_9 :
    ({(0 : Fin 11), (2 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_0, m11MaximalRep]

private theorem m11MaximalCase_0_2_10 :
    ({(0 : Fin 11), (2 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_1, m11MaximalRep]

private theorem m11MaximalCase_0_3_4 :
    ({(0 : Fin 11), (3 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_1, m11MaximalRep]

private theorem m11MaximalCase_0_3_5 :
    ({(0 : Fin 11), (3 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_7_0, m11MaximalRep]

private theorem m11MaximalCase_0_3_6 :
    ({(0 : Fin 11), (3 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_3_0, m11MaximalRep]

private theorem m11MaximalCase_0_3_7 :
    ({(0 : Fin 11), (3 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_2_1, m11MaximalRep]

private theorem m11MaximalCase_0_3_8 :
    ({(0 : Fin 11), (3 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_0, m11MaximalRep]

private theorem m11MaximalCase_0_3_9 :
    ({(0 : Fin 11), (3 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_1, m11MaximalRep]

private theorem m11MaximalCase_0_3_10 :
    ({(0 : Fin 11), (3 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_0, m11MaximalRep]

private theorem m11MaximalCase_0_4_5 :
    ({(0 : Fin 11), (4 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_0, m11MaximalRep]

private theorem m11MaximalCase_0_4_6 :
    ({(0 : Fin 11), (4 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_0_4_7 :
    ({(0 : Fin 11), (4 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_0_4_8 :
    ({(0 : Fin 11), (4 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_1, m11MaximalRep]

private theorem m11MaximalCase_0_4_9 :
    ({(0 : Fin 11), (4 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_1, m11MaximalRep]

private theorem m11MaximalCase_0_4_10 :
    ({(0 : Fin 11), (4 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_0, m11MaximalRep]

private theorem m11MaximalCase_0_5_6 :
    ({(0 : Fin 11), (5 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_1, m11MaximalRep]

private theorem m11MaximalCase_0_5_7 :
    ({(0 : Fin 11), (5 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_0_5_8 :
    ({(0 : Fin 11), (5 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_0_5_9 :
    ({(0 : Fin 11), (5 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_0, m11MaximalRep]

private theorem m11MaximalCase_0_5_10 :
    ({(0 : Fin 11), (5 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_0, m11MaximalRep]

private theorem m11MaximalCase_0_6_7 :
    ({(0 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_0, m11MaximalRep]

private theorem m11MaximalCase_0_6_8 :
    ({(0 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_3_1, m11MaximalRep]

private theorem m11MaximalCase_0_6_9 :
    ({(0 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_6_0, m11MaximalRep]

private theorem m11MaximalCase_0_6_10 :
    ({(0 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_0_7_8 :
    ({(0 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_1, m11MaximalRep]

private theorem m11MaximalCase_0_7_9 :
    ({(0 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_0_7_10 :
    ({(0 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_1, m11MaximalRep]

private theorem m11MaximalCase_0_8_9 :
    ({(0 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_0, m11MaximalRep]

private theorem m11MaximalCase_0_8_10 :
    ({(0 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_1, m11MaximalRep]

private theorem m11MaximalCase_0_9_10 :
    ({(0 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_1_2_3 :
    ({(1 : Fin 11), (2 : Fin 11), (3 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_1_2_4 :
    ({(1 : Fin 11), (2 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_1_2_5 :
    ({(1 : Fin 11), (2 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_0, m11MaximalRep]

private theorem m11MaximalCase_1_2_6 :
    ({(1 : Fin 11), (2 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_1_2_7 :
    ({(1 : Fin 11), (2 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_1, m11MaximalRep]

private theorem m11MaximalCase_1_2_8 :
    ({(1 : Fin 11), (2 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_0, m11MaximalRep]

private theorem m11MaximalCase_1_2_9 :
    ({(1 : Fin 11), (2 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_1, m11MaximalRep]

private theorem m11MaximalCase_1_2_10 :
    ({(1 : Fin 11), (2 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_0, m11MaximalRep]

private theorem m11MaximalCase_1_3_4 :
    ({(1 : Fin 11), (3 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_0, m11MaximalRep]

private theorem m11MaximalCase_1_3_5 :
    ({(1 : Fin 11), (3 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_1, m11MaximalRep]

private theorem m11MaximalCase_1_3_6 :
    ({(1 : Fin 11), (3 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((0, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((0, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_1_3_7 :
    ({(1 : Fin 11), (3 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_1, m11MaximalRep]

private theorem m11MaximalCase_1_3_8 :
    ({(1 : Fin 11), (3 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_1, m11MaximalRep]

private theorem m11MaximalCase_1_3_9 :
    ({(1 : Fin 11), (3 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_1_3_10 :
    ({(1 : Fin 11), (3 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_0, m11MaximalRep]

private theorem m11MaximalCase_1_4_5 :
    ({(1 : Fin 11), (4 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_0, m11MaximalRep]

private theorem m11MaximalCase_1_4_6 :
    ({(1 : Fin 11), (4 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_1_4_7 :
    ({(1 : Fin 11), (4 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_1, m11MaximalRep]

private theorem m11MaximalCase_1_4_8 :
    ({(1 : Fin 11), (4 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_1, m11MaximalRep]

private theorem m11MaximalCase_1_4_9 :
    ({(1 : Fin 11), (4 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_0, m11MaximalRep]

private theorem m11MaximalCase_1_4_10 :
    ({(1 : Fin 11), (4 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_1_5_6 :
    ({(1 : Fin 11), (5 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_1_5_7 :
    ({(1 : Fin 11), (5 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_1, m11MaximalRep]

private theorem m11MaximalCase_1_5_8 :
    ({(1 : Fin 11), (5 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_1_5_9 :
    ({(1 : Fin 11), (5 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_1_5_10 :
    ({(1 : Fin 11), (5 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_1, m11MaximalRep]

private theorem m11MaximalCase_1_6_7 :
    ({(1 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_0, m11MaximalRep]

private theorem m11MaximalCase_1_6_8 :
    ({(1 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_0, m11MaximalRep]

private theorem m11MaximalCase_1_6_9 :
    ({(1 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_1_6_10 :
    ({(1 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_1, m11MaximalRep]

private theorem m11MaximalCase_1_7_8 :
    ({(1 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_0, m11MaximalRep]

private theorem m11MaximalCase_1_7_9 :
    ({(1 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_1_7_10 :
    ({(1 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_0, m11MaximalRep]

private theorem m11MaximalCase_1_8_9 :
    ({(1 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_0, m11MaximalRep]

private theorem m11MaximalCase_1_8_10 :
    ({(1 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_1, m11MaximalRep]

private theorem m11MaximalCase_1_9_10 :
    ({(1 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_0, m11MaximalRep]

private theorem m11MaximalCase_2_3_4 :
    ({(2 : Fin 11), (3 : Fin 11), (4 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_2_3_5 :
    ({(2 : Fin 11), (3 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_0, m11MaximalRep]

private theorem m11MaximalCase_2_3_6 :
    ({(2 : Fin 11), (3 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_1_0, m11MaximalRep]

private theorem m11MaximalCase_2_3_7 :
    ({(2 : Fin 11), (3 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_1, m11MaximalRep]

private theorem m11MaximalCase_2_3_8 :
    ({(2 : Fin 11), (3 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_4_1, m11MaximalRep]

private theorem m11MaximalCase_2_3_9 :
    ({(2 : Fin 11), (3 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_5_0, m11MaximalRep]

private theorem m11MaximalCase_2_3_10 :
    ({(2 : Fin 11), (3 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_2_4_5 :
    ({(2 : Fin 11), (4 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_1, m11MaximalRep]

private theorem m11MaximalCase_2_4_6 :
    ({(2 : Fin 11), (4 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_1, m11MaximalRep]

private theorem m11MaximalCase_2_4_7 :
    ({(2 : Fin 11), (4 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_0, m11MaximalRep]

private theorem m11MaximalCase_2_4_8 :
    ({(2 : Fin 11), (4 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_2_4_9 :
    ({(2 : Fin 11), (4 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_2_4_10 :
    ({(2 : Fin 11), (4 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_0, m11MaximalRep]

private theorem m11MaximalCase_2_5_6 :
    ({(2 : Fin 11), (5 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_5_1, m11MaximalRep]

private theorem m11MaximalCase_2_5_7 :
    ({(2 : Fin 11), (5 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_2_5_8 :
    ({(2 : Fin 11), (5 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_1, m11MaximalRep]

private theorem m11MaximalCase_2_5_9 :
    ({(2 : Fin 11), (5 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_2_5_10 :
    ({(2 : Fin 11), (5 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_2_6_7 :
    ({(2 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_4_0, m11MaximalRep]

private theorem m11MaximalCase_2_6_8 :
    ({(2 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_0, m11MaximalRep]

private theorem m11MaximalCase_2_6_9 :
    ({(2 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_1, m11MaximalRep]

private theorem m11MaximalCase_2_6_10 :
    ({(2 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_2_7_8 :
    ({(2 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_2_7_9 :
    ({(2 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_0, m11MaximalRep]

private theorem m11MaximalCase_2_7_10 :
    ({(2 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_1, m11MaximalRep]

private theorem m11MaximalCase_2_8_9 :
    ({(2 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_2_8_10 :
    ({(2 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_0, m11MaximalRep]

private theorem m11MaximalCase_2_9_10 :
    ({(2 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_3_4_5 :
    ({(3 : Fin 11), (4 : Fin 11), (5 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_6_1, m11MaximalRep]

private theorem m11MaximalCase_3_4_6 :
    ({(3 : Fin 11), (4 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_3_1, m11MaximalRep]

private theorem m11MaximalCase_3_4_7 :
    ({(3 : Fin 11), (4 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_3_0, m11MaximalRep]

private theorem m11MaximalCase_3_4_8 :
    ({(3 : Fin 11), (4 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_1, m11MaximalRep]

private theorem m11MaximalCase_3_4_9 :
    ({(3 : Fin 11), (4 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_0, m11MaximalRep]

private theorem m11MaximalCase_3_4_10 :
    ({(3 : Fin 11), (4 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_3_5_6 :
    ({(3 : Fin 11), (5 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_2_1, m11MaximalRep]

private theorem m11MaximalCase_3_5_7 :
    ({(3 : Fin 11), (5 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_0, m11MaximalRep]

private theorem m11MaximalCase_3_5_8 :
    ({(3 : Fin 11), (5 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_3_5_9 :
    ({(3 : Fin 11), (5 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_1, m11MaximalRep]

private theorem m11MaximalCase_3_5_10 :
    ({(3 : Fin 11), (5 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_1, m11MaximalRep]

private theorem m11MaximalCase_3_6_7 :
    ({(3 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_0_0, m11MaximalRep]

private theorem m11MaximalCase_3_6_8 :
    ({(3 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_0_1, m11MaximalRep]

private theorem m11MaximalCase_3_6_9 :
    ({(3 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_2_0, m11MaximalRep]

private theorem m11MaximalCase_3_6_10 :
    ({(3 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((4, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((4, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_5_0, m11MaximalRep]

private theorem m11MaximalCase_3_7_8 :
    ({(3 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_1, m11MaximalRep]

private theorem m11MaximalCase_3_7_9 :
    ({(3 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_1, m11MaximalRep]

private theorem m11MaximalCase_3_7_10 :
    ({(3 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_0, m11MaximalRep]

private theorem m11MaximalCase_3_8_9 :
    ({(3 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_3_8_10 :
    ({(3 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_1_0, m11MaximalRep]

private theorem m11MaximalCase_3_9_10 :
    ({(3 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_0_1, m11MaximalRep]

private theorem m11MaximalCase_4_5_6 :
    ({(4 : Fin 11), (5 : Fin 11), (6 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_4_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_4_0, m11MaximalRep]

private theorem m11MaximalCase_4_5_7 :
    ({(4 : Fin 11), (5 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_4_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_4_1, m11MaximalRep]

private theorem m11MaximalCase_4_5_8 :
    ({(4 : Fin 11), (5 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_4_5_9 :
    ({(4 : Fin 11), (5 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_6_1, m11MaximalRep]

private theorem m11MaximalCase_4_5_10 :
    ({(4 : Fin 11), (5 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_4_6_7 :
    ({(4 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_3_1, m11MaximalRep]

private theorem m11MaximalCase_4_6_8 :
    ({(4 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_2_0, m11MaximalRep]

private theorem m11MaximalCase_4_6_9 :
    ({(4 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_7_1, m11MaximalRep]

private theorem m11MaximalCase_4_6_10 :
    ({(4 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_1, m11MaximalRep]

private theorem m11MaximalCase_4_7_8 :
    ({(4 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_0, m11MaximalRep]

private theorem m11MaximalCase_4_7_9 :
    ({(4 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_1, m11MaximalRep]

private theorem m11MaximalCase_4_7_10 :
    ({(4 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_4_8_9 :
    ({(4 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_0, m11MaximalRep]

private theorem m11MaximalCase_4_8_10 :
    ({(4 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_1_0, m11MaximalRep]

private theorem m11MaximalCase_4_9_10 :
    ({(4 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_7_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_7_1, m11MaximalRep]

private theorem m11MaximalCase_5_6_7 :
    ({(5 : Fin 11), (6 : Fin 11), (7 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_0_1, m11MaximalRep]

private theorem m11MaximalCase_5_6_8 :
    ({(5 : Fin 11), (6 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_7_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_7_0, m11MaximalRep]

private theorem m11MaximalCase_5_6_9 :
    ({(5 : Fin 11), (6 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_0, m11MaximalRep]

private theorem m11MaximalCase_5_6_10 :
    ({(5 : Fin 11), (6 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_0_0, m11MaximalRep]

private theorem m11MaximalCase_5_7_8 :
    ({(5 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_0, m11MaximalRep]

private theorem m11MaximalCase_5_7_9 :
    ({(5 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_1, m11MaximalRep]

private theorem m11MaximalCase_5_7_10 :
    ({(5 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_0, m11MaximalRep]

private theorem m11MaximalCase_5_8_9 :
    ({(5 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_0, m11MaximalRep]

private theorem m11MaximalCase_5_8_10 :
    ({(5 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_0, m11MaximalRep]

private theorem m11MaximalCase_5_9_10 :
    ({(5 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_0, m11MaximalRep]

private theorem m11MaximalCase_6_7_8 :
    ({(6 : Fin 11), (7 : Fin 11), (8 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_1_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_1_0, m11MaximalRep]

private theorem m11MaximalCase_6_7_9 :
    ({(6 : Fin 11), (7 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_3_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_3_0, m11MaximalRep]

private theorem m11MaximalCase_6_7_10 :
    ({(6 : Fin 11), (7 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((7, ((2 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((7, ((2 : Fin 3), ((1 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_2_1_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_2_1_1, m11MaximalRep]

private theorem m11MaximalCase_6_8_9 :
    ({(6 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((2, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((2, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_2_1, m11MaximalRep]

private theorem m11MaximalCase_6_8_10 :
    ({(6 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_5_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_5_1, m11MaximalRep]

private theorem m11MaximalCase_6_9_10 :
    ({(6 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((3, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((3, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_0, m11MaximalRep]

private theorem m11MaximalCase_7_8_9 :
    ({(7 : Fin 11), (8 : Fin 11), (9 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_2_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_2_1, m11MaximalRep]

private theorem m11MaximalCase_7_8_10 :
    ({(7 : Fin 11), (8 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((1, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).2) =
      (m11MaximalRep ((1, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_5_0]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_5_0, m11MaximalRep]

private theorem m11MaximalCase_7_9_10 :
    ({(7 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((6, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((6, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_1_0_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_1_0_1, m11MaximalRep]

private theorem m11MaximalCase_8_9_10 :
    ({(8 : Fin 11), (9 : Fin 11), (10 : Fin 11)} : Finset (Fin 11)).image
        (m11MaximalNFPerm ((5, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).2) =
      (m11MaximalRep ((5, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2))))).1 : Finset (Fin 11)) := by
  rw [m11MaximalNFPerm_eq_0_6_1]
  ext x
  fin_cases x <;> simp [m11MaximalNFAction_0_6_1, m11MaximalRep]

private theorem m11MaximalWitness_1_9_10 :
    m11MaximalWitness (1 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (7, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_8_9 :
    m11MaximalWitness (2 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (5, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_7_9 :
    m11MaximalWitness (1 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (3, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_9 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (9 : Fin 11) =
      (7, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_5_9 :
    m11MaximalWitness (4 : Fin 11) (5 : Fin 11) (9 : Fin 11) =
      (6, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_3 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (3 : Fin 11) =
      (4, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_8_9 :
    m11MaximalWitness (5 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (5, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_8_9_10 :
    m11MaximalWitness (8 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_5 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (5 : Fin 11) =
      (7, ((2 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_6 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (6 : Fin 11) =
      (4, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_7_9 :
    m11MaximalWitness (6 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (7, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_6 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (6 : Fin 11) =
      (7, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_5 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (5 : Fin 11) =
      (4, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_9 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (9 : Fin 11) =
      (6, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_8_9 :
    m11MaximalWitness (3 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (2, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_5_6 :
    m11MaximalWitness (4 : Fin 11) (5 : Fin 11) (6 : Fin 11) =
      (3, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_6_9 :
    m11MaximalWitness (1 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (4, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_8 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (8 : Fin 11) =
      (6, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_6 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (6 : Fin 11) =
      (7, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_8 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (8 : Fin 11) =
      (3, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_8_10 :
    m11MaximalWitness (4 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_10 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (10 : Fin 11) =
      (5, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_7_10 :
    m11MaximalWitness (4 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (6, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_5_9 :
    m11MaximalWitness (3 : Fin 11) (5 : Fin 11) (9 : Fin 11) =
      (7, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_6_9 :
    m11MaximalWitness (0 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (7, ((2 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_5_7 :
    m11MaximalWitness (0 : Fin 11) (5 : Fin 11) (7 : Fin 11) =
      (5, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_6 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (6 : Fin 11) =
      (4, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_9 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (9 : Fin 11) =
      (3, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_8 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (8 : Fin 11) =
      (3, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_5_10 :
    m11MaximalWitness (0 : Fin 11) (5 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_8_10 :
    m11MaximalWitness (0 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (6, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_9 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (9 : Fin 11) =
      (4, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_9_10 :
    m11MaximalWitness (6 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (3, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_6_8 :
    m11MaximalWitness (1 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (4, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_5_8 :
    m11MaximalWitness (3 : Fin 11) (5 : Fin 11) (8 : Fin 11) =
      (7, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_5 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (5 : Fin 11) =
      (3, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_6_10 :
    m11MaximalWitness (4 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (7, ((0 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_6_7 :
    m11MaximalWitness (3 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (4, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_7_8_10 :
    m11MaximalWitness (7 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (1, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_9_10 :
    m11MaximalWitness (2 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_4 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (4 : Fin 11) =
      (2, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_7 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (7 : Fin 11) =
      (4, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_5_10 :
    m11MaximalWitness (3 : Fin 11) (5 : Fin 11) (10 : Fin 11) =
      (3, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_9 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (9 : Fin 11) =
      (3, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_8 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (8 : Fin 11) =
      (1, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_6_7 :
    m11MaximalWitness (2 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (7, ((2 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_10 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (10 : Fin 11) =
      (7, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_8 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (8 : Fin 11) =
      (4, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_5_8 :
    m11MaximalWitness (2 : Fin 11) (5 : Fin 11) (8 : Fin 11) =
      (6, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_9 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (9 : Fin 11) =
      (7, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_6 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (6 : Fin 11) =
      (0, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_8_9 :
    m11MaximalWitness (4 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (5, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_6_7 :
    m11MaximalWitness (0 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (3, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_7 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (7 : Fin 11) =
      (1, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_5_7 :
    m11MaximalWitness (2 : Fin 11) (5 : Fin 11) (7 : Fin 11) =
      (5, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_5_8 :
    m11MaximalWitness (1 : Fin 11) (5 : Fin 11) (8 : Fin 11) =
      (3, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_6_9 :
    m11MaximalWitness (3 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (4, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_10 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (10 : Fin 11) =
      (5, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_10 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (10 : Fin 11) =
      (4, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_9 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (9 : Fin 11) =
      (5, ((0 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_7_9 :
    m11MaximalWitness (4 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (1, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_6_8 :
    m11MaximalWitness (5 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (7, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_7_8 :
    m11MaximalWitness (1 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (3, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_8_10 :
    m11MaximalWitness (3 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (7, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_8 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (8 : Fin 11) =
      (7, ((2 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_7_8 :
    m11MaximalWitness (2 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (6, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_7_9 :
    m11MaximalWitness (0 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (6, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_9 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (9 : Fin 11) =
      (6, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_6_10 :
    m11MaximalWitness (0 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (7, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_7_10 :
    m11MaximalWitness (2 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_6 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (6 : Fin 11) =
      (4, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_10 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (10 : Fin 11) =
      (7, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_7_8_9 :
    m11MaximalWitness (7 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (5, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_8_10 :
    m11MaximalWitness (2 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_7_10 :
    m11MaximalWitness (1 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (7, ((1 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_2 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (2 : Fin 11) =
      (3, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_4 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (4 : Fin 11) =
      (3, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_7 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (7 : Fin 11) =
      (3, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_6 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (6 : Fin 11) =
      (4, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_6_10 :
    m11MaximalWitness (1 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (4, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_4 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (4 : Fin 11) =
      (2, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_8_9 :
    m11MaximalWitness (6 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (2, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_5_9 :
    m11MaximalWitness (0 : Fin 11) (5 : Fin 11) (9 : Fin 11) =
      (6, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_10 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (10 : Fin 11) =
      (2, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_5_7 :
    m11MaximalWitness (3 : Fin 11) (5 : Fin 11) (7 : Fin 11) =
      (2, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_6_8 :
    m11MaximalWitness (4 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (7, ((2 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_10 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (10 : Fin 11) =
      (3, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_5 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (5 : Fin 11) =
      (6, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_8 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (8 : Fin 11) =
      (7, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_10 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (10 : Fin 11) =
      (2, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_3 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (3 : Fin 11) =
      (7, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_6 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (6 : Fin 11) =
      (2, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_5 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (5 : Fin 11) =
      (7, ((2 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_7_8 :
    m11MaximalWitness (5 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (5, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_6_9 :
    m11MaximalWitness (2 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (3, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_5_6 :
    m11MaximalWitness (2 : Fin 11) (5 : Fin 11) (6 : Fin 11) =
      (7, ((2 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_9_10 :
    m11MaximalWitness (3 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (7, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_6_9 :
    m11MaximalWitness (4 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (7, ((2 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_9_10 :
    m11MaximalWitness (0 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (1, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_3_4 :
    m11MaximalWitness (1 : Fin 11) (3 : Fin 11) (4 : Fin 11) =
      (4, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_8 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (8 : Fin 11) =
      (5, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_5_10 :
    m11MaximalWitness (2 : Fin 11) (5 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_4 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (4 : Fin 11) =
      (7, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_5_6 :
    m11MaximalWitness (1 : Fin 11) (5 : Fin 11) (6 : Fin 11) =
      (4, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_4 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (4 : Fin 11) =
      (5, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_5_6 :
    m11MaximalWitness (3 : Fin 11) (5 : Fin 11) (6 : Fin 11) =
      (4, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_10 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (10 : Fin 11) =
      (3, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_3_7 :
    m11MaximalWitness (0 : Fin 11) (3 : Fin 11) (7 : Fin 11) =
      (7, ((2 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_7_10 :
    m11MaximalWitness (5 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (5, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_8 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (8 : Fin 11) =
      (7, ((1 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_7 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (7 : Fin 11) =
      (7, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_5 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (5 : Fin 11) =
      (7, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_4_6 :
    m11MaximalWitness (1 : Fin 11) (4 : Fin 11) (6 : Fin 11) =
      (4, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_8_10 :
    m11MaximalWitness (5 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_6_7 :
    m11MaximalWitness (5 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (2, ((0 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_7_10 :
    m11MaximalWitness (3 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (3, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_7_10 :
    m11MaximalWitness (6 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (7, ((2 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_6_7 :
    m11MaximalWitness (1 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (4, ((0 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_10 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (10 : Fin 11) =
      (5, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_5_9 :
    m11MaximalWitness (2 : Fin 11) (5 : Fin 11) (9 : Fin 11) =
      (1, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_5_6 :
    m11MaximalWitness (0 : Fin 11) (5 : Fin 11) (6 : Fin 11) =
      (3, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_5_9 :
    m11MaximalWitness (1 : Fin 11) (5 : Fin 11) (9 : Fin 11) =
      (3, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_5 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (5 : Fin 11) =
      (7, ((1 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_7_8 :
    m11MaximalWitness (4 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (6, ((1 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_7_9_10 :
    m11MaximalWitness (7 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_7 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (7 : Fin 11) =
      (5, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_7_10 :
    m11MaximalWitness (0 : Fin 11) (7 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_6 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (6 : Fin 11) =
      (4, ((2 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_8_10 :
    m11MaximalWitness (6 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (3, ((1 : Fin 3), ((5 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_8_10 :
    m11MaximalWitness (1 : Fin 11) (8 : Fin 11) (10 : Fin 11) =
      (7, ((1 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_3 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (3 : Fin 11) =
      (4, ((0 : Fin 3), ((2 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_5_8 :
    m11MaximalWitness (0 : Fin 11) (5 : Fin 11) (8 : Fin 11) =
      (1, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_5_10 :
    m11MaximalWitness (1 : Fin 11) (5 : Fin 11) (10 : Fin 11) =
      (7, ((1 : Fin 3), ((6 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_8_9 :
    m11MaximalWitness (0 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (5, ((0 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_5_7 :
    m11MaximalWitness (1 : Fin 11) (5 : Fin 11) (7 : Fin 11) =
      (2, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_5_7 :
    m11MaximalWitness (4 : Fin 11) (5 : Fin 11) (7 : Fin 11) =
      (5, ((0 : Fin 3), ((4 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_8_9 :
    m11MaximalWitness (1 : Fin 11) (8 : Fin 11) (9 : Fin 11) =
      (2, ((1 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_6_9 :
    m11MaximalWitness (5 : Fin 11) (6 : Fin 11) (9 : Fin 11) =
      (7, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_6_7_8 :
    m11MaximalWitness (6 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (7, ((0 : Fin 3), ((1 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_9_10 :
    m11MaximalWitness (4 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (6, ((1 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_4_5 :
    m11MaximalWitness (0 : Fin 11) (4 : Fin 11) (5 : Fin 11) =
      (5, ((0 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_6_10 :
    m11MaximalWitness (2 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (2, ((0 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_6_10 :
    m11MaximalWitness (3 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (4, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_3_9 :
    m11MaximalWitness (2 : Fin 11) (3 : Fin 11) (9 : Fin 11) =
      (7, ((2 : Fin 3), ((5 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_7 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (7 : Fin 11) =
      (7, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_1_2_7 :
    m11MaximalWitness (1 : Fin 11) (2 : Fin 11) (7 : Fin 11) =
      (7, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_7_8 :
    m11MaximalWitness (0 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (6, ((1 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_9 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (9 : Fin 11) =
      (7, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_2_5 :
    m11MaximalWitness (0 : Fin 11) (2 : Fin 11) (5 : Fin 11) =
      (6, ((0 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_4_7 :
    m11MaximalWitness (3 : Fin 11) (4 : Fin 11) (7 : Fin 11) =
      (7, ((2 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_5_8 :
    m11MaximalWitness (4 : Fin 11) (5 : Fin 11) (8 : Fin 11) =
      (6, ((0 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_6_7 :
    m11MaximalWitness (4 : Fin 11) (6 : Fin 11) (7 : Fin 11) =
      (3, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_6_8 :
    m11MaximalWitness (2 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (3, ((1 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_7_9 :
    m11MaximalWitness (5 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (5, ((1 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_4_5_10 :
    m11MaximalWitness (4 : Fin 11) (5 : Fin 11) (10 : Fin 11) =
      (1, ((0 : Fin 3), ((2 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_7_8 :
    m11MaximalWitness (3 : Fin 11) (7 : Fin 11) (8 : Fin 11) =
      (7, ((0 : Fin 3), ((1 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_7_9 :
    m11MaximalWitness (2 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (6, ((1 : Fin 3), ((4 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_7_9 :
    m11MaximalWitness (3 : Fin 11) (7 : Fin 11) (9 : Fin 11) =
      (7, ((0 : Fin 3), ((7 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_6_8 :
    m11MaximalWitness (0 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (7, ((2 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_5 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (5 : Fin 11) =
      (7, ((1 : Fin 3), ((3 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_0_1_8 :
    m11MaximalWitness (0 : Fin 11) (1 : Fin 11) (8 : Fin 11) =
      (7, ((1 : Fin 3), ((7 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_9_10 :
    m11MaximalWitness (5 : Fin 11) (9 : Fin 11) (10 : Fin 11) =
      (6, ((0 : Fin 3), ((6 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_2_4_7 :
    m11MaximalWitness (2 : Fin 11) (4 : Fin 11) (7 : Fin 11) =
      (6, ((1 : Fin 3), ((3 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_5_6_10 :
    m11MaximalWitness (5 : Fin 11) (6 : Fin 11) (10 : Fin 11) =
      (7, ((2 : Fin 3), ((0 : Fin 8), (0 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_3_6_8 :
    m11MaximalWitness (3 : Fin 11) (6 : Fin 11) (8 : Fin 11) =
      (4, ((2 : Fin 3), ((0 : Fin 8), (1 : Fin 2)))) := by
  rfl

private theorem m11MaximalWitness_spec_0 :
    ∀ b c : Fin 11, (0 : Fin 11) < b -> b < c ->
      ({(0 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (0 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (0 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_2] using m11MaximalCase_0_1_2
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_3] using m11MaximalCase_0_1_3
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_4] using m11MaximalCase_0_1_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_5] using m11MaximalCase_0_1_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_6] using m11MaximalCase_0_1_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_7] using m11MaximalCase_0_1_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_8] using m11MaximalCase_0_1_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_9] using m11MaximalCase_0_1_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_1_10] using m11MaximalCase_0_1_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_3] using m11MaximalCase_0_2_3
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_4] using m11MaximalCase_0_2_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_5] using m11MaximalCase_0_2_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_6] using m11MaximalCase_0_2_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_7] using m11MaximalCase_0_2_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_8] using m11MaximalCase_0_2_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_9] using m11MaximalCase_0_2_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_2_10] using m11MaximalCase_0_2_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_4] using m11MaximalCase_0_3_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_5] using m11MaximalCase_0_3_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_6] using m11MaximalCase_0_3_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_7] using m11MaximalCase_0_3_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_8] using m11MaximalCase_0_3_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_9] using m11MaximalCase_0_3_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_3_10] using m11MaximalCase_0_3_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_5] using m11MaximalCase_0_4_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_6] using m11MaximalCase_0_4_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_7] using m11MaximalCase_0_4_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_8] using m11MaximalCase_0_4_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_9] using m11MaximalCase_0_4_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_4_10] using m11MaximalCase_0_4_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_5_6] using m11MaximalCase_0_5_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_5_7] using m11MaximalCase_0_5_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_5_8] using m11MaximalCase_0_5_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_5_9] using m11MaximalCase_0_5_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_5_10] using m11MaximalCase_0_5_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_6_7] using m11MaximalCase_0_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_6_8] using m11MaximalCase_0_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_6_9] using m11MaximalCase_0_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_6_10] using m11MaximalCase_0_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_7_8] using m11MaximalCase_0_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_7_9] using m11MaximalCase_0_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_7_10] using m11MaximalCase_0_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_8_9] using m11MaximalCase_0_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_8_10] using m11MaximalCase_0_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_0_9_10] using m11MaximalCase_0_9_10

private theorem m11MaximalWitness_spec_1 :
    ∀ b c : Fin 11, (1 : Fin 11) < b -> b < c ->
      ({(1 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (1 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (1 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_3] using m11MaximalCase_1_2_3
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_4] using m11MaximalCase_1_2_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_5] using m11MaximalCase_1_2_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_6] using m11MaximalCase_1_2_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_7] using m11MaximalCase_1_2_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_8] using m11MaximalCase_1_2_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_9] using m11MaximalCase_1_2_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_2_10] using m11MaximalCase_1_2_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_4] using m11MaximalCase_1_3_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_5] using m11MaximalCase_1_3_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_6] using m11MaximalCase_1_3_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_7] using m11MaximalCase_1_3_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_8] using m11MaximalCase_1_3_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_9] using m11MaximalCase_1_3_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_3_10] using m11MaximalCase_1_3_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_5] using m11MaximalCase_1_4_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_6] using m11MaximalCase_1_4_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_7] using m11MaximalCase_1_4_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_8] using m11MaximalCase_1_4_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_9] using m11MaximalCase_1_4_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_4_10] using m11MaximalCase_1_4_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_5_6] using m11MaximalCase_1_5_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_5_7] using m11MaximalCase_1_5_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_5_8] using m11MaximalCase_1_5_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_5_9] using m11MaximalCase_1_5_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_5_10] using m11MaximalCase_1_5_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_6_7] using m11MaximalCase_1_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_6_8] using m11MaximalCase_1_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_6_9] using m11MaximalCase_1_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_6_10] using m11MaximalCase_1_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_7_8] using m11MaximalCase_1_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_7_9] using m11MaximalCase_1_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_7_10] using m11MaximalCase_1_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_8_9] using m11MaximalCase_1_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_8_10] using m11MaximalCase_1_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_1_9_10] using m11MaximalCase_1_9_10

private theorem m11MaximalWitness_spec_2 :
    ∀ b c : Fin 11, (2 : Fin 11) < b -> b < c ->
      ({(2 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (2 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (2 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_4] using m11MaximalCase_2_3_4
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_5] using m11MaximalCase_2_3_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_6] using m11MaximalCase_2_3_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_7] using m11MaximalCase_2_3_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_8] using m11MaximalCase_2_3_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_9] using m11MaximalCase_2_3_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_3_10] using m11MaximalCase_2_3_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_5] using m11MaximalCase_2_4_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_6] using m11MaximalCase_2_4_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_7] using m11MaximalCase_2_4_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_8] using m11MaximalCase_2_4_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_9] using m11MaximalCase_2_4_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_4_10] using m11MaximalCase_2_4_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_5_6] using m11MaximalCase_2_5_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_5_7] using m11MaximalCase_2_5_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_5_8] using m11MaximalCase_2_5_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_5_9] using m11MaximalCase_2_5_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_5_10] using m11MaximalCase_2_5_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_6_7] using m11MaximalCase_2_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_6_8] using m11MaximalCase_2_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_6_9] using m11MaximalCase_2_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_6_10] using m11MaximalCase_2_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_7_8] using m11MaximalCase_2_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_7_9] using m11MaximalCase_2_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_7_10] using m11MaximalCase_2_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_8_9] using m11MaximalCase_2_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_8_10] using m11MaximalCase_2_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_2_9_10] using m11MaximalCase_2_9_10

private theorem m11MaximalWitness_spec_3 :
    ∀ b c : Fin 11, (3 : Fin 11) < b -> b < c ->
      ({(3 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (3 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (3 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_5] using m11MaximalCase_3_4_5
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_6] using m11MaximalCase_3_4_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_7] using m11MaximalCase_3_4_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_8] using m11MaximalCase_3_4_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_9] using m11MaximalCase_3_4_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_4_10] using m11MaximalCase_3_4_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_5_6] using m11MaximalCase_3_5_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_5_7] using m11MaximalCase_3_5_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_5_8] using m11MaximalCase_3_5_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_5_9] using m11MaximalCase_3_5_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_5_10] using m11MaximalCase_3_5_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_6_7] using m11MaximalCase_3_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_6_8] using m11MaximalCase_3_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_6_9] using m11MaximalCase_3_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_6_10] using m11MaximalCase_3_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_7_8] using m11MaximalCase_3_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_7_9] using m11MaximalCase_3_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_7_10] using m11MaximalCase_3_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_8_9] using m11MaximalCase_3_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_8_10] using m11MaximalCase_3_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_3_9_10] using m11MaximalCase_3_9_10

private theorem m11MaximalWitness_spec_4 :
    ∀ b c : Fin 11, (4 : Fin 11) < b -> b < c ->
      ({(4 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (4 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (4 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_5_6] using m11MaximalCase_4_5_6
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_5_7] using m11MaximalCase_4_5_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_5_8] using m11MaximalCase_4_5_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_5_9] using m11MaximalCase_4_5_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_5_10] using m11MaximalCase_4_5_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_6_7] using m11MaximalCase_4_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_6_8] using m11MaximalCase_4_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_6_9] using m11MaximalCase_4_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_6_10] using m11MaximalCase_4_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_7_8] using m11MaximalCase_4_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_7_9] using m11MaximalCase_4_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_7_10] using m11MaximalCase_4_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_8_9] using m11MaximalCase_4_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_8_10] using m11MaximalCase_4_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_4_9_10] using m11MaximalCase_4_9_10

private theorem m11MaximalWitness_spec_5 :
    ∀ b c : Fin 11, (5 : Fin 11) < b -> b < c ->
      ({(5 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (5 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (5 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_6_7] using m11MaximalCase_5_6_7
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_6_8] using m11MaximalCase_5_6_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_6_9] using m11MaximalCase_5_6_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_6_10] using m11MaximalCase_5_6_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_7_8] using m11MaximalCase_5_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_7_9] using m11MaximalCase_5_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_7_10] using m11MaximalCase_5_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_8_9] using m11MaximalCase_5_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_8_10] using m11MaximalCase_5_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_5_9_10] using m11MaximalCase_5_9_10

private theorem m11MaximalWitness_spec_6 :
    ∀ b c : Fin 11, (6 : Fin 11) < b -> b < c ->
      ({(6 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (6 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (6 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_7_8] using m11MaximalCase_6_7_8
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_7_9] using m11MaximalCase_6_7_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_7_10] using m11MaximalCase_6_7_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_8_9] using m11MaximalCase_6_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_8_10] using m11MaximalCase_6_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_6_9_10] using m11MaximalCase_6_9_10

private theorem m11MaximalWitness_spec_7 :
    ∀ b c : Fin 11, (7 : Fin 11) < b -> b < c ->
      ({(7 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (7 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (7 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_7_8_9] using m11MaximalCase_7_8_9
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_7_8_10] using m11MaximalCase_7_8_10
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_7_9_10] using m11MaximalCase_7_9_10

private theorem m11MaximalWitness_spec_8 :
    ∀ b c : Fin 11, (8 : Fin 11) < b -> b < c ->
      ({(8 : Fin 11), b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness (8 : Fin 11) b c).2) =
        (m11MaximalRep (m11MaximalWitness (8 : Fin 11) b c).1 : Finset (Fin 11)) := by
  intro b c hb hbc
  fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hb hbc ⊢ <;> try omega
  · simpa only [Fin.reduceFinMk, m11MaximalWitness_8_9_10] using m11MaximalCase_8_9_10

private theorem m11MaximalWitness_spec :
    ∀ a b c : Fin 11, a < b -> b < c ->
      ({a, b, c} : Finset (Fin 11)).image
          (m11MaximalNFPerm (m11MaximalWitness a b c).2) =
        (m11MaximalRep (m11MaximalWitness a b c).1 : Finset (Fin 11)) := by
  intro a b c hab hbc
  fin_cases a
  · exact m11MaximalWitness_spec_0 b c hab hbc
  · exact m11MaximalWitness_spec_1 b c hab hbc
  · exact m11MaximalWitness_spec_2 b c hab hbc
  · exact m11MaximalWitness_spec_3 b c hab hbc
  · exact m11MaximalWitness_spec_4 b c hab hbc
  · exact m11MaximalWitness_spec_5 b c hab hbc
  · exact m11MaximalWitness_spec_6 b c hab hbc
  · exact m11MaximalWitness_spec_7 b c hab hbc
  · exact m11MaximalWitness_spec_8 b c hab hbc
  · fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hab hbc ⊢ <;> omega
  · fin_cases b <;> fin_cases c <;> simp only [Fin.reduceFinMk] at hab hbc ⊢ <;> omega
private theorem m11MaximalNF_cover :
    ∀ t : M11TripleSet,
      ∃ (i : Fin 8) (p : Fin 3 × Fin 8 × Fin 2),
        m11MaximalNFPerm p • t = m11MaximalRep i := by
  intro t
  rcases t with ⟨s, hs⟩
  change s.card = 3 at hs
  let l := s.sort (· ≤ ·)
  have hl : l.length = 3 := by simp [l, hs]
  obtain ⟨a, b, c, hlist⟩ := List.length_eq_three.mp hl
  have hsort : l.SortedLT := by
    simpa [l] using Finset.sortedLT_sort s
  rw [hlist] at hsort
  have hab : a < b := by
    have hhead := (List.pairwise_cons.mp hsort.pairwise).1
    simpa using hhead b (by simp)
  have hbc : b < c := by
    have htail := (List.pairwise_cons.mp hsort.pairwise).2
    have hhead := (List.pairwise_cons.mp htail).1
    simpa using hhead c (by simp)
  have hsabc : s = {a, b, c} := by
    have hsortset : l.toFinset = s := Finset.sort_toFinset s (· ≤ ·)
    rw [← hsortset, hlist]
    simp
  simp only [Subtype.ext_iff]
  change ∃ (i : Fin 8) (p : Fin 3 × Fin 8 × Fin 2),
    s.image (m11MaximalNFPerm p) = (m11MaximalRep i : Finset (Fin 11))
  rw [hsabc]
  let w := m11MaximalWitness a b c
  refine ⟨w.1, w.2, ?_⟩
  exact m11MaximalWitness_spec a b c hab hbc

private noncomputable def m11MaximalTransport : Fin 8 → M11 := ![
  1,
  m11GeneratorBInM11 * m11GeneratorAInM11 *
    (m11GeneratorBInM11 * m11GeneratorBInM11 * m11GeneratorBInM11),
  m11GeneratorBInM11 * m11GeneratorAInM11 *
    (m11GeneratorBInM11 * m11GeneratorBInM11 * m11GeneratorBInM11) *
    m11GeneratorAInM11 * m11GeneratorBInM11,
  m11GeneratorBInM11 * m11GeneratorAInM11 * m11GeneratorBInM11,
  m11GeneratorBInM11 * m11GeneratorBInM11,
  m11GeneratorBInM11,
  m11GeneratorBInM11 * m11GeneratorBInM11 * m11GeneratorBInM11,
  m11GeneratorBInM11 * m11GeneratorAInM11 *
    m11GeneratorBInM11 * m11GeneratorAInM11 * m11GeneratorBInM11
]

private def m11MaximalTransportPerm : Fin 8 → Equiv.Perm (Fin 11) := ![
  1,
  m11GeneratorB * m11GeneratorA *
    (m11GeneratorB * m11GeneratorB * m11GeneratorB),
  m11GeneratorB * m11GeneratorA *
    (m11GeneratorB * m11GeneratorB * m11GeneratorB) *
    m11GeneratorA * m11GeneratorB,
  m11GeneratorB * m11GeneratorA * m11GeneratorB,
  m11GeneratorB * m11GeneratorB,
  m11GeneratorB,
  m11GeneratorB * m11GeneratorB * m11GeneratorB,
  m11GeneratorB * m11GeneratorA *
    m11GeneratorB * m11GeneratorA * m11GeneratorB
]

private theorem m11MaximalTransport_perm (i : Fin 8) :
    (m11MaximalTransport i : Equiv.Perm (Fin 11)) =
      m11MaximalTransportPerm i := by
  fin_cases i <;> rfl

private theorem m11MaximalTransportPerm_action :
    ∀ i : Fin 8, m11MaximalTransportPerm i • m11FixedTriple =
      m11MaximalRep i := by
  intro i
  fin_cases i <;> decide

private theorem m11MaximalTransport_action :
    ∀ i : Fin 8, m11MaximalTransport i • m11FixedTriple =
      m11MaximalRep i := by
  intro i
  change
    (m11MaximalTransport i : Equiv.Perm (Fin 11)) •
      m11FixedTriple = m11MaximalRep i
  rw [m11MaximalTransport_perm]
  exact m11MaximalTransportPerm_action i

private noncomputable def m11MaximalWordGen (i : Fin 8) : Fin 6 → M11 := ![
  m11CentralizerU,
  m11CentralizerV,
  m11MaximalTransport i,
  m11CentralizerU⁻¹,
  m11CentralizerV⁻¹,
  (m11MaximalTransport i)⁻¹
]

private noncomputable def m11MaximalWordEval (i : Fin 8) :
    List (Fin 6) → M11
  | [] => 1
  | j :: w => m11MaximalWordGen i j * m11MaximalWordEval i w

private def m11MaximalWord : Fin 8 → List (Fin 6) := ![
  [],
  [3, 3, 2, 0, 1, 2, 0, 0, 2, 0],
  [0, 5, 5, 0, 1, 0, 2],
  [1, 2, 3, 5, 0, 5, 1],
  [0, 0, 2, 0, 2, 4, 2, 3, 3],
  [2],
  [5],
  [5, 0, 4, 5, 5, 0]
]

private theorem m11MaximalWordEval_mem_of
    (K : Subgroup M11) (i : Fin 8)
    (hU : m11CentralizerU ∈ K)
    (hV : m11CentralizerV ∈ K)
    (hT : m11MaximalTransport i ∈ K)
    (w : List (Fin 6)) :
    m11MaximalWordEval i w ∈ K := by
  induction w with
  | nil => simp [m11MaximalWordEval]
  | cons j w ih =>
      rw [m11MaximalWordEval]
      apply K.mul_mem
      · fin_cases j <;> simp [m11MaximalWordGen, hU, hV, hT]
      · exact ih

private theorem m11MaximalWordEval_mem
    (K : Subgroup M11) (i : Fin 8)
    (hU : m11CentralizerU ∈ K)
    (hV : m11CentralizerV ∈ K)
    (hT : m11MaximalTransport i ∈ K) :
    m11MaximalWordEval i (m11MaximalWord i) ∈ K :=
  m11MaximalWordEval_mem_of K i hU hV hT (m11MaximalWord i)

private theorem m11MaximalB_word
    (i : Fin 8) (hi : i ≠ 0) :
    m11GeneratorBInM11 =
      m11MaximalWordEval i (m11MaximalWord i) := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals
    apply Subtype.ext
    change (m11GeneratorB : Equiv.Perm (Fin 11)) = _
    simp [m11MaximalWordEval, m11MaximalWord, m11MaximalWordGen,
      m11CentralizerU_perm, m11CentralizerV_perm,
      m11MaximalTransport_perm, m11MaximalTransportPerm,
      m11GeneratorA, m11GeneratorB]
  all_goals decide

/-- The standard involution centralizer of M11 is a maximal subgroup. -/
public theorem m11_involutionCentralizer_isCoatom :
    IsCoatom m11InvolutionCentralizer := by
  constructor
  · intro htop
    have hcard := congrArg (fun H : Subgroup M11 => Nat.card H) htop
    rw [m11_involutionCentralizer_card, Subgroup.card_top, m11_order] at hcard
    norm_num at hcard
  · intro K hHK
    obtain ⟨g, hgK, hgH⟩ := SetLike.exists_of_lt hHK
    obtain ⟨i, p, hpt⟩ :=
      m11MaximalNF_cover (g • m11FixedTriple)
    have hNF : m11MaximalNF p ∈ K :=
      hHK.le (m11MaximalNF_mem p)
    have hi : i ≠ 0 := by
      intro hi0
      subst i
      have hqH : m11MaximalNF p * g ∈
          m11InvolutionCentralizer := by
        rw [m11_involutionCentralizer_eq_fixedTriple_stabilizer,
          MulAction.mem_stabilizer_iff, mul_smul]
        change ((((m11MaximalNF p : M11) : Equiv.Perm (Fin 11)) •
          (g • m11FixedTriple) : M11TripleSet) = m11FixedTriple)
        rw [m11MaximalNF_perm]
        simpa [m11MaximalRep] using hpt
      apply hgH
      simpa [mul_assoc] using
        m11InvolutionCentralizer.mul_mem
          (m11InvolutionCentralizer.inv_mem (m11MaximalNF_mem p)) hqH
    have hxK : m11MaximalNF p * g ∈ K :=
      K.mul_mem hNF hgK
    have hpt' :
        m11MaximalNF p • (g • m11FixedTriple) =
          m11MaximalRep i := by
      change ((((m11MaximalNF p : M11) : Equiv.Perm (Fin 11)) •
        (g • m11FixedTriple) : M11TripleSet) = m11MaximalRep i)
      rw [m11MaximalNF_perm]
      exact hpt
    have hxt :
        (m11MaximalNF p * g) • m11FixedTriple =
          m11MaximalRep i := by
      rw [mul_smul]
      exact hpt'
    have htrans :
        m11MaximalTransport i • m11FixedTriple =
          m11MaximalRep i :=
      m11MaximalTransport_action i
    let q : M11 := (m11MaximalTransport i)⁻¹ *
      (m11MaximalNF p * g)
    have hqH : q ∈ m11InvolutionCentralizer := by
      rw [m11_involutionCentralizer_eq_fixedTriple_stabilizer,
        MulAction.mem_stabilizer_iff]
      change ((m11MaximalTransport i)⁻¹ *
        (m11MaximalNF p * g)) • m11FixedTriple = m11FixedTriple
      rw [mul_smul, hxt, ← htrans, inv_smul_smul]
    have hqK : q ∈ K := hHK.le hqH
    have htransportK : m11MaximalTransport i ∈ K := by
      have htmp := K.mul_mem hxK (K.inv_mem hqK)
      simpa [q, mul_assoc] using htmp
    have hUK : m11CentralizerU ∈ K := hHK.le m11CentralizerU_mem
    have hVK : m11CentralizerV ∈ K := hHK.le m11CentralizerV_mem
    have hBK :
        m11GeneratorBInM11 ∈ K := by
      rw [m11MaximalB_word i hi]
      exact m11MaximalWordEval_mem K i hUK hVK htransportK
    have hA_H : m11GeneratorAInM11 ∈ m11InvolutionCentralizer := by
      rw [m11_mem_involutionCentralizer_iff]
    have hAK : m11GeneratorAInM11 ∈ K := hHK.le hA_H
    have hgen :
        Subgroup.closure
          ({m11GeneratorAInM11, m11GeneratorBInM11} : Set M11) ≤ K := by
      refine (Subgroup.closure_le K).2 ?_
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hAK
      · exact hBK
    have hKeq : K = ⊤ :=
      top_unique (by simpa [m11_generators_closure_eq_top] using hgen)
    exact hKeq

end Sporadic.Mathieu
