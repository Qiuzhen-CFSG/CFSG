module

public import Stellmacher.Recognition.LyonsU3Four.TableICharacterExtraction
public import Stellmacher.Recognition.LyonsU3Four.TableIClassificationLargeDifferences
public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedRowCoverage
public import Stellmacher.Recognition.LyonsU3Four.TableIIsolatedCountClassification
public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeRowSupport
public import Stellmacher.Recognition.LyonsU3Four.TableIClassificationConsecutiveDifferences
public import Stellmacher.Recognition.LyonsU3Four.TableIClassificationSparseWithoutOpposite
public import Stellmacher.Recognition.LyonsU3Four.TableISparseOppositeTransport
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationEarly
public import Stellmacher.Recognition.LyonsU3Four.TableIEliminationLate
public import Stellmacher.Recognition.LyonsU3Four.TableISurvivorCompletion
public import Stellmacher.Recognition.LyonsU3Four.TableIDegreeTwelveTransport

/-!
# The Lyons character producer from sparse-opposite multiplicities

The explicit scalar classifier completes the sparse-opposite branch by counting
all normalized rows and reconstructing a principal-preserving signed row
equivalence. The other three difference branches give a canonical Table I
matrix, possibly after numerical column reflection.

Signed transport carries all degree, order and prime constraints to that
matrix. The early and late eliminations leave U and V. Galois normalization
retains its row permutation, so the forced degree-twelve witness pulls back to
the original rows. In the reflected branch we then undo the column reflection
before extracting any actual character; no fifth-root section formula is
asserted for the reflected columns.

Ambient realization and the existing character-extraction and strong-embedding
adapters yield the rational degree-twelve character, the centralizer formula,
strong embedding, and trivial odd cores in involution centralizers of N₂ groups.
The only remaining classification input here is the stated scalar hypothesis.

Source: R. Lyons, *A Characterization of the Group U₃(4)*, Trans. AMS 164
(1972), pp. 374–386; detailed source notes are in the imported modules.
-/

public section
noncomputable section
namespace Stellmacher.Recognition.LyonsU3Four
open GeneralizedDecompositionData

variable {I : Type*} [Fintype I]

/-- The four difference branches assemble to a canonical pattern up to the
numerical column reflection. The sparse-opposite branch is discharged by the
explicit multiplicity classifier supplied as input. -/
theorem canonical_or_reflected_of_pattern_and_opposite_counts
    (d : GeneralizedDecompositionData I) (principal : I)
    (h : d.TableIPatternHypotheses principal)
    (hcounts : ∀ m : Fin 51 → ℕ,
      SparseOppositeRows.MultiplicityConstraints m →
        ∃ v : Fin 4, m = SparseOppositeRows.modelCounts v) :
    d.HasCanonicalTableIPattern principal ∨
      d.reflectColumns.HasCanonicalTableIPattern principal := by
  rcases d.tableI_difference_cases with hl | ⟨hl, hc⟩ | ⟨hl, hc, ho⟩ | ⟨hl, hc, ho⟩
  · exact d.hasCanonicalTableIPattern_or_reflect_of_largeDifference_enumeration
      principal h hl TableIIsolatedRows.admissible_covered
      (by
        intro n hn
        exact TableIIsolatedRows.count_solutions n hn)
  · exact d.canonical_or_reflected_of_consecutive h hl hc
  · exact Or.inl (d.hasCanonicalTableIPattern_of_sparse_without_opposite h hl hc ho)
  · have hs := d.normalized_sparse_opposite_supported h hl hc
    have hm := d.opposite_multiplicity_constraints h hs ho
    obtain ⟨v, hv⟩ := hcounts _ hm
    exact Or.inl (d.hasCanonicalTableIPattern_of_opposite_modelCounts h hs v hv)

/-- Keep the normalizing permutation when using the printed degree labels. -/
private theorem witness_of_galois_labels
    {d : GeneralizedDecompositionData I} {principal : I} {L : Type*}
    (a : d.GaloisLabeling principal L) (hz : ∀ j, 0 < d.zValue j)
    {r : I → ℤ} {g c z : ℕ}
    (hd : d.DegreeConstraints principal r) (ho : d.OrderConstraints r g c z)
    (hp : d.PrimeConstraints r g)
    (produce : ∀ x : L → ℤ,
      d.DegreeConstraints principal (fun j => x (a.label j)) →
      d.OrderConstraints (fun j => x (a.label j)) g c z →
      d.PrimeConstraints (fun j => x (a.label j)) g →
      Nonempty (DegreeTwelveWitness d (fun j => x (a.label j)))) :
    Nonempty (DegreeTwelveWitness d r) := by
  obtain ⟨e, he, hm⟩ := a.exists_normalizing_perm hd.galois_symmetry hz
  let x : L → ℤ := fun l => r (a.representative l)
  let h : SignedDegreeEquiv d d (fun j => x (a.label j)) r := {
    equiv := e
    sign := fun _ => 1
    sign_sq := fun _ => by norm_num
    degree_eq := fun j => by simpa [x] using (hm j).2
    t_eq := fun j => by simpa using congrFun (hm j).1 0
    z_eq := fun j i => by simpa using congrFun (hm j).1 i.succ }
  have he' : h.symm.equiv principal = principal := e.symm_apply_eq.mpr he.symm
  have hd' := h.symm.degreeConstraints (principal := principal) (by rfl) hd
  rw [he'] at hd'
  obtain ⟨w⟩ := produce x hd' (h.symm.orderConstraints ho) (h.symm.primeConstraints hp)
  exact ⟨w.signedTransport h⟩

private theorem witness_of_tableIData
    (a : TableICase) (v : a.Variant)
    {r : Fin (tableIRowCount a) → ℤ} {g c z : ℕ}
    (hd : (tableIData a v).DegreeConstraints (tableIPrincipal a) r)
    (ho : (tableIData a v).OrderConstraints r g c z)
    (hp : (tableIData a v).PrimeConstraints r g) :
    Nonempty (DegreeTwelveWitness (tableIData a v) r) := by
  cases a with
  | A => exact False.elim (tableI_early_impossible .A v (by simp) hd ho hp)
  | B => exact False.elim (tableI_early_impossible .B v (by simp) hd ho hp)
  | C => exact False.elim (tableI_early_impossible .C v (by simp) hd ho hp)
  | D => exact False.elim (tableI_early_impossible .D v (by simp) hd ho hp)
  | E => exact False.elim (tableI_early_impossible .E v (by simp) hd ho hp)
  | F => exact False.elim (tableI_early_impossible .F v (by simp) hd ho hp)
  | G => exact False.elim (tableI_early_impossible .G v (by simp) hd ho hp)
  | H => exact False.elim (tableI_early_impossible .H v (by simp) hd ho hp)
  | J => exact False.elim (tableI_early_impossible .J v (by simp) hd ho hp)
  | K => exact False.elim (tableI_early_impossible .K v (by simp) hd ho hp)
  | L => exact False.elim (tableI_early_impossible .L v (by simp) hd ho hp)
  | M => exact False.elim (tableI_late_impossible .M v (by simp) hd ho hp)
  | N => exact False.elim (tableI_late_impossible .N v (by simp) hd ho hp)
  | P => exact False.elim (tableI_late_impossible .P v (by simp) hd ho hp)
  | Q => exact False.elim (tableI_late_impossible .Q v (by simp) hd ho hp)
  | R => exact False.elim (tableI_late_impossible .R v (by simp) hd ho hp)
  | S => exact False.elim (tableI_late_impossible .S v (by simp) hd ho hp)
  | T => exact False.elim (tableI_late_impossible .T v (by simp) hd ho hp)
  | U =>
    cases v
    exact witness_of_galois_labels SurvivorU.galoisLabeling (by decide) hd ho hp
      (fun _ hd' ho' hp' => ⟨SurvivorU.degree_twelve_witness_of_constraints hd' ho' hp'⟩)
  | V =>
    cases v
    exact witness_of_galois_labels SurvivorV.galoisLabeling (by decide) hd ho hp
      (fun _ hd' ho' hp' => ⟨SurvivorV.degree_twelve_witness_of_constraints hd' ho' hp'⟩)

private theorem witness_of_canonical_pattern
    {d : GeneralizedDecompositionData I} {principal : I}
    (hpat : d.TableIPatternHypotheses principal)
    {r : I → ℤ} {g c z : ℕ}
    (hd : d.DegreeConstraints principal r)
    (ho : d.OrderConstraints r g c z)
    (hp : d.PrimeConstraints r g)
    (hc : d.HasCanonicalTableIPattern principal) :
    Nonempty (DegreeTwelveWitness d r) := by
  rcases hc with ⟨a, v, e, ε, hε, hm, he⟩
  have hq : tableIMatrix a v (tableIPrincipal a) 0 = 1 := by
    rw [tableIMatrix_principal]
    rfl
  obtain ⟨hd', ho', hp'⟩ := constraints_of_signed_matrix e ε hε hm he
    hpat.principal_dT hq hd ho hp
  obtain ⟨w⟩ := witness_of_tableIData a v hd' ho' hp'
  exact ⟨w.signedTransport (signedDegreeEquivOfMatrix d (tableIMatrix a v) r e ε hε hm).symm⟩

/-- Produce the degree-twelve witness from the actual ambient constraints and
an explicit sparse-opposite multiplicity classifier. -/
theorem ambient_degreeTwelveWitnessProducer_of_opposite_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G)
    (hcounts : ∀ m : Fin 51 → ℕ,
      SparseOppositeRows.MultiplicityConstraints m →
        ∃ v : Fin 4, m = SparseOppositeRows.modelCounts v) :
    AmbientDegreeTwelveWitnessProducer S := by
  intro b t ht μ a hd ho hp
  have hpat := a.pattern
  rcases canonical_or_reflected_of_pattern_and_opposite_counts a.columns
      ⟨b.principal, b.principal_mem⟩ hpat hcounts with hc | hc
  · exact witness_of_canonical_pattern hpat hd ho hp hc
  · have hd' := hd.reflectColumns
    have ho' := ho.reflectColumns
    have hp' := hp.reflectColumns
    obtain ⟨w⟩ := witness_of_canonical_pattern (hpat.reflectColumns a.columns)
      hd' ho' hp' hc
    exact ⟨w.of_reflectColumns⟩

/-- The explicit multiplicity classifier supplies the actual rational character
and the centralizer order formula at every nonidentity Sylow-center element. -/
theorem character_and_formula_of_isNTwoGroup_and_opposite_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (hs : SylowStructure S)
    (hcounts : ∀ m : Fin 51 → ℕ,
      SparseOppositeRows.MultiplicityConstraints m →
        ∃ v : Fin 4, m = SparseOppositeRows.modelCounts v) :
    (∃ χ : ClassFunction G, IsIrreducibleCharacter χ ∧ χ 1 = 12 ∧
      ∀ g : G, ∃ q : ℚ, χ g = (q : ℂ)) ∧
    (∀ u ∈ centerImage S, u ≠ 1 →
      Nat.card G * Nat.card (Subgroup.centralizer (centerImage S : Set G)) ^ 2 =
        195 * Nat.card (Subgroup.centralizer ({u} : Set G)) ^ 3) :=
  character_and_formula_of_isNTwoGroup_and_degreeTwelveWitnessProducer hN S hs
    (ambient_degreeTwelveWitnessProducer_of_opposite_counts S hcounts)

/-- The character and formula force centralizer equality and strong embedding
of the Sylow-center normalizer. -/
theorem centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_opposite_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (hs : SylowStructure S)
    (hcounts : ∀ m : Fin 51 → ℕ,
      SparseOppositeRows.MultiplicityConstraints m →
        ∃ v : Fin 4, m = SparseOppositeRows.modelCounts v) :
    (∀ u ∈ centerImage S, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) =
        Subgroup.centralizer (centerImage S : Set G)) ∧
    IsStronglyEmbedded (Subgroup.normalizer (centerImage S : Set G)) :=
  centralizer_eq_and_stronglyEmbedded_of_isNTwoGroup_and_degreeTwelveWitnessProducer
    hN S hs (ambient_degreeTwelveWitnessProducer_of_opposite_counts S hcounts)

/-- Direct endpoint used by the recognition consumers. -/
theorem involutionCentralizer_oddCore_eq_bot_of_opposite_counts
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hN : IsNTwoGroup G) (S : Sylow 2 G) (hs : SylowStructure S)
    (hcounts : ∀ m : Fin 51 → ℕ,
      SparseOppositeRows.MultiplicityConstraints m →
        ∃ v : Fin 4, m = SparseOppositeRows.modelCounts v)
    {x : G} (hx : orderOf x = 2) :
    pPrimeCore 2 (Subgroup.centralizer ({x} : Set G)) = ⊥ :=
  involutionCentralizer_oddCore_eq_bot_of_isNTwoGroup_and_degreeTwelveWitnessProducer
    hN S hs (ambient_degreeTwelveWitnessProducer_of_opposite_counts S hcounts) hx

end Stellmacher.Recognition.LyonsU3Four
