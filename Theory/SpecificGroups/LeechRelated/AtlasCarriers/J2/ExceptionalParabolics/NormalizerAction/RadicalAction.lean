module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer.QuotientSeed
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Center and odd action on the fixed Hall--Janko radical

The existing 64-element enumeration bounds the center by four. The first
fixed cubic word fixes no nonidentity central element. Twelve commutators
with the two cubic words generate all six radical generators, so the
radical lies in the literal two-residual of its inner normalizer.

Source: GLS3 Table 5.3g; Aschbacher--Smith 15.3.42, printed p.1138.
The tables and words retain the ATLAS J2G1-p100B0 attribution from
`PairNormalizer`. All finite checks use kernel reduction.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
open Theory.GroupTheory Subgroup GeneratorPair Seed PairNormalizer
open PairNormalizer.RadicalData PairNormalizer.QuotientData
open GeneratorPair.SecondOrbitCertificate

set_option maxRecDepth 100000 in
private theorem center_check : ∀ i : Fin 64,
    (∀ j : Fin 6,
      (qGenTable j * qTable i) 0 = (qTable i * qGenTable j) 0 ∧
      (qGenTable j * qTable i) 1 = (qTable i * qGenTable j) 1) →
    i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26 := by
  apply allFin
  decide +kernel

private theorem center_index {x : q₂} (hx : x ∈ center q₂)
    {i : Fin 64} (hi : qElement i = x) : i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26 := by
  apply center_check
  intro j
  have h := congrArg (fun y : q₂ => inclusion (y : Carrier))
    (mem_center_iff.mp hx ⟨q₂Generator j, subset_closure ⟨j, rfl⟩⟩)
  change inclusion (q₂Generator j * (x : Carrier)) = inclusion ((x : Carrier) * q₂Generator j) at h
  rw [← hi, map_mul, map_mul, q₂Generator_inclusion, qElement_inclusion] at h
  exact ⟨congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h,
    congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h⟩

/-- The actual radical center has at most four elements. -/
theorem card_center_q₂_le : Nat.card (center q₂) ≤ 4 := by
  classical
  let f : center q₂ → {i : Fin 64 // i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26} := fun x =>
    ⟨(exists_qElement x.val.property).choose,
      center_index x.property (exists_qElement x.val.property).choose_spec⟩
  have hf : Function.Injective f := by
    intro x y h
    have hi := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    exact (exists_qElement x.val.property).choose_spec.symm.trans
      ((congrArg qElement hi).trans (exists_qElement y.val.property).choose_spec)
  have h := Nat.card_le_card_of_injective f hf
  have hc : Nat.card {i : Fin 64 // i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26} = 4 := by
    rw [Nat.card_eq_fintype_card]
    decide
  exact h.trans_eq hc

set_option maxRecDepth 100000 in
private theorem center_fixed_check : ∀ i : Fin 64,
    (i = 0 ∨ i = 5 ∨ i = 6 ∨ i = 26) →
    (oddTable 0 * qTable i) 0 = (qTable i * oddTable 0) 0 →
    (oddTable 0 * qTable i) 1 = (qTable i * oddTable 0) 1 → i = 0 := by
  apply allFin
  decide +kernel

/-- The first actual cubic word fixes only the identity in the radical center. -/
theorem center_fixed_eq_one (x : q₂) (hx : x ∈ center q₂)
    (ho : oddGenerator 0 * (x : Carrier) = (x : Carrier) * oddGenerator 0) : x = 1 := by
  obtain ⟨i, hi⟩ := exists_qElement x.property
  have h := congrArg inclusion ho
  rw [← hi, map_mul, map_mul, oddGenerator_inclusion, qElement_inclusion] at h
  have hi0 := center_fixed_check i (center_index hx hi)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) h)
    (congrArg (fun p : Equiv.Perm (Fin 100) => p 1) h)
  subst i
  exact Subtype.ext hi.symm

set_option maxRecDepth 100000 in
private theorem cubic_check : ∀ i : Fin 2, (oddTable i) ^ 3 = 1 := by
  apply allFin
  decide +kernel

/-- Both fixed normalizer words have cube one in the original carrier. -/
theorem oddGenerator_cube (i : Fin 2) : oddGenerator i ^ 3 = 1 := by
  apply inclusion_injective
  rw [map_pow, map_one, oddGenerator_inclusion]
  exact cubic_check i

private def commutatorWord : Fin 6 → List (Fin 12) :=
  ![[5, 4, 1], [6, 1], [3, 0], [8, 4], [5], [5, 4]]

private def radicalCommutator (k : Fin 12) : Carrier :=
  q₂Generator ⟨k.val % 6, Nat.mod_lt _ (by decide)⟩ *
    oddGenerator ⟨k.val / 6, by omega⟩ *
    (q₂Generator ⟨k.val % 6, Nat.mod_lt _ (by decide)⟩)⁻¹ *
    (oddGenerator ⟨k.val / 6, by omega⟩)⁻¹

private def commutatorTable (k : Fin 12) : Equiv.Perm (Fin 100) :=
  qGenTable ⟨k.val % 6, Nat.mod_lt _ (by decide)⟩ *
    oddTable ⟨k.val / 6, by omega⟩ *
    (qGenTable ⟨k.val % 6, Nat.mod_lt _ (by decide)⟩)⁻¹ *
    (oddTable ⟨k.val / 6, by omega⟩)⁻¹

set_option maxRecDepth 100000 in
private theorem commutator_word_check : ∀ i : Fin 6,
    qGenTable i = evalWord commutatorTable (commutatorWord i) := by
  apply allFin
  decide +kernel

private theorem q₂Generator_commutator_word (i : Fin 6) :
    q₂Generator i = evalWord radicalCommutator (commutatorWord i) := by
  have hw (w : List (Fin 12)) : inclusion (evalWord radicalCommutator w) =
      evalWord commutatorTable w := by
    induction w with
    | nil => rfl
    | cons k w ih =>
      rw [evalWord, map_mul, ih, evalWord]
      congr 1
      simp only [radicalCommutator, commutatorTable, map_mul, map_inv,
        q₂Generator_inclusion, oddGenerator_inclusion]
  apply inclusion_injective
  rw [q₂Generator_inclusion, hw]
  exact commutator_word_check i

/-- Each cubic word lies in the intrinsic two-residual of the inner normalizer. -/
theorem oddGenerator_mem_innerResidual (i : Fin 2) :
    (⟨oddGenerator i, oddGenerator_mem_p₂ i⟩ : p₂) ∈ pResidual 2 p₂ := by
  apply mem_pResidual_of_orderOf_coprime
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (Subtype.ext (oddGenerator_cube i)))

/-- The whole fixed radical lies in the actual embedded two-residual. -/
theorem q₂_le_innerResidual : q₂ ≤ (pResidual 2 p₂).map p₂.subtype := by
  let R := (pResidual 2 p₂).map p₂.subtype
  have hc (k : Fin 12) : radicalCommutator k ∈ R := by
    let g : p₂ := ⟨q₂Generator ⟨k.val % 6, Nat.mod_lt _ (by decide)⟩,
      q₂.le_normalizer (subset_closure ⟨_, rfl⟩)⟩
    let o : p₂ := ⟨oddGenerator ⟨k.val / 6, by omega⟩, oddGenerator_mem_p₂ _⟩
    have ho : o ∈ pResidual 2 p₂ := oddGenerator_mem_innerResidual _
    exact ⟨g * o * g⁻¹ * o⁻¹,
      (pResidual 2 p₂).mul_mem
        ((inferInstance : (pResidual 2 p₂).Normal).conj_mem o ho g)
        ((pResidual 2 p₂).inv_mem ho), rfl⟩
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [q₂Generator_commutator_word]
  have hw (w : List (Fin 12)) : evalWord radicalCommutator w ∈ R := by
    induction w with
    | nil => exact R.one_mem
    | cons k w ih => exact R.mul_mem (hc k) ih
  exact hw _

end Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
