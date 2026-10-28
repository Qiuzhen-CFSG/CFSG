module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorGeometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.DoubleCosetCover.SectorOrbits.Data

/-!
# A finite certificate for Rudvalis sector coverage

Each row encodes a 28-point set, two standard-generator successors, and an
edge towards one of the 76 sector roots. Equality of bitmaps certifies equality
of the actual finite sets; the maps are the previously proved point actions.
Strictly decreasing parent indices give candidate-orbit membership by induction.
Closure under the two standard generators preserves the whole finite family,
so their generation of the actual model puts every seed translate in it.

`cover_of_checks` is conditional on the two exhaustive table checks. Those
premises must be discharged before asserting coverage. Neither distinctness
of the rows, the exact orbit cardinality, nor a stabilizer identification is
needed. The root comparison uses the inverse sector words, preserving the
GAP-right/Lean-left convention of `SectorGeometry`.

Source application: Aschbacher--Smith, printed p.511 (PDF p.528), citing
Aschbacher (1986), no.343. The untrusted witness producer is `source/Generate.py`.
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SectorOrbitCertificate
open Representatives RadicalCoverage.SylowCertificate
open scoped Pointwise

@[expose] public def points : Nat → Nat → List (Fin 4060)
  | 0, _ => []
  | n + 1, q => ⟨q % 4096 % 4060, Nat.mod_lt _ (by decide)⟩ :: points n (q >>> 12)

@[expose] public def bitmap : List (Fin 4060) → Nat
  | [] => 0
  | x :: xs => (1 <<< x.val) ||| bitmap xs

@[expose] public def mapped (f : Fin 4060 → Fin 4060) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, q =>
    (1 <<< (f ⟨q % 4096 % 4060, Nat.mod_lt _ (by decide)⟩).val) |||
      mapped f n (q >>> 12)

@[expose] public def family (i : Fin 424125) : Finset (Fin 4060) :=
  (points 28 (pointCode i.val)).toFinset

@[expose] public def nextA (i : Nat) : Fin 424125 :=
  ⟨((row i >>> 336) % 524288) % 424125, Nat.mod_lt _ (by decide)⟩

@[expose] public def nextB (i : Nat) : Fin 424125 :=
  ⟨((row i >>> 355) % 524288) % 424125, Nat.mod_lt _ (by decide)⟩

@[expose] public def parent (i : Nat) : Fin 424125 :=
  ⟨((row i >>> 374) % 524288) % 424125, Nat.mod_lt _ (by decide)⟩

@[expose] public def edge (i : Nat) : Fin 14 :=
  ⟨((row i >>> 393) % 16) % 14, Nat.mod_lt _ (by decide)⟩

@[expose] public def closureCheck (i : Nat) : Bool :=
  (mapped Rudvalis.Data.aMap 28 (pointCode i) == mapped id 28 (pointCode (nextA i).val)) &&
  (mapped Rudvalis.Data.bMap 28 (pointCode i) == mapped id 28 (pointCode (nextB i).val))

@[expose] public def forestCheck (i : Nat) : Bool :=
  decide (i < 76) || (decide ((parent i).val < i) &&
    (mapped (LocalOrder.generatorMap (edge i)) 28 (pointCode i) ==
      mapped id 28 (pointCode (parent i).val)))

public theorem bitmap_mem (l : List (Fin 4060)) (x : Fin 4060) :
    (bitmap l).testBit x.val = true ↔ x ∈ l := by
  induction l with
  | nil => simp [bitmap]
  | cons y l ih =>
    simp only [bitmap, Nat.testBit_or, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons,
      Fin.val_inj, ih]
    exact or_congr eq_comm Iff.rfl

public theorem bitmap_eq (l k : List (Fin 4060)) (h : bitmap l = bitmap k) :
    l.toFinset = k.toFinset := by
  ext x
  simp only [List.mem_toFinset, ← bitmap_mem, h]

public theorem mapped_eq (f : Fin 4060 → Fin 4060) (n q : Nat) :
    mapped f n q = bitmap ((points n q).map f) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih => simp only [mapped, points, List.map_cons, bitmap, ih]

public theorem image_eq_of_mapped_eq (f : Fin 4060 → Fin 4060) (i j : Fin 424125)
    (h : mapped f 28 (pointCode i.val) = mapped id 28 (pointCode j.val)) :
    (family i).image f = family j := by
  rw [mapped_eq, mapped_eq, List.map_id] at h
  have he := bitmap_eq _ _ h
  change ((points 28 (pointCode i.val)).toFinset.image f) = (points 28 (pointCode j.val)).toFinset
  rw [← he]
  ext x
  simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]

public theorem closureCheck_sound (i : Fin 424125) (h : closureCheck i.val = true) :
    a • family i = family (nextA i.val) ∧ b • family i = family (nextB i.val) := by
  simp only [closureCheck, Bool.and_eq_true, beq_iff_eq] at h
  constructor
  · rw [← Finset.image_smul]
    exact image_eq_of_mapped_eq Rudvalis.Data.aMap i _ h.1
  · rw [← Finset.image_smul]
    exact image_eq_of_mapped_eq Rudvalis.Data.bMap i _ h.2

public theorem forestCheck_sound (i : Fin 424125) (hi : 76 ≤ i.val)
    (h : forestCheck i.val = true) :
    (parent i.val).val < i.val ∧
      candidateGenerator (edge i.val) • family i = family (parent i.val) := by
  simp only [forestCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  obtain ⟨hlt, heq⟩ := h.resolve_left (by omega)
  refine ⟨hlt, ?_⟩
  rw [← Finset.image_smul]
  simp only [LocalOrder.generator_smul]
  exact image_eq_of_mapped_eq _ i _ heq

set_option maxRecDepth 2000 in
set_option maxHeartbeats 1600000 in
public theorem roots_eq : ∀ s : Fin 76, family ⟨s.val, by omega⟩ = sectorSet s := by
  apply OrderCertificate.allFin
  decide +kernel

public theorem seed_eq : family 0 = seed := by decide +kernel

public theorem family_sector (hf : ∀ i : Fin 424125, forestCheck i.val = true)
    (i : Fin 424125) : ∃ s p, p ∈ candidate ∧ family i = p • sectorSet s := by
  have h (k : Nat) : ∀ hk : k < 424125,
      ∃ s p, p ∈ candidate ∧ family ⟨k, hk⟩ = p • sectorSet s := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      by_cases hroot : k < 76
      · exact ⟨⟨k, hroot⟩, 1, candidate.one_mem, (roots_eq ⟨k, hroot⟩).trans
          (one_smul Model _).symm⟩
      · have he := forestCheck_sound ⟨k, hk⟩ (Nat.le_of_not_gt hroot) (hf ⟨k, hk⟩)
        obtain ⟨s, p, hp, heq⟩ := ih _ he.1 (parent k).isLt
        refine ⟨s, (candidateGenerator (edge k))⁻¹ * p,
          candidate.mul_mem (candidate.inv_mem
            (Subgroup.subset_closure (Set.mem_range_self (edge k)))) hp, ?_⟩
        rw [mul_smul, ← heq, ← he.2, inv_smul_smul]
  exact h i.val i.isLt

public theorem closure_family
    (ha : ∀ i, ∃ j, a • family i = family j)
    (hb : ∀ i, ∃ j, b • family i = family j) :
    ∀ x : Model, ∀ i, ∃ j, x • family i = family j := by
  let Q := Finset.univ.image family
  have memQ (i) : family i ∈ Q := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have fix (g : Model) (hg : ∀ i, ∃ j, g • family i = family j) :
      g ∈ MulAction.stabilizer Model Q := by
    change g • Q = Q
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_smul_finset.mp hs
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨j, hj⟩ := hg i
      rw [hj]
      exact memQ j
    · simp
  have ht := eq_top_of_a_mem_of_b_mem (MulAction.stabilizer Model Q)
    (fix a ha) (fix b hb)
  intro x i
  have hx : x • Q = Q := (MulAction.mem_stabilizer_iff).mp (ht.symm ▸ Subgroup.mem_top x)
  have hmem : x • family i ∈ Q := by
    rw [← hx]
    exact Finset.smul_mem_smul_finset (memQ i)
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  exact ⟨j, hj.symm⟩

public theorem cover_of_checks
    (hc : ∀ i : Fin 424125, closureCheck i.val = true)
    (hf : ∀ i : Fin 424125, forestCheck i.val = true) :
    ∀ x : Model, ∃ (s : Fin 76) (n : Fin 16384), x • seed = normalTranslate s n := by
  intro x
  obtain ⟨j, hj⟩ := closure_family
    (fun i => ⟨nextA i.val, (closureCheck_sound i (hc i)).1⟩)
    (fun i => ⟨nextB i.val, (closureCheck_sound i (hc i)).2⟩) x 0
  rw [seed_eq] at hj
  obtain ⟨s, p, hp, he⟩ := family_sector hf j
  refine ⟨s, (exists_normalTranslate_iff _ s).mpr ?_⟩
  exact ⟨p, hp, hj.trans (he.trans (congrArg (p • ·) (sectorSet_eq s)))⟩

end Rudvalis.SylowOvergroups.TwoCore.Generation.DoubleCosetCover.SectorOrbitCertificate
