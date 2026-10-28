module

public import Theory.Mathieu.M23.QuasithinGeometry.Design
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Combinatorics.Configuration
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Coordinates for the M23 pair-derived plane

Deleting the pair `{11,17}` from its containing certified Witt heptads gives
exactly the orthogonality plane over the field of four elements. The explicit
point and line tables below retain the ambient `Fin 23` labels and the heptad
certificate indices, so they also give concrete coordinates for transporting
the stabilizer action.

We calculate in the quadratic field `F₂[a]` with `a² = a + 1`. Kernel-checked
finite certificates verify nonzero, distinct projective representatives,
exhaustion of the heptads through the pair, and the full incidence table.
Finite-field uniqueness transports the coefficients to `GaloisField 2 2`;
the projective cardinality formula proves that the 21 representatives exhaust
that target. No uniqueness theorem for abstract planes is used.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, §5.2,
PDF pp.672–674; Aschbacher, *Sporadic Groups*, §18. The coordinate tables are
computed from this project's certified `m23BlockMaskArray`.
-/

@[expose] public section
namespace Sporadic.Mathieu.M23Geometry.PairPlaneCoordinates

/-- A computable realization of the field with four elements. -/
abbrev Four := QuadraticAlgebra (ZMod 2) 1 1
instance fourNoRoot : Fact (∀ r : ZMod 2, r ^ 2 ≠ 1 + 1 * r) := ⟨by decide +kernel⟩
instance fourFintype : Fintype Four :=
  Fintype.ofEquiv (ZMod 2 × ZMod 2) (QuadraticAlgebra.equivProd 1 1).symm

theorem card_four : Fintype.card Four = 4 := by decide +kernel

/-- Identification with the field in the canonical target plane. -/
noncomputable def fieldEquiv : Four ≃+* GaloisField 2 2 := by
  letI := Fintype.ofFinite (GaloisField 2 2)
  apply FiniteField.ringEquivOfCardEq
  rw [card_four, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by decide)]
  norm_num

/-- The quadratic generator, satisfying `a² = a + 1`. -/
def a : Four := ⟨0, 1⟩

/-- Normalized projective representatives: `[1,u,v]`, `[0,1,u]`, and `[0,0,1]`. -/
def vector : Fin 21 → Fin 3 → Four :=
  ![![1, 0, 0],
    ![1, 0, 1],
    ![1, 0, a],
    ![1, 0, a + 1],
    ![1, 1, 0],
    ![1, 1, 1],
    ![1, 1, a],
    ![1, 1, a + 1],
    ![1, a, 0],
    ![1, a, 1],
    ![1, a, a],
    ![1, a, a + 1],
    ![1, a + 1, 0],
    ![1, a + 1, 1],
    ![1, a + 1, a],
    ![1, a + 1, a + 1],
    ![0, 1, 0],
    ![0, 1, 1],
    ![0, 1, a],
    ![0, 1, a + 1],
    ![0, 0, 1]]

/-- The ambient Witt-design point attached to each coordinate row. -/
def pointLabel : Fin 21 → Fin 23 :=
  ![0, 1, 8, 16, 3, 7, 12, 13, 19, 20, 22, 5, 10, 6, 4, 15, 14, 2, 18, 9, 21]

/-- Heptad certificate indices, in dual coordinate order. -/
def blockIndex : Fin 21 → Fin 253 :=
  ![127, 58, 217, 194, 162, 0, 156, 166, 186, 74, 130, 208, 218, 71, 190, 116, 69, 123, 197, 205, 171]

/-- The five ambient points on each dual coordinate row. -/
def lineSet : Fin 21 → Finset (Fin 23) :=
  ![{2, 9, 14, 18, 21},
    {1, 6, 7, 14, 20},
    {5, 13, 14, 15, 16},
    {4, 8, 12, 14, 22},
    {3, 7, 12, 13, 21},
    {1, 2, 3, 4, 5},
    {3, 6, 9, 16, 22},
    {3, 8, 15, 18, 20},
    {4, 6, 10, 15, 21},
    {1, 10, 13, 18, 22},
    {2, 10, 12, 16, 20},
    {5, 7, 8, 9, 10},
    {5, 19, 20, 21, 22},
    {1, 9, 12, 15, 19},
    {4, 7, 16, 18, 19},
    {2, 6, 8, 13, 19},
    {0, 1, 8, 16, 21},
    {0, 2, 7, 15, 22},
    {0, 4, 9, 13, 20},
    {0, 5, 6, 12, 18},
    {0, 3, 10, 14, 19}]

section Certificates

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem vector_ne_zero : ∀ i, vector i ≠ 0 := by decide +kernel

theorem vector_separates : ∀ (i j : Fin 21) (c : Four),
    c • vector j = vector i → i = j := by decide +kernel

theorem pointLabel_mem : ∀ i, pointLabel i ∈ pairComplement x.val := by decide +kernel

theorem pointLabel_injective : Function.Injective pointLabel := by decide +kernel

theorem blockIndex_contains : ∀ i, x.val ⊆ m23BlockAt (blockIndex i) := by decide +kernel

theorem blockIndex_complete : ∀ b : Fin 253, x.val ⊆ m23BlockAt b →
    ∃ i, blockIndex i = b := by decide +kernel

theorem lineSet_eq : ∀ i, lineSet i = m23BlockAt (blockIndex i) \ x.val := by decide +kernel

theorem lineSet_injective : Function.Injective lineSet := by decide +kernel

theorem incidence_table : ∀ i j, vector i ⬝ᵥ vector j = 0 ↔ pointLabel i ∈ lineSet j := by
  decide +kernel

end Certificates

/-- The canonical field plane, with orthogonality incidence. -/
abbrev PG := Projectivization (GaloisField 2 2) (Fin 3 → GaloisField 2 2)

/-- The normalized coordinate rows transported coefficient by coefficient. -/
noncomputable def fieldVector (i : Fin 21) : Fin 3 → GaloisField 2 2 :=
  fieldEquiv ∘ vector i

theorem fieldVector_ne_zero (i : Fin 21) : fieldVector i ≠ 0 := by
  intro h
  apply vector_ne_zero i
  funext k
  apply fieldEquiv.injective
  simpa [fieldVector] using congrFun h k

/-- The projective class of a transported coordinate row. -/
noncomputable def projectivePoint (i : Fin 21) : PG :=
  Projectivization.mk _ (fieldVector i) (fieldVector_ne_zero i)

theorem projectivePoint_injective : Function.Injective projectivePoint := by
  intro i j h
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' _ _ _ _ _).mp h
  apply vector_separates i j (fieldEquiv.symm c)
  funext k
  apply fieldEquiv.injective
  simpa [fieldVector, Pi.smul_apply, smul_eq_mul] using congrFun hc k

theorem card_pg : Nat.card PG = 21 := by
  rw [Projectivization.card'']
  norm_num [Nat.card_fun, GaloisField.card 2 2 (by decide)]

/-- The 21 normalized coordinate vectors enumerate the projective plane. -/
noncomputable def projectiveEquiv : Fin 21 ≃ PG :=
  Equiv.ofBijective projectivePoint
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨projectivePoint_injective, by simp [card_pg]⟩)

theorem projective_incident (i j : Fin 21) :
    projectiveEquiv i ∈ projectiveEquiv j ↔ pointLabel i ∈ lineSet j := by
  change projectivePoint i ∈ projectivePoint j ↔ _
  rw [Configuration.ofField.mem_iff, projectivePoint, projectivePoint,
    Projectivization.orthogonal_mk]
  change (fieldEquiv.toRingHom ∘ vector i) ⬝ᵥ (fieldEquiv.toRingHom ∘ vector j) = 0 ↔ _
  rw [← fieldEquiv.toRingHom.map_dotProduct]
  exact fieldEquiv.map_eq_zero_iff.trans (incidence_table i j)

/-- Labels retaining the actual ambient points of the Witt design. -/
def labeledPoint (i : Fin 21) : pairComplement x.val :=
  ⟨pointLabel i, pointLabel_mem i⟩

theorem labeledPoint_bijective : Function.Bijective labeledPoint := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j h
    exact pointLabel_injective (congrArg Subtype.val h)
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp only [Fintype.card_fin, Fintype.card_coe]
    exact (pairComplement_card x.property).symm

/-- The coordinate row index is an explicit enumeration of the complement. -/
noncomputable def pointLabelEquiv : Fin 21 ≃ pairComplement x.val :=
  Equiv.ofBijective labeledPoint labeledPoint_bijective

theorem lineSet_mem (i : Fin 21) : lineSet i ∈ pairLines x.val := by
  apply mem_pairLines.mpr
  refine ⟨m23BlockAt (blockIndex i), ?_, blockIndex_contains i, (lineSet_eq i).symm⟩
  exact Finset.mem_image.mpr ⟨blockIndex i, Finset.mem_univ _, rfl⟩

/-- Labels retaining the actual five-element derived lines. -/
noncomputable def labeledLine (i : Fin 21) : pairLines x.val :=
  ⟨lineSet i, lineSet_mem i⟩

theorem labeledLine_bijective : Function.Bijective labeledLine := by
  constructor
  · intro i j h
    exact lineSet_injective (congrArg Subtype.val h)
  · intro l
    obtain ⟨B, hB, hPB, hBl⟩ := mem_pairLines.mp l.property
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨i, hi⟩ := blockIndex_complete b hPB
    refine ⟨i, Subtype.ext ?_⟩
    change lineSet i = l.val
    rw [lineSet_eq, hi, hBl]

/-- The dual coordinate row index enumerates precisely the derived lines. -/
noncomputable def lineLabelEquiv : Fin 21 ≃ pairLines x.val :=
  Equiv.ofBijective labeledLine labeledLine_bijective

/-- Explicit coordinates of the 21 ambient points complementary to `{11,17}`. -/
noncomputable def pointEquiv : pairComplement x.val ≃ PG :=
  pointLabelEquiv.symm.trans projectiveEquiv

/-- Explicit dual coordinates of the 21 heptads through `{11,17}`, with that pair deleted. -/
noncomputable def lineEquiv : pairLines x.val ≃ PG :=
  lineLabelEquiv.symm.trans projectiveEquiv

@[simp] theorem pointEquiv_labeledPoint (i : Fin 21) :
    pointEquiv (labeledPoint i) = projectivePoint i :=
  projectiveEquiv.congr_arg (pointLabelEquiv.symm_apply_apply i)

@[simp] theorem lineEquiv_labeledLine (i : Fin 21) :
    lineEquiv (labeledLine i) = projectivePoint i :=
  projectiveEquiv.congr_arg (lineLabelEquiv.symm_apply_apply i)

/-- The concrete pair-derived design has precisely the canonical field-plane incidence. -/
theorem incident_iff (p : pairComplement x.val) (l : pairLines x.val) :
    pointEquiv p ∈ lineEquiv l ↔ p.val ∈ l.val := by
  obtain ⟨i, rfl⟩ := pointLabelEquiv.surjective p
  obtain ⟨j, rfl⟩ := lineLabelEquiv.surjective l
  change pointEquiv (labeledPoint i) ∈ lineEquiv (labeledLine j) ↔ _
  rw [pointEquiv_labeledPoint, lineEquiv_labeledLine]
  exact projective_incident i j

end Sporadic.Mathieu.M23Geometry.PairPlaneCoordinates
