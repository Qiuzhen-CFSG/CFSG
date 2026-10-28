module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceAction
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceDual

/-!
# The opposite marking and the source column normalizer

The involutory model automorphism fixing the distinguished transvection
interchanges the literal row and column groups and the two rectangular
groups. Composing the original full-centralizer marking with this
automorphism transports the row action and splitting to the actual column
subgroup in the original ambient group. The two fusion sets remain sets of
G-conjugates, so their 21-element counts are preserved.

This implements the symmetry in Aschbacher, *Sporadic Groups* (1994),
39.1(4), p.213, and the column version of 39.3, p.214. Together with the
row module it supplies both alternatives of 39.3, including relative
normality, literal quotient action and splitting. The 40.3 fusion argument
and the 41.1–41.4 generation/comparison remain separate source obligations.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
private theorem closure_map_le {A : Type*} [Group A] (e : MulAut A) (s t : Set A)
    (h : ∀ a ∈ s, e a ∈ closure t) : closure s ≤ (closure t).comap e.toMonoidHom :=
  (Subgroup.closure_le _).mpr h

private theorem swap_mem_iff {A : Type*} [Group A] (e : MulAut A) (P Q : Subgroup A)
    (he : ∀ a, e (e a) = a) (hPQ : P ≤ Q.comap e.toMonoidHom)
    (hQP : Q ≤ P.comap e.toMonoidHom) (a : A) : e a ∈ P ↔ a ∈ Q := by
  constructor
  · intro ha
    have hh := hPQ ha
    change e (e a) ∈ Q at hh
    rwa [he] at hh
  · intro ha
    exact hQP ha

private theorem modelDual_upper_le : upper ≤ upper.comap modelDual.toMonoidHom := by
  apply closure_map_le
  rintro _ ⟨i, j, hij, rfl⟩
  change modelDual (root hij) ∈ upper
  rw [modelDual_root]
  exact subset_closure ⟨j.rev, i.rev, Fin.rev_lt_rev.mpr hij, rfl⟩

/-- The symmetry preserves the same positive-root subgroup of the marked flag. -/
theorem modelDual_upper_iff (g : SL) : modelDual g ∈ upper ↔ g ∈ upper :=
  swap_mem_iff modelDual upper upper modelDual_square modelDual_upper_le modelDual_upper_le g

private theorem modelDual_column_le : Model.column ≤ Model.row.comap modelDual.toMonoidHom := by
  apply closure_map_le
  rintro _ ⟨i, hi, rfl⟩
  change modelDual (root hi) ∈ Model.row
  rw [modelDual_root]
  exact subset_closure ⟨i.rev, Fin.rev_lt_rev.mpr hi, rfl⟩

private theorem modelDual_row_le : Model.row ≤ Model.column.comap modelDual.toMonoidHom := by
  apply closure_map_le
  rintro _ ⟨j, hj, rfl⟩
  change modelDual (root hj) ∈ Model.column
  rw [modelDual_root]
  exact subset_closure ⟨j.rev, Fin.rev_lt_rev.mpr hj, rfl⟩

/-- The graph automorphism interchanges the literal root subgroups. -/
theorem modelDual_row_iff (g : SL) : modelDual g ∈ Model.row ↔ g ∈ Model.column :=
  swap_mem_iff modelDual Model.row Model.column modelDual_square
    modelDual_row_le modelDual_column_le g

/-- The reverse implication retains the same involutory model automorphism. -/
theorem modelDual_column_iff (g : SL) : modelDual g ∈ Model.column ↔ g ∈ Model.row := by
  have h := modelDual_row_iff (modelDual g)
  rw [modelDual_square] at h
  exact h.symm

private theorem modelDual_plane_le :
    Model.plane ≤ Model.threeSpace.comap modelDual.toMonoidHom := by
  apply closure_map_le
  rintro _ ⟨i, j, hij, hi, hj, rfl⟩
  change modelDual (root hij) ∈ Model.threeSpace
  rw [modelDual_root]
  refine subset_closure ⟨j.rev, i.rev, Fin.rev_lt_rev.mpr hij, ?_, ?_, rfl⟩
  · simp only [Fin.val_rev]; omega
  · simp only [Fin.val_rev]; omega

private theorem modelDual_threeSpace_le :
    Model.threeSpace ≤ Model.plane.comap modelDual.toMonoidHom := by
  apply closure_map_le
  rintro _ ⟨i, j, hij, hi, hj, rfl⟩
  change modelDual (root hij) ∈ Model.plane
  rw [modelDual_root]
  refine subset_closure ⟨j.rev, i.rev, Fin.rev_lt_rev.mpr hij, ?_, ?_, rfl⟩
  · simp only [Fin.val_rev]; omega
  · simp only [Fin.val_rev]; omega

/-- The same graph automorphism interchanges the two rectangular groups. -/
theorem modelDual_plane_iff (g : SL) :
    modelDual g ∈ Model.plane ↔ g ∈ Model.threeSpace := by
  constructor
  · intro hg
    have hh := modelDual_plane_le hg
    change modelDual (modelDual g) ∈ Model.threeSpace at hh
    rwa [modelDual_square] at hh
  · intro hg; exact modelDual_threeSpace_le hg

/-- The three-space and plane groups are interchanged in both directions. -/
theorem modelDual_threeSpace_iff (g : SL) :
    modelDual g ∈ Model.threeSpace ↔ g ∈ Model.plane := by
  have h := modelDual_plane_iff (modelDual g)
  rw [modelDual_square] at h
  exact h.symm

private theorem modelDual_centralizer (g : centralizer) : modelDual g ∈ centralizer := by
  apply mem_centralizer_singleton_iff.mpr
  calc
    modelDual (g : SL) * transvection = modelDual ((g : SL) * transvection) := by
      rw [map_mul, modelDual_point]
    _ = modelDual (transvection * (g : SL)) :=
      congrArg modelDual (mem_centralizer_singleton_iff.mp g.property)
    _ = transvection * modelDual (g : SL) := by rw [map_mul, modelDual_point]

private def dualCentralizer : MulAut centralizer where
  toFun g := ⟨modelDual g, modelDual_centralizer g⟩
  invFun g := ⟨modelDual g, modelDual_centralizer g⟩
  left_inv g := Subtype.ext (modelDual_square g)
  right_inv g := Subtype.ext (modelDual_square g)
  map_mul' g h := Subtype.ext (modelDual.map_mul g h)

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)
/-- The opposite marking uses the same full point centralizer. -/
def oppositeMarking : MarkedCentralizer z where
  equiv := F.equiv.trans dualCentralizer
  on_point := by change modelDual (F.equiv _ : SL) = transvection; rw [F.on_point, modelDual_point]

/-- The opposite row is exactly the original column, not merely an isomorphic subgroup. -/
theorem oppositeMarking_row : (oppositeMarking F).row = F.column := by
  ext x
  constructor
  · intro hx
    have hc := (oppositeMarking F).pullback_le Model.row hx
    apply (F.mem_pullback_iff Model.column ⟨x, hc⟩).mpr
    apply (modelDual_row_iff _).mp
    exact ((oppositeMarking F).mem_pullback_iff Model.row ⟨x, hc⟩).mp hx
  · intro hx
    have hc := F.pullback_le Model.column hx
    apply ((oppositeMarking F).mem_pullback_iff Model.row ⟨x, hc⟩).mpr
    exact (modelDual_row_iff _).mpr ((F.mem_pullback_iff Model.column ⟨x, hc⟩).mp hx)

/-- The opposite column is the original row. -/
theorem oppositeMarking_column : (oppositeMarking F).column = F.row := by
  ext x
  constructor
  · intro hx
    have hc := (oppositeMarking F).pullback_le Model.column hx
    apply (F.mem_pullback_iff Model.row ⟨x, hc⟩).mpr
    apply (modelDual_column_iff _).mp
    exact ((oppositeMarking F).mem_pullback_iff Model.column ⟨x, hc⟩).mp hx
  · intro hx
    have hc := F.pullback_le Model.row hx
    apply ((oppositeMarking F).mem_pullback_iff Model.column ⟨x, hc⟩).mpr
    exact (modelDual_column_iff _).mpr ((F.mem_pullback_iff Model.row ⟨x, hc⟩).mp hx)

/-- The opposite plane is the original three-space subgroup. -/
theorem oppositeMarking_plane : (oppositeMarking F).plane = F.threeSpace := by
  ext x
  constructor
  · intro hx
    have hc := (oppositeMarking F).pullback_le Model.plane hx
    apply (F.mem_pullback_iff Model.threeSpace ⟨x, hc⟩).mpr
    apply (modelDual_plane_iff _).mp
    exact ((oppositeMarking F).mem_pullback_iff Model.plane ⟨x, hc⟩).mp hx
  · intro hx
    have hc := F.pullback_le Model.threeSpace hx
    apply ((oppositeMarking F).mem_pullback_iff Model.plane ⟨x, hc⟩).mpr
    exact (modelDual_plane_iff _).mpr ((F.mem_pullback_iff Model.threeSpace ⟨x, hc⟩).mp hx)

/-- The opposite three-space is the original plane subgroup. -/
theorem oppositeMarking_threeSpace : (oppositeMarking F).threeSpace = F.plane := by
  ext x
  constructor
  · intro hx
    have hc := (oppositeMarking F).pullback_le Model.threeSpace hx
    apply (F.mem_pullback_iff Model.plane ⟨x, hc⟩).mpr
    apply (modelDual_threeSpace_iff _).mp
    exact ((oppositeMarking F).mem_pullback_iff Model.threeSpace ⟨x, hc⟩).mp hx
  · intro hx
    have hc := F.pullback_le Model.plane hx
    apply ((oppositeMarking F).mem_pullback_iff Model.threeSpace ⟨x, hc⟩).mpr
    exact (modelDual_threeSpace_iff _).mpr ((F.mem_pullback_iff Model.plane ⟨x, hc⟩).mp hx)

/-- Reversing the marking preserves the actual two fusion counts in G. -/
theorem oppositeMarking_linearFusion (hlinear : F.LinearFusion) :
    (oppositeMarking F).LinearFusion := by
  simpa only [MarkedCentralizer.LinearFusion, MarkedCentralizer.fusion,
    oppositeMarking_plane, oppositeMarking_threeSpace, and_comm] using hlinear

/-- The column is self-centralizing in the original ambient group. -/
theorem column_centralizer_eq : Subgroup.centralizer (F.column : Set G) = F.column := by
  simpa only [oppositeMarking_row] using row_centralizer_eq (oppositeMarking F)

/-- The point centralizer normalizes the original column subgroup. -/
theorem point_centralizer_le_column_normalizer :
    Subgroup.centralizer ({z} : Set G) ≤ normalizer (F.column : Set G) := by
  simpa only [oppositeMarking_row] using
    point_centralizer_le_row_normalizer (oppositeMarking F)

/-- Column normality is inside the full point centralizer. -/
theorem column_normal_in_point_centralizer :
    (F.column.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal := by
  simpa only [oppositeMarking_row] using
    row_normal_in_point_centralizer (oppositeMarking F)

/-- The column also has sixteen elements. -/
theorem column_card : Nat.card F.column = 16 := by
  simpa only [oppositeMarking_row] using row_card (oppositeMarking F)

/-- The actual column normalizer in the source group. -/
abbrev columnNormalizer := normalizer (F.column : Set G)

/-- The quotient uses column normality inside its own normalizer. -/
abbrev columnQuotient := columnNormalizer F ⧸ F.column.subgroupOf (columnNormalizer F)

/-- The column quotient acts by the original ambient conjugation. -/
def columnQuotientAction : columnQuotient F →* MulAut F.column :=
  QuotientGroup.lift _ F.column.normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker, column_centralizer_eq F])

/-- Self-centralization identifies the exact kernel of the column action. -/
theorem columnQuotientAction_injective : Function.Injective (columnQuotientAction F) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker, column_centralizer_eq F]

/-- The quotient map and action retain the literal conjugation formula. -/
theorem columnQuotientAction_mk_apply (g : columnNormalizer F) (x : F.column) :
    (columnQuotientAction F (QuotientGroup.mk g) x : G) =
      (g : G) * (x : G) * (g : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe F.column g x

/-- A column normalizer larger than the point centralizer has full action. -/
theorem column_action_surjective_of_normalizer_ne_centralizer
    (hne : normalizer (F.column : Set G) ≠ Subgroup.centralizer ({z} : Set G)) :
    Function.Surjective F.column.normalizerMonoidHom := by
  rw [← oppositeMarking_row F] at hne ⊢
  exact row_action_surjective_of_normalizer_ne_centralizer (oppositeMarking F) hne

/-- Source 39.1(2): the full point centralizer splits over its column. -/
theorem point_centralizer_splits_column :
    ∃ K : Subgroup (Subgroup.centralizer ({z} : Set G)),
      (F.column.subgroupOf (Subgroup.centralizer ({z} : Set G))).IsComplement' K := by
  rw [← oppositeMarking_row F]
  exact point_centralizer_splits_row (oppositeMarking F)

/-- The column extension splits in either alternative of source 39.3. -/
theorem column_normalizer_splits [Finite G] :
    ∃ K : Subgroup (normalizer (F.column : Set G)),
      (F.column.subgroupOf (normalizer (F.column : Set G))).IsComplement' K := by
  rw [← oppositeMarking_row F]
  exact row_normalizer_splits (oppositeMarking F)

/-- The other 21-element fusion count gives the dual source witness. -/
theorem linear_fusion_outside_column [Finite G] (hlinear : F.LinearFusion) :
    ∃ a : G, a ∈ F.threeSpace ∧ IsConj z a ∧
      a ∈ normalizer (F.column : Set G) ∧ a ∉ F.column := by
  simpa only [rowNormalizer, oppositeMarking_row, oppositeMarking_plane] using
    linear_fusion_outside_row (oppositeMarking F) (oppositeMarking_linearFusion F hlinear)

/-- The column version of source 39.3, in the literal normalizer and quotient. -/
theorem column_normalizer_structure [Finite G] :
    normalizer (F.column : Set G) = Subgroup.centralizer ({z} : Set G) ∨
      (Nonempty ((normalizer (F.column : Set G) ⧸
          F.column.subgroupOf (normalizer (F.column : Set G))) ≃*
        ((Fin 4 → ZMod 2) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))) ∧
        ∃ K : Subgroup (normalizer (F.column : Set G)),
          (F.column.subgroupOf (normalizer (F.column : Set G))).IsComplement' K) := by
  rw [← oppositeMarking_row F]
  exact row_normalizer_structure (oppositeMarking F)

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
