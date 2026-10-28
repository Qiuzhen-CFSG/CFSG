module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRow
import Mathlib.Tactic.FinCases

/-!
# The marked row intersections in the source normalizer geometry

Centralizing the four-group `row ∩ threeSpace` forces the bottom two
matrix rows to be identity rows, hence normalizes the three-space rectangle.
Transport through the full centralizer marking and weak closure then show
that the whole four-group normalizer preserves that rectangle. Consequently
its relative normalizer inside the row normalizer is the actual intersection
of the two full normalizers.

The existing marked row isomorphism therefore preserves both flag
intersections and their intersection, with its literal quotient map unchanged.
The final theorem applies these comparisons to the induction overgroup without
assuming that overgroup simple. This supplies the row-side intersection
alignment in Aschbacher, *Sporadic Groups* (1994), 41.4, printed p.222.
Agreement with the three-space map and global generation remain to be proved.

The two `import all` directives make this an implementation extension of the
row-coordinate and local-isomorphism modules: they prove the missing public
marking equation without exposing those implementation bodies to clients or
changing the high-fanout row module.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem centralizer_row_threeSpace_bottom (g : SL)
    (hg : g ∈ Subgroup.centralizer ((Model.row ⊓ Model.threeSpace : Subgroup SL) : Set SL))
    (i j : Fin 5) (hi : 3 ≤ i.val) : g i j = if i = j then 1 else 0 := by
  have hr (k : Fin 5) (hk : 3 ≤ k.val) : root (show 0 < k from by omega) * g =
      g * root (show 0 < k from by omega) :=
    mem_centralizer_iff.mp hg _ ⟨subset_closure ⟨k, by omega, rfl⟩,
      subset_closure ⟨0, k, by omega, by decide, hk, rfl⟩⟩
  have he (k : Fin 5) : g i k = if k = i then g 0 0 else 0 := by
    have hh := congrArg (fun a : SL => a 0 k) (hr i hi)
    change ((1 + Matrix.single 0 i 1) * g.val : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 k =
      (g.val * (1 + Matrix.single 0 i 1) : Matrix (Fin 5) (Fin 5) (ZMod 2)) 0 k at hh
    by_cases hk : k = i
    · subst k
      simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.add_apply, Matrix.single_mul_apply_same, Matrix.mul_single_apply_same,
        one_mul, mul_one, add_right_inj, ite_true] using hh
    · simpa only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
        Matrix.add_apply, Matrix.single_mul_apply_same,
        Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, one_mul, add_zero, add_eq_left,
        if_neg hk] using hh
  have h00 : g 0 0 = 1 := by
    apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
    intro hz
    apply g.det_ne_zero
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [he k, hz]
  simpa only [h00, eq_comm] using he j

private theorem centralizer_row_threeSpace_normalizes :
    Subgroup.centralizer ((Model.row ⊓ Model.threeSpace : Subgroup SL) : Set SL) ≤
      normalizer (Model.threeSpace : Set SL) := by
  apply le_normalizer_iff.mpr
  intro g hg
  change Model.threeSpace ≤ Model.threeSpace.comap (MulAut.conj g).toMonoidHom
  apply (closure_le _).mpr
  rintro _ ⟨i, j, hij, hi, hj, rfl⟩
  change g * root hij * g⁻¹ ∈ rectangle 3
  apply (RectangleCoordinates.mem3_iff _).mpr
  intro a b hab
  have hb : ∀ k : Fin 5, (g⁻¹) j k = if j = k then 1 else 0 :=
    fun k => centralizer_row_threeSpace_bottom g⁻¹
      ((Subgroup.centralizer _).inv_mem hg) j k hj
  have he : (g * root hij * g⁻¹).val =
      1 + g.val * Matrix.single i j 1 * (g⁻¹).val := by
    change g.val * (1 + Matrix.single i j 1) * (g⁻¹).val = _
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  rw [he, Matrix.add_apply, Matrix.one_apply]
  suffices (g.val * Matrix.single i j 1 * (g⁻¹).val : Matrix (Fin 5) (Fin 5) (ZMod 2)) a b = 0 by rw [this, add_zero]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k = j
  · subst k
    rw [Matrix.mul_single_apply_same, mul_one, hb]
    by_cases hjb : j = b
    · subst b
      have ha : 3 ≤ a.val := by omega
      rw [centralizer_row_threeSpace_bottom g hg a i ha, if_neg (by intro h; subst i; omega), zero_mul]
    · rw [if_neg hjb, mul_zero]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk, zero_mul]

variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

/-- The four-group centralizer normalizes the original three-space rectangle. -/
theorem source_row_threeSpace_centralizer_le_normalizer :
    Subgroup.centralizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) ≤
      normalizer (F.threeSpace : Set G) := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) :=
    mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hx z ⟨point_mem_row F, point_mem_threeSpace F⟩).symm
  let xc : Subgroup.centralizer ({z} : Set G) := ⟨x, hxC⟩
  have hm : (F.equiv xc : SL) ∈
      Subgroup.centralizer ((Model.row ⊓ Model.threeSpace : Subgroup SL) : Set SL) := by
    apply mem_centralizer_iff.mpr
    intro a ha
    change a ∈ Model.row ⊓ Model.threeSpace at ha
    let ac := F.equiv.symm ⟨a, Model.row_le_centralizer ha.1⟩
    have hrow : (ac : G) ∈ F.row := (F.mem_pullback_iff Model.row ac).mpr (by
      change (F.equiv (F.equiv.symm _) : SL) ∈ Model.row
      rw [F.equiv.apply_symm_apply]
      exact ha.1)
    have hthree : (ac : G) ∈ F.threeSpace := (F.mem_pullback_iff Model.threeSpace ac).mpr (by
      change (F.equiv (F.equiv.symm _) : SL) ∈ Model.threeSpace
      rw [F.equiv.apply_symm_apply]
      exact ha.2)
    have he : ac * xc = xc * ac := Subtype.ext (mem_centralizer_iff.mp hx ac ⟨hrow, hthree⟩)
    have hh := congrArg (fun c => (F.equiv c : SL)) he
    simpa only [map_mul, Subgroup.coe_mul, ac, F.equiv.apply_symm_apply] using hh
  have hn := centralizer_row_threeSpace_normalizes hm
  have hp : x ∈ F.pullback (centralizer ⊓ normalizer (Model.threeSpace : Set SL)) :=
    (F.mem_pullback_iff _ xc).mpr ⟨(F.equiv xc).property, hn⟩
  rw [F.pullback_relativeNormalizer Model.threeSpace Model.threeSpace_le_centralizer] at hp
  exact hp.2

variable [Finite G]

/-- Weak closure promotes centralizer control to the entire four-group normalizer. -/
theorem source_row_threeSpace_normalizer_le_threeSpace :
    normalizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) ≤
      normalizer (F.threeSpace : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply source_threeSpace_weakly_closed_in_normalizer F g
  have hAC : F.threeSpace ≤
      Subgroup.centralizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) := by
    let := marked_rectangle_elementary F 3
    exact F.threeSpace.le_centralizer.trans (centralizer_le inf_le_right)
  apply le_trans ?_ (source_row_threeSpace_centralizer_le_normalizer F)
  rintro _ ⟨a, ha, rfl⟩
  exact (mem_normalizer_iff.mp
    (normalizer_le_normalizer_centralizer (F.row ⊓ F.threeSpace) hg) a).mp (hAC ha)

/-- Inside the row normalizer, the four-group stabilizer is the actual three-space intersection. -/
theorem source_row_threeSpace_relative_normalizer :
    normalizer (((F.row ⊓ F.threeSpace).subgroupOf (rowNormalizer F)) :
      Set (rowNormalizer F)) = (normalizer (F.threeSpace : Set G)).subgroupOf (rowNormalizer F) := by
  rw [← subgroupOf_normalizer_eq (show F.row ⊓ F.threeSpace ≤ rowNormalizer F from
    inf_le_left.trans F.row.le_normalizer)]
  apply le_antisymm
  · exact fun g hg => source_row_threeSpace_normalizer_le_threeSpace F hg
  · intro g hg
    exact inf_normalizer_le_normalizer_inf ⟨g.property, hg⟩


/-- The corresponding relative normalizer for the marked eight-group. -/
theorem source_row_plane_relative_normalizer :
    normalizer (((F.row ⊓ F.plane).subgroupOf (rowNormalizer F)) :
      Set (rowNormalizer F)) = (sourcePlaneNormalizer F).subgroupOf (rowNormalizer F) := by
  rw [← subgroupOf_normalizer_eq (show F.row ⊓ F.plane ≤ rowNormalizer F from
    inf_le_left.trans F.row.le_normalizer), source_row_plane_normalizer]
  ext g
  exact and_iff_right g.property

variable {G' : Type*} [Group G'] {z' : G'} (F' : MarkedCentralizer z')

omit [Finite G] in
/-- The row-coordinate comparison is exactly the original full-centralizer marking. -/
theorem rowMarkingEquiv_model (a : F.row) :
    F'.pullbackEquiv Model.row Model.row_le_centralizer (rowMarkingEquiv F F' a) =
      F.pullbackEquiv Model.row Model.row_le_centralizer a := by
  apply modelRowCoordinates.injective
  change rowCoordinates F' (rowMarkingEquiv F F' a) = rowCoordinates F a
  exact (rowCoordinates F').apply_symm_apply _

omit [Finite G] in
/-- The row comparison preserves every subgroup selected by the same model marking. -/
theorem rowMarkingEquiv_mem_pullback (A : Subgroup SL) (a : F.row) :
    (rowMarkingEquiv F F' a : G') ∈ F'.pullback A ↔ (a : G) ∈ F.pullback A := by
  rw [F'.mem_pullback_iff A ⟨rowMarkingEquiv F F' a,
    F'.pullback_le Model.row (rowMarkingEquiv F F' a).property⟩,
    F.mem_pullback_iff A ⟨a, F.pullback_le Model.row a.property⟩]
  change (F'.pullbackEquiv Model.row Model.row_le_centralizer
    (rowMarkingEquiv F F' a) : SL) ∈ A ↔
      (F.pullbackEquiv Model.row Model.row_le_centralizer a : SL) ∈ A
  rw [rowMarkingEquiv_model]

omit [Finite G] in
private theorem row_normalizer_equiv_marked_inf
    (e : rowNormalizer F ≃* rowNormalizer F')
    (he : ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
      inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) (A : Subgroup SL) :
    ((F.row ⊓ F.pullback A).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (F'.row ⊓ F'.pullback A).subgroupOf (rowNormalizer F') := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hx' : (x : G) ∈ F.row ∧ (x : G) ∈ F.pullback A := hx
    have hh := he ⟨x, hx'.1⟩
    change e x = _ at hh
    change ((e x : rowNormalizer F') : G') ∈ F'.row ⊓ F'.pullback A
    rw [hh]
    exact ⟨(rowMarkingEquiv F F' ⟨x, hx'.1⟩).property,
      (rowMarkingEquiv_mem_pullback F F' A _).mpr hx'.2⟩
  · intro y hy
    have hy' : (y : G') ∈ F'.row ∧ (y : G') ∈ F'.pullback A := hy
    let a := (rowMarkingEquiv F F').symm ⟨y, hy'.1⟩
    have ha : (a : G) ∈ F.pullback A := (rowMarkingEquiv_mem_pullback F F' A a).mp
      (by rw [(rowMarkingEquiv F F').apply_symm_apply]; exact hy'.2)
    refine ⟨inclusion F.row.le_normalizer a, ⟨a.property, ha⟩, ?_⟩
    change e (inclusion F.row.le_normalizer a) = y
    rw [he]
    exact congrArg (inclusion F'.row.le_normalizer)
      ((rowMarkingEquiv F F').apply_symm_apply ⟨y, hy'.1⟩)

variable [Finite G']

theorem row_normalizer_equiv_threeSpace_intersection
    (e : rowNormalizer F ≃* rowNormalizer F')
    (he : ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
      inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) :
    ((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F') := by
  rw [← source_row_threeSpace_relative_normalizer F, map_equiv_normalizer_eq,
    row_normalizer_equiv_marked_inf F F' e he Model.threeSpace,
    source_row_threeSpace_relative_normalizer F']


theorem row_normalizer_equiv_plane_intersection
    (e : rowNormalizer F ≃* rowNormalizer F')
    (he : ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
      inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) :
    ((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
      (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F') := by
  rw [← source_row_plane_relative_normalizer F, map_equiv_normalizer_eq,
    row_normalizer_equiv_marked_inf F F' e he Model.plane,
    source_row_plane_relative_normalizer F']

theorem row_normalizer_equiv_flag_intersection
    (e : rowNormalizer F ≃* rowNormalizer F')
    (he : ∀ a : F.row, e (inclusion F.row.le_normalizer a) =
      inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) :
    (((sourcePlaneNormalizer F) ⊓ (sourceThreeSpaceNormalizer F)).subgroupOf
        (rowNormalizer F)).map e.toMonoidHom =
      ((sourcePlaneNormalizer F') ⊓ (sourceThreeSpaceNormalizer F')).subgroupOf
        (rowNormalizer F') := by
  simp only [subgroupOf, comap_inf, map_inf _ _ e.toMonoidHom e.injective]
  exact congrArg₂ (· ⊓ ·) (row_normalizer_equiv_plane_intersection F F' e he)
    (row_normalizer_equiv_threeSpace_intersection F F' e he)

/-- The source row comparison, with both flag intersections and its literal quotient map. -/
theorem exists_row_normalizer_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) ∧
      ((sourcePlaneNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((sourceThreeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F') ∧
      ∀ n, (QuotientGroup.mk (e n) : rowQuotient F') =
        ((linearRowQuotientEquiv F h).trans (linearRowQuotientEquiv F' h').symm)
          (QuotientGroup.mk n) := by
  obtain ⟨e, he, hq⟩ := exists_row_normalizer_equiv F F' h h'
  exact ⟨e, he, row_normalizer_equiv_plane_intersection F F' e he,
    row_normalizer_equiv_threeSpace_intersection F F' e he, hq⟩

/-- Apply the intersection alignment to the source 41.1 induction overgroup. -/
theorem normalizerSpan_row_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : rowNormalizer (normalizerSpanMarking F) ≃* rowNormalizer F',
      ((sourcePlaneNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (sourcePlaneNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((sourceThreeSpaceNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (sourceThreeSpaceNormalizer F').subgroupOf (rowNormalizer F') := by
  obtain ⟨e, _, heP, heA, _⟩ := exists_row_normalizer_flag_equiv
    (normalizerSpanMarking F) F' (normalizerSpan_linearFusion F h) h'
  exact ⟨e, heP, heA⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
