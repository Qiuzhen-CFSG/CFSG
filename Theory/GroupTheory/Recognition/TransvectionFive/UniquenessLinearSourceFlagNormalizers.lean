module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRowFlags
public import Mathlib.Algebra.Module.ZMod

/-!
# The ambient row–three-space intersection normalizer

The full row action realizes every automorphism of its binary four-space.
Extend an automorphism of any row subspace to prove transitivity on that
subspace's nonidentity elements. For the marked four-group
`row ∩ threeSpace`, an element normalizing it can therefore be multiplied
by a row-normalizer element to centralize the distinguished involution.
Its full centralizer already normalizes the row. Combined with the proved
three-space control, this identifies the full four-group normalizer with
the intersection of the original ambient normalizers.

This is the source flag-intersection identification needed on the local-group
side of Aschbacher, *Sporadic Groups* (1994), 41.4, printed p.222. No
simplicity of the normalizer-generated subgroup or ambient isomorphism is used.

The opposite marking gives the column–plane equality. The marked plane
isomorphism preserves that intersection, and transport back through the
opposite marking supplies a three-space isomorphism preserving its actual
row-normalizer intersection. The final theorem discharges these local
comparison premises for the 41.1 induction overgroup. Agreement between the
row and three-space maps on their common subgroup remains a separate proof.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear

private theorem subspace_nonzero_transitive {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b : V) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ f : V ≃ₗ[ZMod 2] V, f a = b := by
  let ea := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V a ha
  let eb := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V b hb
  obtain ⟨f, hf⟩ := Submodule.exists_linearEquiv_restrict_eq (ea.symm.trans eb)
  refine ⟨f, ?_⟩
  have h := hf (ea 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ea, eb] using h.symm

private theorem subgroup_nonzero_transitive (A : Subgroup (Multiplicative (Fin 4 → ZMod 2)))
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ f : MulAut (Multiplicative (Fin 4 → ZMod 2)),
      (∀ x, f x ∈ A ↔ x ∈ A) ∧ f a = b := by
  let D : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
    AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm A)
  let a' : D := ⟨(a : Multiplicative (Fin 4 → ZMod 2)).toAdd, a.property⟩
  let b' : D := ⟨(b : Multiplicative (Fin 4 → ZMod 2)).toAdd, b.property⟩
  have ha' : a' ≠ 0 := by intro he; exact ha (Subtype.ext (congrArg Subtype.val he))
  have hb' : b' ≠ 0 := by intro he; exact hb (Subtype.ext (congrArg Subtype.val he))
  obtain ⟨f, hf⟩ := subspace_nonzero_transitive a' b' ha' hb'
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have hmem (x : Fin 4 → ZMod 2) : g x ∈ D ↔ x ∈ D := by
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := f.surjective ⟨g x, hx⟩
      have he : (y : Fin 4 → ZMod 2) = x := g.injective ((hg y).symm.trans (congrArg Subtype.val hy))
      exact he ▸ y.property
    · intro hx
      rw [← hg ⟨x, hx⟩]
      exact (f ⟨x, hx⟩).property
  refine ⟨g.toAddEquiv.toMultiplicative, hmem, ?_⟩
  exact (hg a').symm.trans (congrArg Subtype.val hf)


variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- The stabilizer of any row subgroup is transitive on its nonidentity elements. -/
theorem row_subgroup_nonidentity_transitive (h : F.LinearFusion) (D : Subgroup G)
    (hD : D ≤ F.row) (a b : D) (ha : a ≠ 1) (hb : b ≠ 1) :
    ∃ n ∈ rowNormalizer F, n ∈ normalizer (D : Set G) ∧ n * a * n⁻¹ = b := by
  let A := D.subgroupOf F.row
  let c := rowCoordinates F
  let e := A.equivMapOfInjective c.toMonoidHom c.injective
  let a' : A := ⟨⟨a, hD a.property⟩, a.property⟩
  let b' : A := ⟨⟨b, hD b.property⟩, b.property⟩
  have ha' : e a' ≠ 1 := by
    intro he
    have he' : a' = 1 := e.map_eq_one_iff.mp he
    exact ha (Subtype.ext (congrArg (fun x : A => ((x : F.row) : G)) he'))
  have hb' : e b' ≠ 1 := by
    intro he
    have he' : b' = 1 := e.map_eq_one_iff.mp he
    exact hb (Subtype.ext (congrArg (fun x : A => ((x : F.row) : G)) he'))
  obtain ⟨f, hf, hfab⟩ := subgroup_nonzero_transitive (A.map c.toMonoidHom)
    (e a') (e b') ha' hb'
  let α : MulAut F.row := MulAut.congr c.symm f
  obtain ⟨n, hn⟩ := row_action_surjective_of_normalizer_ne_centralizer F
    (linear_rowNormalizer_ne_centralizer F h) α
  have hα (x : F.row) : α x ∈ A ↔ x ∈ A := by
    have hh := hf (c x)
    rw [mem_map_equiv, mem_map_equiv, c.symm_apply_apply] at hh
    exact hh
  refine ⟨n, n.property, ?_, ?_⟩
  · apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj (n : G)).injective])
    rintro _ ⟨x, hx, rfl⟩
    have ha : α ⟨x, hD hx⟩ ∈ A := (hα _).mpr hx
    rw [← hn] at ha
    exact ha
  · have he := hfab
    have he' : α (a' : F.row) = (b' : F.row) := by
      apply c.injective
      change c (c.symm (f (c (a' : F.row)))) = c (b' : F.row)
      rw [c.apply_symm_apply]
      exact he
    rw [← hn] at he'
    exact congrArg Subtype.val he'

/-- The full ambient normalizer of the marked four-group preserves both original factors. -/
theorem source_row_threeSpace_normalizer (h : F.LinearFusion) :
    normalizer ((F.row ⊓ F.threeSpace : Subgroup G) : Set G) =
      rowNormalizer F ⊓ sourceThreeSpaceNormalizer F := by
  apply le_antisymm ?_ inf_normalizer_le_normalizer_inf
  intro g hg
  refine ⟨?_, source_row_threeSpace_normalizer_le_threeSpace F hg⟩
  let D := F.row ⊓ F.threeSpace
  let a : D := ⟨z, point_mem_row F, point_mem_threeSpace F⟩
  let b : D := ⟨g * z * g⁻¹, (mem_normalizer_iff.mp hg z).mp a.property⟩
  have ha : a ≠ 1 := by
    intro he
    have hz1 : z = 1 := congrArg Subtype.val he
    have ho := F.point_orderOf
    simp [hz1] at ho
  have hb : b ≠ 1 := by
    intro he
    have he' : (MulAut.conj g) z = (MulAut.conj g) 1 :=
      (congrArg Subtype.val he).trans (map_one _).symm
    exact ha (Subtype.ext ((MulAut.conj g).injective he'))
  obtain ⟨n, hn, _, he⟩ := row_subgroup_nonidentity_transitive F h D inf_le_left a b ha hb
  have hc : n⁻¹ * g ∈ Subgroup.centralizer ({z} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have he' : n * z * n⁻¹ = g * z * g⁻¹ := he
    have hh := congrArg (fun x => n⁻¹ * x * g) he'
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using hh.symm
  have hm := (rowNormalizer F).mul_mem hn (point_centralizer_le_row_normalizer F hc)
  rw [mul_inv_cancel_left] at hm
  exact hm


/-- The four-group stabilizer in the three-space normalizer is its literal row-normalizer intersection. -/
theorem source_threeSpace_row_relative_normalizer (h : F.LinearFusion) :
    normalizer (((F.row ⊓ F.threeSpace).subgroupOf (sourceThreeSpaceNormalizer F)) :
      Set (sourceThreeSpaceNormalizer F)) =
        (rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F) := by
  rw [← subgroupOf_normalizer_eq (show F.row ⊓ F.threeSpace ≤ sourceThreeSpaceNormalizer F from
    inf_le_right.trans F.threeSpace.le_normalizer), source_row_threeSpace_normalizer F h]
  ext g
  exact and_iff_left g.property

/-- The opposite flag has the corresponding ambient normalizer equality. -/
theorem source_column_plane_normalizer (h : F.LinearFusion) :
    normalizer ((F.column ⊓ F.plane : Subgroup G) : Set G) =
      columnNormalizer F ⊓ sourcePlaneNormalizer F := by
  simpa only [rowNormalizer, sourceThreeSpaceNormalizer, oppositeMarking_row,
    oppositeMarking_threeSpace] using source_row_threeSpace_normalizer
      (oppositeMarking F) (oppositeMarking_linearFusion F h)

/-- The column intersection inside the plane normalizer is the literal four-group stabilizer. -/
theorem source_plane_column_relative_normalizer (h : F.LinearFusion) :
    normalizer (((F.column ⊓ F.plane).subgroupOf (sourcePlaneNormalizer F)) :
      Set (sourcePlaneNormalizer F)) =
        (columnNormalizer F).subgroupOf (sourcePlaneNormalizer F) := by
  rw [← subgroupOf_normalizer_eq (show F.column ⊓ F.plane ≤ sourcePlaneNormalizer F from
    inf_le_right.trans F.plane.le_normalizer), source_column_plane_normalizer F h]
  ext g
  exact and_iff_left g.property

variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} (F' : MarkedCentralizer z')

theorem plane_normalizer_equiv_column_intersection
    (h : F.LinearFusion) (h' : F'.LinearFusion)
    (e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) :
    ((columnNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
      (columnNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
  let D := (F.column ⊓ F.plane).subgroupOf (sourcePlaneNormalizer F)
  let D' := (F'.column ⊓ F'.plane).subgroupOf (sourcePlaneNormalizer F')
  have hD : D.map e.toMonoidHom = D' := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ F.column ∧ (x : G) ∈ F.plane := hx
      have hh := he ⟨x, hx'.2⟩
      change e x = _ at hh
      change e x ∈ D'
      rw [hh]
      exact ⟨(planeMarkingEquiv_mem_pullback F F' Model.column _).mpr hx'.1,
        (planeMarkingEquiv F F' ⟨x, hx'.2⟩).property⟩
    · intro y hy
      have hy' : (y : G') ∈ F'.column ∧ (y : G') ∈ F'.plane := hy
      let a := (planeMarkingEquiv F F').symm ⟨y, hy'.2⟩
      have ha : (a : G) ∈ F.column := (planeMarkingEquiv_mem_pullback F F' Model.column a).mp
        (by rw [(planeMarkingEquiv F F').apply_symm_apply]; exact hy'.1)
      refine ⟨inclusion F.plane.le_normalizer a, ⟨ha, a.property⟩, ?_⟩
      change e (inclusion F.plane.le_normalizer a) = y
      rw [he]
      exact congrArg (inclusion F'.plane.le_normalizer)
        ((planeMarkingEquiv F F').apply_symm_apply ⟨y, hy'.2⟩)
  rw [← source_plane_column_relative_normalizer F h, map_equiv_normalizer_eq,
    hD, source_plane_column_relative_normalizer F' h']


/-- The marked plane comparison supplies the required column intersection map. -/
theorem exists_plane_normalizer_column_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F',
      ((columnNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
        (columnNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
  obtain ⟨e, he, _⟩ := exists_plane_normalizer_equiv F F' h h'
  exact ⟨e, plane_normalizer_equiv_column_intersection F F' h h' e he⟩

omit [Finite G] [Finite G'] in
private theorem transport_flag_equiv
    {A B I J : Subgroup G} {A' B' I' J' : Subgroup G'}
    (hAB : A = B) (hAB' : A' = B') (hIJ : I = J) (hIJ' : I' = J')
    (he : ∃ e : A ≃* A', (I.subgroupOf A).map e.toMonoidHom = I'.subgroupOf A') :
    ∃ e : B ≃* B', (J.subgroupOf B).map e.toMonoidHom = J'.subgroupOf B' := by
  subst B
  subst B'
  subst J
  subst J'
  exact he

/-- The opposite marking supplies a three-space comparison preserving its actual row intersection. -/
theorem exists_threeSpace_normalizer_row_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F',
      ((rowNormalizer F).subgroupOf (sourceThreeSpaceNormalizer F)).map e.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') := by
  have he := exists_plane_normalizer_column_flag_equiv (oppositeMarking F) (oppositeMarking F')
    (oppositeMarking_linearFusion F h) (oppositeMarking_linearFusion F' h')
  exact transport_flag_equiv
    (congrArg (fun A : Subgroup G => normalizer (A : Set G)) (oppositeMarking_plane F))
    (congrArg (fun A : Subgroup G' => normalizer (A : Set G')) (oppositeMarking_plane F'))
    (congrArg (fun A : Subgroup G => normalizer (A : Set G)) (oppositeMarking_column F))
    (congrArg (fun A : Subgroup G' => normalizer (A : Set G')) (oppositeMarking_column F')) he


/-- The local comparison preserves the row intersection in the induction overgroup without assuming simplicity. -/
theorem normalizerSpan_threeSpace_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourceThreeSpaceNormalizer (normalizerSpanMarking F) ≃* sourceThreeSpaceNormalizer F',
      ((rowNormalizer (normalizerSpanMarking F)).subgroupOf
        (sourceThreeSpaceNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (rowNormalizer F').subgroupOf (sourceThreeSpaceNormalizer F') :=
  exists_threeSpace_normalizer_row_flag_equiv (normalizerSpanMarking F) F'
    (normalizerSpan_linearFusion F h) h'

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
