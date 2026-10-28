module

public import Theory.Representation.SpecialLinearThreeFrameGeometry
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
# Coordinates for a marked plane in SL₃

Choose a nonzero vector on each of the three frame lines. Since they span a
three-dimensional space, they form a basis. Conjugation by this coordinate
isomorphism transports the literal roots and setwise stabilizers.

These coordinates support the plane factorization and residual calculation
in Aschbacher–Smith, G.2.5, printed pp.335–336.
-/

@[expose] public section
open Matrix Subgroup
open scoped MatrixGroups Pointwise
noncomputable section
namespace Matrix.SpecialLinearGroup.FrameGeometry.PlaneResidual
variable {F : Type*} [Field F]

def coordinatePoint (i : Fin 3) : Submodule F (Fin 3 → F) :=
  Submodule.span F {Pi.single i 1}

theorem mem_coordinatePoint (i : Fin 3) (v : Fin 3 → F) :
    v ∈ coordinatePoint i ↔ ∀ j, j ≠ i → v j = 0 := by
  rw [coordinatePoint, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩ j hj
    simp [Pi.single_eq_of_ne hj]
  · intro hv
    refine ⟨v i, ?_⟩
    ext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h, hv j h]

theorem mem_coordinatePlane (v : Fin 3 → F) :
    v ∈ coordinatePoint (F := F) 0 ⊔ coordinatePoint 1 ↔ v 2 = 0 := by
  constructor
  · intro hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    change a 2 + b 2 = 0
    rw [(mem_coordinatePoint _ _).mp ha 2 (by decide),
      (mem_coordinatePoint _ _).mp hb 2 (by decide), add_zero]
  · intro hv
    refine Submodule.mem_sup.mpr ⟨![v 0, 0, 0], ?_, ![0, v 1, 0], ?_, ?_⟩
    · rw [mem_coordinatePoint]; intro j hj; fin_cases j <;> simp_all
    · rw [mem_coordinatePoint]; intro j hj; fin_cases j <;> simp_all
    · ext j; fin_cases j <;> simp [hv]

/-- A frame admits coordinates with precisely its three marked lines. -/
theorem frame_basis (b : Frame F) :
    ∃ e : Module.Basis (Fin 3) F (Fin 3 → F),
      ∀ i, b.point i = Submodule.span F {e i} := by
  have hn (i : Fin 3) : b.point i ≠ ⊥ := by
    intro h
    have hd := b.dimension i
    rw [h] at hd
    simp at hd
  choose v hv hv0 using fun i => (b.point i).ne_bot_iff.mp (hn i)
  have hs (i) : b.point i = Submodule.span F {v i} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (b.dimension i) (hv i) (hv0 i)
  have hspan : ⊤ ≤ Submodule.span F (Set.range v) := by
    rw [← b.span]
    apply sup_le
    · apply sup_le
      all_goals rw [hs]; exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
    · rw [hs]; exact Submodule.span_mono (Set.singleton_subset_iff.mpr ⟨_, rfl⟩)
  let e := basisOfTopLeSpanOfCardEqFinrank v hspan (by simp)
  exact ⟨e, fun i => by simpa [e] using hs i⟩

def coordinateChange (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) : SL(3, F) ≃* SL(3, F) :=
  (toLin'_equiv.trans (_root_.SpecialLinearGroup.congr_linearEquiv e)).trans
    toLin'_equiv.symm

theorem coordinateChange_apply (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (g : SL(3, F)) (v : Fin 3 → F) :
    natural (coordinateChange e g) (e v) = e (natural g v) := by
  change Matrix.toLin' (LinearMap.toMatrix' _) (e v) = _
  rw [Matrix.toLin'_toMatrix']
  change e (natural g (e.symm (e v))) = _
  rw [e.symm_apply_apply]

theorem equiv_mem_map (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (A : Submodule F (Fin 3 → F)) (v : Fin 3 → F) :
    e v ∈ A.map e.toLinearMap ↔ v ∈ A := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact e.injective he ▸ hw
  · exact fun hv => Submodule.mem_map_of_mem hv

theorem coordinateChange_root (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (A B : Submodule F (Fin 3 → F)) :
    (root A B).map (coordinateChange e).toMonoidHom =
      root (A.map e.toLinearMap) (B.map e.toLinearMap) := by
  have hmem (g : SL(3, F)) : g ∈ root A B ↔
      coordinateChange e g ∈ root (A.map e.toLinearMap) (B.map e.toLinearMap) := by
    constructor
    · rintro ⟨hd, hf⟩
      constructor
      · intro w
        obtain ⟨v, rfl⟩ := e.surjective w
        rw [coordinateChange_apply, ← map_sub]
        exact Submodule.mem_map_of_mem (hd v)
      · intro w hw
        obtain ⟨v, hv, rfl⟩ := hw
        change natural (coordinateChange e g) (e v) = e v
        rw [coordinateChange_apply, hf v hv]
    · rintro ⟨hd, hf⟩
      constructor
      · intro v
        have hh := hd (e v)
        rw [coordinateChange_apply, ← map_sub] at hh
        exact (equiv_mem_map e A _).mp hh
      · intro v hv
        apply e.injective
        rw [← coordinateChange_apply]
        exact hf _ (Submodule.mem_map_of_mem hv)
  ext g
  obtain ⟨a, rfl⟩ := (coordinateChange e).surjective g
  rw [Subgroup.mem_map_equiv]
  simpa using hmem a

theorem coordinateChange_stabilizer (e : (Fin 3 → F) ≃ₗ[F] (Fin 3 → F))
    (A : Submodule F (Fin 3 → F)) :
    (stabilizer A).map (coordinateChange e).toMonoidHom =
      stabilizer (A.map e.toLinearMap) := by
  have hmem (g : SL(3, F)) : g ∈ stabilizer A ↔
      coordinateChange e g ∈ stabilizer (A.map e.toLinearMap) := by
    simp only [stabilizer, MulAction.mem_stabilizer_set]
    change (∀ v, natural g v ∈ A ↔ v ∈ A) ↔
      (∀ w, natural (coordinateChange e g) w ∈ A.map e.toLinearMap ↔
        w ∈ A.map e.toLinearMap)
    constructor
    · intro h w
      obtain ⟨v, rfl⟩ := e.surjective w
      rw [coordinateChange_apply, equiv_mem_map,
        equiv_mem_map]
      exact h v
    · intro h v
      have hh := h (e v)
      rw [coordinateChange_apply, equiv_mem_map,
        equiv_mem_map] at hh
      exact hh
  ext g
  obtain ⟨a, rfl⟩ := (coordinateChange e).surjective g
  rw [Subgroup.mem_map_equiv]
  simpa using hmem a

theorem basis_point_map (e : Module.Basis (Fin 3) F (Fin 3 → F)) (i : Fin 3) :
    (Submodule.span F {e i}).map e.equivFun.toLinearMap = coordinatePoint i := by
  rw [Submodule.map_span, Set.image_singleton]
  unfold coordinatePoint
  congr 2
  ext j
  simp [Pi.single_apply, eq_comm]

end Matrix.SpecialLinearGroup.FrameGeometry.PlaneResidual
