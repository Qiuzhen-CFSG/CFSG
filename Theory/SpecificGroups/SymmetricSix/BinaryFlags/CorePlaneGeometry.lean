module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
/-!
# Constant-weight Sylow-invariant planes in the six-letter augmentation core

An invariant binary plane whose three nonzero words have the same weight
consists of weight-four words. A certificate checks the three generators
of the canonical alternating Sylow subgroup on the 32 actual core words.
The general plane statement chooses a basis and uses its four-vector expansion.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939.
-/
@[expose] public section
open BinaryPermutation Subgroup Module
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.CorePlaneGeometry
open NaturalGeometry
abbrev C := BinaryPermutation.core (Fin 6)
def weight (v : C) : ℕ := (Finset.univ.filter fun i => v.val i ≠ 0).card
private local instance : DecidablePred (fun v : Full (Fin 6) => v ∈ core (Fin 6)) :=
  fun v => inferInstanceAs (Decidable ((augmentation (Fin 6)) v = 0))
private local instance : Fintype C :=
  Fintype.ofFinset (Finset.univ.filter fun v => v ∈ core (Fin 6)) (by simp)
private def inPlane (u v w : C) : Prop := w = 0 ∨ w = u ∨ w = v ∨ w = u + v
private instance (u v w : C) : Decidable (inPlane u v w) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem constantWeight_cert : ∀ u v : C,
    u ≠ 0 → v ≠ 0 → u ≠ v → weight v = weight u → weight (u + v) = weight u →
    (inPlane u v (coreRepresentation (Fin 6) genA u) ∧
      inPlane u v (coreRepresentation (Fin 6) genA v)) →
    (inPlane u v (coreRepresentation (Fin 6) genB u) ∧
      inPlane u v (coreRepresentation (Fin 6) genB v)) →
    (inPlane u v (coreRepresentation (Fin 6) genC u) ∧
      inPlane u v (coreRepresentation (Fin 6) genC v)) → weight u = 4 := by
  decide +kernel

private theorem mem_plane_cases (u v w : C)
    (hw : w ∈ Submodule.span (ZMod 2) {u,v}) : inPlane u v w := by
  obtain ⟨a,b,rfl⟩ := Submodule.mem_span_pair.mp hw
  have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hc a with rfl | rfl <;> rcases hc b with rfl | rfl <;> simp [inPlane]

/-- Every nonzero word in a constant-weight plane normalized by the actual
alternating Sylow flag group has weight four. -/
theorem plane_weight_four (P : Submodule (ZMod 2) C)
    (hd : finrank (ZMod 2) P = 2)
    (hi : ∀ g ∈ T0, ∀ v ∈ P, coreRepresentation (Fin 6) g v ∈ P)
    (hw : ∀ u ∈ P, u ≠ 0 → ∀ v ∈ P, v ≠ 0 → weight u = weight v) :
    ∀ u ∈ P, u ≠ 0 → weight u = 4 := by
  let b : Basis (Fin 2) (ZMod 2) P := (finBasis (ZMod 2) P).reindex (finCongr hd)
  let u : C := b 0
  let v : C := b 1
  have hu : u ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
  have hv : v ≠ 0 := fun h => b.ne_zero 1 (Subtype.ext h)
  have huv : u ≠ v := fun h => by
    have h01 := b.injective (Subtype.ext h)
    exact (by decide : (0 : Fin 2) ≠ 1) h01
  have huv0 : u + v ≠ 0 := by
    intro hz
    apply huv
    have h := congrArg (fun x : C => x + v) hz
    have htwo : v + v = 0 := by
      simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using (two_smul (ZMod 2) v).symm
    simpa only [add_assoc,htwo,add_zero,zero_add] using h
  have hspan : P = Submodule.span (ZMod 2) {u,v} := by
    have h := congrArg (Submodule.map P.subtype) b.span_eq
    rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype] at h
    have hs : Set.range (fun i : Fin 2 => (b i : C)) = {u,v} := by
      ext x
      constructor
      · rintro ⟨i,rfl⟩
        fin_cases i <;> simp [u,v]
      · intro hx
        rcases hx with rfl | rfl
        · exact ⟨0,rfl⟩
        · exact ⟨1,rfl⟩
    rw [← Set.range_comp] at h
    change Submodule.span (ZMod 2) (Set.range (fun i : Fin 2 => (b i : C))) = P at h
    rw [hs] at h
    exact h.symm
  have hwu : weight u = 4 := by
    apply constantWeight_cert u v hu hv huv (hw v (b 1).property hv u (b 0).property hu)
      (hw (u+v) (P.add_mem (b 0).property (b 1).property) huv0 u (b 0).property hu)
    all_goals
      refine ⟨mem_plane_cases u v _ (hspan ▸ hi _ ?_ u (b 0).property),
        mem_plane_cases u v _ (hspan ▸ hi _ ?_ v (b 1).property)⟩
      all_goals first | exact genA_mem_T0 | exact genB_mem_T0 | exact genC_mem_T0
  intro w hwm hw0
  exact (hw w hwm hw0 u (b 0).property hu).trans hwu
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.CorePlaneGeometry
