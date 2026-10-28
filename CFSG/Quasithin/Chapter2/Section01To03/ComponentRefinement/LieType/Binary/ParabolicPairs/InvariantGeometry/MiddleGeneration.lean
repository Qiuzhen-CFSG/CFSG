module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs.InvariantGeometry.Endpoints

/-!
# Generation by the degree-five endpoint and middle flags

The stabilizer of a nested two-space and three-space moves both endpoints
of a surrounding line–hyperplane flag. Explicit rank-one transvections
prove each failure of containment. The overgroup theorem for the endpoint
flag then shows that the two flag stabilizers generate the entire component.

This is the geometric generation calculation for types {1,4} and {2,3}
in Aschbacher–Smith 2.3.9(7), printed pp.525–526. Sylow containment and
invariance of the middle flag are separate inputs, not consequences asserted
by this calculation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

/-- The proper flag with successive dimensions two and three. -/
noncomputable def middleFlag (W₂ W₃ : Space 5)
    (h₂ : Module.finrank (ZMod 2) W₂ = 2) (h₃ : Module.finrank (ZMod 2) W₃ = 3)
    (h₂₃ : W₂ ≤ W₃) : Flag 5 where
  spaces := {W₂, W₃}
  nonempty := by simp
  proper := by
    intro W hW
    have hd : Module.finrank (ZMod 2) W = 2 ∨ Module.finrank (ZMod 2) W = 3 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hW
      rcases hW with rfl | rfl
      · exact Or.inl h₂
      · exact Or.inr h₃
    constructor
    · intro he
      rw [he, finrank_bot] at hd
      omega
    · intro he
      rw [he, finrank_top, Module.finrank_fin_fun] at hd
      omega
  chain := by
    intro W hW W' hW'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW hW'
    rcases hW with rfl | rfl <;> rcases hW' with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl h₂₃
    · exact Or.inr h₂₃
    · exact Or.inl le_rfl

theorem middleFlag_types (W₂ W₃ : Space 5)
    (h₂ : Module.finrank (ZMod 2) W₂ = 2) (h₃ : Module.finrank (ZMod 2) W₃ = 3)
    (h₂₃ : W₂ ≤ W₃) : (middleFlag W₂ W₃ h₂ h₃ h₂₃).types = {2, 3} := by
  classical
  simp [Flag.types, middleFlag, h₂, h₃]

variable {G : Type*} [Group G] {L : Subgroup G}

theorem middleFlag_stabilizer (e : L ≃* PSL 5) (W₂ W₃ : Space 5)
    (h₂ : Module.finrank (ZMod 2) W₂ = 2) (h₃ : Module.finrank (ZMod 2) W₃ = 3)
    (h₂₃ : W₂ ≤ W₃) :
    flagStabilizer e (middleFlag W₂ W₃ h₂ h₃ h₂₃) =
      subspaceStabilizer e W₂ ⊓ subspaceStabilizer e W₃ := by
  ext x
  simp only [mem_flagStabilizer, middleFlag, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, mem_inf, mem_subspaceStabilizer]

private theorem scalar_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 :=
  (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem transvection_stabilizes {W : Space 5}
    {w : Vector 5} {f : Vector 5 →ₗ[ZMod 2] ZMod 2} (hfw : f w = 0)
    (h : w ∈ W ∨ W ≤ f.ker) : BinaryLinear.transvection w f hfw ∈ BinaryLinear.parabolic W := by
  intro v
  change v + f v • w ∈ W ↔ v ∈ W
  rcases h with hw | hf
  · exact W.add_mem_iff_left (W.smul_mem (f v) hw)
  · constructor
    · intro hv
      have he : f v = 0 := by
        have := hf hv
        simpa [map_add, map_smul, hfw] using this
      simpa [he] using hv
    · intro hv
      have he : f v = 0 := hf hv
      simpa [he] using hv

variable {e : L ≃* PSL 5} {t : L}

private theorem middle_not_le_line (c : TransvectionCoordinates e t)
    (W₂ W₃ : Space 5) (h₂ : Module.finrank (ZMod 2) W₂ = 2)
    (h₂₃ : W₂ ≤ W₃) :
    ¬ subspaceStabilizer e W₂ ⊓ subspaceStabilizer e W₃ ≤ subspaceStabilizer e c.line := by
  intro hle
  have hnot : ¬ W₂ ≤ c.line := by
    intro h
    have hd := Submodule.finrank_mono h
    rw [h₂, c.line_finrank] at hd
    omega
  obtain ⟨u, hu₂, hul⟩ := SetLike.not_le_iff_exists.mp hnot
  have hwu : c.vector ∉ Submodule.span (ZMod 2) {u} := by
    rintro hw
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hw
    have ha0 : a ≠ 0 := by
      intro ha0
      exact c.vector_ne_zero (by simpa [ha0] using ha.symm)
    have he : u = c.vector := by simpa [scalar_one ha0] using ha
    exact hul (he ▸ Submodule.mem_span_singleton_self c.vector)
  obtain ⟨q, hqw, hq⟩ := Submodule.exists_le_ker_of_notMem hwu
  have hqu : q u = 0 := hq (Submodule.mem_span_singleton_self u)
  let g := BinaryLinear.transvection u q hqu
  let x := (linearModel e).symm g
  have hx : x ∈ subspaceStabilizer e W₂ ⊓ subspaceStabilizer e W₃ := by
    change linearModel e x ∈ BinaryLinear.parabolic W₂ ⊓ BinaryLinear.parabolic W₃
    rw [show linearModel e x = g from (linearModel e).apply_symm_apply g]
    exact ⟨transvection_stabilizes hqu (Or.inl hu₂),
      transvection_stabilizes hqu (Or.inl (h₂₃ hu₂))⟩
  have hw := ((mem_subspaceStabilizer e c.line x).mp (hle hx) c.vector).mpr
    (Submodule.mem_span_singleton_self c.vector)
  rw [show linearModel e x = g from (linearModel e).apply_symm_apply g] at hw
  change c.vector + q c.vector • u ∈ c.line at hw
  rw [scalar_one hqw, one_smul] at hw
  exact hul ((c.line.add_mem_iff_right (Submodule.mem_span_singleton_self c.vector)).mp hw)

private theorem middle_not_le_hyperplane (c : TransvectionCoordinates e t)
    (W₂ W₃ : Space 5) (h₃ : Module.finrank (ZMod 2) W₃ = 3)
    (h₂₃ : W₂ ≤ W₃) (h₃h : W₃ ≤ c.hyperplane) :
    ¬ subspaceStabilizer e W₂ ⊓ subspaceStabilizer e W₃ ≤
      subspaceStabilizer e c.hyperplane := by
  intro hle
  have hnot : ¬ c.hyperplane ≤ W₃ := by
    intro h
    have hd := Submodule.finrank_mono h
    have hh := c.hyperplane_finrank
    omega
  obtain ⟨u, huh, hu₃⟩ := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨v, hv⟩ := LinearMap.surjective c.functional_ne_zero (1 : ZMod 2)
  have hu : u ∉ W₃ ⊔ Submodule.span (ZMod 2) {v} := by
    intro hu
    obtain ⟨w, hw, y, hy, he⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hwf : c.functional w = 0 := h₃h hw
    have huf : c.functional u = 0 := huh
    have ha : a = 0 := by
      have hf := congrArg c.functional he
      simpa [map_add, map_smul, hwf, huf, hv] using hf
    rw [ha, zero_smul, add_zero] at he
    exact hu₃ (he ▸ hw)
  obtain ⟨q, hqu, hq⟩ := Submodule.exists_le_ker_of_notMem hu
  have hq₃ : W₃ ≤ q.ker := le_sup_left.trans hq
  have hqv : q v = 0 := hq ((show Submodule.span (ZMod 2) {v} ≤ W₃ ⊔ Submodule.span (ZMod 2) {v} from le_sup_right) (Submodule.mem_span_singleton_self v))
  let g := BinaryLinear.transvection v q hqv
  let x := (linearModel e).symm g
  have hx : x ∈ subspaceStabilizer e W₂ ⊓ subspaceStabilizer e W₃ := by
    change linearModel e x ∈ BinaryLinear.parabolic W₂ ⊓ BinaryLinear.parabolic W₃
    rw [show linearModel e x = g from (linearModel e).apply_symm_apply g]
    exact ⟨transvection_stabilizes hqv (Or.inr (h₂₃.trans hq₃)),
      transvection_stabilizes hqv (Or.inr hq₃)⟩
  have hw := ((mem_subspaceStabilizer e c.hyperplane x).mp (hle hx) u).mpr huh
  rw [show linearModel e x = g from (linearModel e).apply_symm_apply g] at hw
  change c.functional (u + q u • v) = 0 at hw
  have huf : c.functional u = 0 := huh
  simp [map_add, huf, hv, scalar_one hqu] at hw

/-- An incident {1,4} flag and {2,3} flag generate the whole degree-five component. -/
theorem TransvectionCoordinates.middle_generate (c : TransvectionCoordinates e t)
    (W₂ W₃ : Space 5) (h₂ : Module.finrank (ZMod 2) W₂ = 2)
    (h₃ : Module.finrank (ZMod 2) W₃ = 3)
    (h₂₃ : W₂ ≤ W₃) (h₃h : W₃ ≤ c.hyperplane) :
    flagStabilizer e (c.flag (by decide)) ⊔
      flagStabilizer e (middleFlag W₂ W₃ h₂ h₃ h₂₃) = ⊤ := by
  rw [← c.centralizer_eq_flag, middleFlag_stabilizer]
  by_contra hne
  rcases c.proper_overgroup_endpoint (by decide) _ le_sup_left hne with h | h
  · exact middle_not_le_line c W₂ W₃ h₂ h₂₃ (le_sup_right.trans h)
  · exact middle_not_le_hyperplane c W₂ W₃ h₃ h₂₃ h₃h (le_sup_right.trans h)

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
