module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Configurations

/-!
# The binary plane seed for G.3.1

Mutually moving root groups yield the two transpositions on the three nonzero
vectors in their plane. Six explicit products therefore realize every linear
automorphism. Symmetry of fixation and the quotient-rank hypothesis supply such
a pair inside every canonical block, even when the ambient space is infinite.

Source: Aschbacher--Smith, G.3.1, printed p.337.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section03
open BinaryLinear BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self_binary (x : V) : x + x = 0 := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  simpa only [add_smul, one_smul, zero_smul] using congrArg (fun c => c • x) h

private theorem mem_binary_plane (x y v : V) :
    v ∈ Submodule.span (ZMod 2) ({x, y} : Set V) ↔
      v = 0 ∨ v = x ∨ v = y ∨ v = x + y := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;>
      rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

private theorem span_three_points (x y : V) :
    Submodule.span (ZMod 2) ({x, y, x + y} : Set V) =
      Submodule.span (ZMod 2) ({x, y} : Set V) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
        (Submodule.subset_span (by simp))
  · apply Submodule.span_mono
    intro v hv
    rcases hv with rfl | rfl <;> simp

/-- Two mutually moving roots induce all six automorphisms of their binary plane. -/
theorem plane_spanAction_surjective {G : Subgroup (GL V)} {x y : V}
    {a b : GL V} (ha : a ∈ rootGroup G x) (hb : b ∈ rootGroup G y)
    (hay : a y ≠ y) (hbx : b x ≠ x) :
    Function.Surjective (spanAction G ({x, y, x + y} : Set V)) := by
  let Γ : Set V := {x, y, x + y}
  let W := Submodule.span (ZMod 2) Γ
  have hxW : x ∈ W := Submodule.subset_span (by simp [Γ])
  have hyW : y ∈ W := Submodule.subset_span (by simp [Γ])
  have hax : a x = x := ha.2.1 x (Submodule.mem_span_singleton_self x)
  have hby : b y = y := hb.2.1 y (Submodule.mem_span_singleton_self y)
  have hay' : a y = x + y := (root_move_eq_add ha hay).trans (add_comm _ _)
  have hbx' : b x = x + y := root_move_eq_add hb hbx
  have hxx := add_self_binary x
  have hyy := add_self_binary y
  have hxy : x ≠ y := by
    rintro rfl
    exact hay hax
  have hx0 : x ≠ 0 := by
    intro he
    apply hay
    rw [hay', he, zero_add]
  have hy0 : y ≠ 0 := by
    intro he
    apply hbx
    rw [hbx', he, add_zero]
  have haΓ : a ∈ generated G Γ := rootGroup_le_generated G (by simp [Γ]) ha
  have hbΓ : b ∈ generated G Γ := rootGroup_le_generated G (by simp [Γ]) hb
  have habx : (a * b) x = y := by
    simp only [LinearEquiv.mul_apply, hbx', map_add, hax, hay', ← add_assoc, hxx, zero_add]
  have haby : (a * b) y = x + y := by simp only [LinearEquiv.mul_apply, hby, hay']
  have hbax : (b * a) x = x + y := by simp only [LinearEquiv.mul_apply, hax, hbx']
  have hbay : (b * a) y = x := by
    simp only [LinearEquiv.mul_apply, hay', map_add, hbx', hby, add_assoc, hyy, add_zero]
  have habax : (a * b * a) x = y := by rw [LinearEquiv.mul_apply, hax, habx]
  have habay : (a * b * a) y = x := by
    rw [LinearEquiv.mul_apply, hay', map_add, habx, haby]
    calc
      y + (x + y) = x + (y + y) := by abel
      _ = x := by rw [hyy, add_zero]
  have hpairs (u v : V) (hu : u = x ∨ u = y ∨ u = x + y)
      (hv : v = x ∨ v = y ∨ v = x + y) (huv : u ≠ v) :
      ∃ g : generated G Γ, g.val x = u ∧ g.val y = v := by
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨⟨a, haΓ⟩, hax, hay'⟩
    · exact ⟨⟨a * b * a, (generated G Γ).mul_mem
        ((generated G Γ).mul_mem haΓ hbΓ) haΓ⟩, habax, habay⟩
    · exact (huv rfl).elim
    · exact ⟨⟨a * b, (generated G Γ).mul_mem haΓ hbΓ⟩, habx, haby⟩
    · exact ⟨⟨b * a, (generated G Γ).mul_mem hbΓ haΓ⟩, hbax, hbay⟩
    · exact ⟨⟨b, hbΓ⟩, hbx', hby⟩
    · exact (huv rfl).elim
  intro e
  let x' : W := ⟨x, hxW⟩
  let y' : W := ⟨y, hyW⟩
  have hform (w : W) : (w : V) = 0 ∨ (w : V) = x ∨ (w : V) = y ∨ (w : V) = x + y := by
    apply (mem_binary_plane x y w).mp
    simpa only [W, Γ, span_three_points] using w.property
  have hex0 : (e x' : V) ≠ 0 := by
    intro he
    exact hx0 (congrArg Subtype.val (e.map_eq_zero_iff.mp (Subtype.ext he)))
  have hey0 : (e y' : V) ≠ 0 := by
    intro he
    exact hy0 (congrArg Subtype.val (e.map_eq_zero_iff.mp (Subtype.ext he)))
  have hexy : (e x' : V) ≠ (e y' : V) := by
    intro he
    exact hxy (congrArg Subtype.val (e.injective (Subtype.ext he)))
  obtain ⟨g, hgx, hgy⟩ := hpairs (e x') (e y')
    ((hform (e x')).resolve_left hex0) ((hform (e y')).resolve_left hey0) hexy
  refine ⟨g, ?_⟩
  ext w
  change g.val w = (e w : V)
  rcases hform w with hw | hw | hw | hw
  · have he : w = 0 := Subtype.ext hw
    simp [he]
  · have he : w = x' := Subtype.ext hw
    simpa only [he] using hgx
  · have he : w = y' := Subtype.ext hw
    simpa only [he] using hgy
  · have he : w = x' + y' := Subtype.ext hw
    simpa only [he, map_add, Submodule.coe_add] using congrArg₂ (· + ·) hgx hgy

/-- Every canonical block contains a configuration on three points. -/
theorem Hypotheses.exists_plane_configuration {G : Subgroup (GL V)} [Finite G]
    {Δ : Set V} (h : Hypotheses G Δ) (i : OrbitBlock G Δ) :
    ∃ Γ : Set V, LinearConfiguration G Δ Γ ∧ Γ ⊆ i.val := by
  classical
  obtain ⟨x, hxΔ, hi⟩ := i.property
  have hx : x ∈ i.val := hi ▸ MulAction.mem_orbit_self x
  obtain ⟨y, hy, a, ha, hay⟩ := h.exists_moved_center_in_block i hx
  have hyΔ := block_subset h i hy
  have hb : ∃ b ∈ rootGroup G y, b x ≠ x := by
    by_contra hn
    push Not at hn
    exact hay (h.fixed_rootGroup_symm hxΔ hyΔ hn a ha)
  obtain ⟨b, hb, hbx⟩ := hb
  let Γ : Set V := {x, y, x + y}
  have hsum : x + y ∈ i.val := by
    rw [orbitBlock_eq_orbit i hy]
    refine MulAction.mem_orbit_iff.mpr ⟨⟨a, rootGroup_le_generated G hxΔ ha⟩, ?_⟩
    exact (root_move_eq_add ha hay).trans (add_comm _ _)
  have hsub : Γ ⊆ i.val := by
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hsum
  have hsubΔ : Γ ⊆ Δ := hsub.trans (block_subset h i)
  have hall : Γ = {v | v ∈ Submodule.span (ZMod 2) Γ ∧ v ≠ 0} := by
    ext v
    constructor
    · intro hv
      exact ⟨Submodule.subset_span hv, h.nonzero v (hsubΔ hv)⟩
    · rintro ⟨hv, hv0⟩
      rw [show Submodule.span (ZMod 2) Γ = Submodule.span (ZMod 2) {x, y}
        from span_three_points x y, mem_binary_plane] at hv
      rcases hv.resolve_left hv0 with rfl | rfl | rfl <;> simp [Γ]
  have hdim : 2 ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) Γ) := by
    have hΓfin : Γ.Finite := by simp [Γ]
    let : FiniteDimensional (ZMod 2) (Submodule.span (ZMod 2) Γ) :=
      Module.Finite.span_of_finite _ hΓfin
    have hline : centerLine x ≤ Submodule.span (ZMod 2) Γ :=
      Submodule.span_mono (Set.singleton_subset_iff.mpr (by simp [Γ]))
    have hlt : centerLine x < Submodule.span (ZMod 2) Γ :=
      lt_of_le_of_ne hline (by
        intro he
        have hyline : y ∈ centerLine x := he ▸ Submodule.subset_span (by simp [Γ])
        exact hay (ha.2.1 y hyline))
    have hd := Submodule.finrank_lt_finrank_of_lt hlt
    rw [finrank_span_singleton (h.nonzero x hxΔ)] at hd
    exact hd
  exact ⟨Γ, ⟨hsubΔ, hall, plane_spanAction_surjective ha hb hay hbx, hdim⟩, hsub⟩

end CFSG.Quasithin.ChapterG.Section03
