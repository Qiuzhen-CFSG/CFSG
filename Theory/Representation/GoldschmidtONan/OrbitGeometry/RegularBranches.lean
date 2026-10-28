module

public import Theory.Representation.GoldschmidtONan.OrbitGeometry.Transport

/-!
# The regular-action branches of the TI suborbit dichotomy

An orbit member contained in the moved space has the asserted transitive
stabilizer action by TI and transitivity on moved vectors. An orbit member
disjoint from the moved space is another complement, and its Y-images cover
exactly the vectors outside both distinguished spaces. A nonidentity stabilizer
element forces containment in the moved space: its displacement map on the
orbit member is injective, hence surjective.

These are the regular-action parts of GLS, Number 2, Chapter C, Proposition
14.2, Step 1 (`refs/KGroup/GLS2/ChapterC.tex`). The mixed-intersection case still
requires the global span comparison in that step.
-/

public section
namespace Representation.GoldschmidtONan
open BinaryOffender RegularCyclicNormalClosure
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

/-- A vector fixed by one nonidentity actor is fixed by all of Y. -/
theorem Input.mem_fixed_of_fixed_actor [Finite X] (h : Input ρ Y)
    {y : Y} (hy : y ≠ 1) {v : V} (hv : ρ y v = v) : v ∈ fixedSpace ρ Y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by
      rw [h.split.sup_eq_top]; trivial)
  have hbf : ρ y b = b := by
    rwa [map_add, show ρ y a = a from ha y, add_right_inj] at hv
  have hb0 := h.eq_zero_of_mem_moved_of_fixed hy hb hbf
  simpa only [hb0, add_zero] using ha

/-- A nontrivial stabilizer forces an orbit member into the moved space. -/
theorem Input.orbit_le_moved_of_stabilizer_ne_one [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hne : W ≠ fixedSpace ρ Y) {y : Y} (hy : y ≠ 1)
    (hyW : W.map (ρ y) = W) : W ≤ displacementSpan ρ Y ⊤ := by
  let f : W → W := fun w => ⟨ρ y w - w, W.sub_mem
    (by
      have hm : ρ y (w : V) ∈ W.map (ρ y) := ⟨w, w.property, rfl⟩
      rw [hyW] at hm
      exact hm) w.property⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have hab' : ρ y (a - b : V) = (a - b : V) := by
      have hh : ρ y a - a = ρ y b - b := congrArg Subtype.val hab
      rw [map_sub]
      calc
        ρ y a - ρ y b = (ρ y a - a) - (ρ y b - b) + (a - b) := by abel
        _ = a - b := by rw [hh]; abel
    have hz : (a - b : V) = 0 := Submodule.disjoint_def.mp
      (h.orbit_disjoint_fixed hW hne) _ (W.sub_mem a.property b.property)
      (h.mem_fixed_of_fixed_actor hy hab')
    exact Subtype.ext (sub_eq_zero.mp hz)
  intro v hv
  obtain ⟨w, hw⟩ := Finite.surjective_of_injective hinj ⟨v, hv⟩
  have hh : ρ y w - w = v := congrArg Subtype.val hw
  exact hh ▸ Submodule.subset_span ⟨y, y.property, w, by trivial, rfl⟩

/-- Containment in the moved space gives the first suborbit alternative. -/
theorem Input.suborbit_of_le_moved (h : Input ρ Y)
    {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hle : W ≤ displacementSpan ρ Y ⊤) :
    nonzeroSuborbitUnion ρ Y W = {v | v ∈ displacementSpan ρ Y ⊤ ∧ v ≠ 0} ∧
      ∀ v ∈ W, v ≠ 0 → ∀ w ∈ W, w ≠ 0 →
        ∃ y : Y, W.map (ρ y) = W ∧ ρ y v = w := by
  constructor
  · ext v
    constructor
    · rintro ⟨hv0, y, u, hu, rfl⟩
      exact ⟨moved_mem_action y (hle hu), hv0⟩
    · rintro ⟨hv, hv0⟩
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h.orbit_ne_bot hW)
      obtain ⟨y, hy⟩ := h.transitive w (hle hw) hw0 v hv hv0
      exact ⟨hv0, y, w, hw, hy⟩
  · intro v hv hv0 w hw hw0
    obtain ⟨y, hy⟩ := h.transitive v (hle hv) hv0 w (hle hw) hw0
    exact ⟨y, h.orbit_eq_of_common_nonzero (map_mem_fixedOrbit hW y) hW
      (show w ∈ W.map (ρ y) from ⟨v, hv, hy⟩) hw hw0, hy⟩

/-- A disjoint orbit member is a complement to the moved space. -/
theorem Input.isCompl_orbit_moved [Finite X] [Finite V] (h : Input ρ Y)
    {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hd : Disjoint W (displacementSpan ρ Y ⊤)) :
    IsCompl W (displacementSpan ρ Y ⊤) := by
  refine ⟨hd, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W (displacementSpan ρ Y ⊤)
  rw [hd.eq_bot, finrank_bot, add_zero, finrank_eq_fixed_of_mem_fixedOrbit hW] at hdim
  exact hdim.trans (Submodule.finrank_add_eq_of_isCompl h.split)

/-- A complement orbit member has trivial Y-stabilizer. -/
theorem Input.stabilizer_eq_one_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hne : W ≠ fixedSpace ρ Y) (hd : Disjoint W (displacementSpan ρ Y ⊤))
    (y : Y) (hyW : W.map (ρ y) = W) : y = 1 := by
  by_contra hy
  have hle := h.orbit_le_moved_of_stabilizer_ne_one hW hne hy hyW
  exact h.orbit_ne_bot hW (le_antisymm (fun v hv =>
    Submodule.disjoint_def.mp hd v hv (hle hv)) bot_le)

/-- The nonzero Y-images of a complement cover exactly the mixed vectors. -/
theorem Input.suborbit_of_disjoint_moved [Finite X] [Finite V]
    (h : Input ρ Y) {W : Submodule (ZMod 2) V} (hW : W ∈ fixedOrbit ρ Y)
    (hne : W ≠ fixedSpace ρ Y) (hd : Disjoint W (displacementSpan ρ Y ⊤)) :
    nonzeroSuborbitUnion ρ Y W =
      {v | v ∉ fixedSpace ρ Y ∧ v ∉ displacementSpan ρ Y ⊤} := by
  have hc := h.isCompl_orbit_moved hW hd
  have hf := h.orbit_disjoint_fixed hW hne
  ext v
  constructor
  · rintro ⟨hv0, y, w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · intro hfix
      exact hv0 (Submodule.disjoint_def.mp
        (h.orbit_disjoint_fixed (map_mem_fixedOrbit hW y) (map_actor_ne_fixed hne y))
        _ ⟨w, hw, rfl⟩ hfix)
    · intro hm
      have hw0 := Submodule.disjoint_def.mp hd w hw ((mem_moved_action_iff y w).mp hm)
      exact hv0 (by simp only [hw0, map_zero])
  · rintro ⟨hvF, hvD⟩
    have hv0 : v ≠ 0 := fun he => hvD (he ▸ (displacementSpan ρ Y ⊤).zero_mem)
    obtain ⟨a, ha, b, hb, hv⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by
        rw [h.split.sup_eq_top]; trivial)
    have ha0 : a ≠ 0 := by
      intro he
      apply hvD
      rw [← hv, he, zero_add]
      exact hb
    have hb0 : b ≠ 0 := by
      intro he
      apply hvF
      rw [← hv, he, add_zero]
      exact ha
    obtain ⟨w, hw, d, hdD, haw⟩ := Submodule.mem_sup.mp
      (show a ∈ W ⊔ displacementSpan ρ Y ⊤ by rw [hc.sup_eq_top]; trivial)
    have hd0 : d ≠ 0 := by
      intro he
      have hwa : w = a := by simpa only [he, add_zero] using haw
      exact ha0 (Submodule.disjoint_def.mp hf a (hwa ▸ hw) ha)
    have hwform : w = a + -d := by rw [← haw]; abel
    obtain ⟨y, hy⟩ := h.transitive (-d) ((displacementSpan ρ Y ⊤).neg_mem hdD)
      (neg_ne_zero.mpr hd0) b hb hb0
    refine ⟨hv0, y, w, hw, ?_⟩
    rw [hwform, map_add, show ρ y a = a from ha y, hy]
    exact hv

end Representation.GoldschmidtONan
