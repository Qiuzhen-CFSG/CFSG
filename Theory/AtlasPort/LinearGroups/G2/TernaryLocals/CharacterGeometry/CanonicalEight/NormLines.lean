module

public import Theory.AtlasPort.LinearGroups.G2.TernaryLocals.CharacterGeometry.Decomposition

/-!
# Intrinsic norm lines above ternary octonion four-groups

In the anisotropic case select the norm-one homogeneous vectors; otherwise
select all homogeneous vectors of nonzero norm. The pointwise stabilizer of
their lines is an actual subgroup of the octonion automorphism group. It
contains the original subgroup and is normalized by its whole ambient
normalizer, because both homogeneity and norm are preserved.

If the selected vectors span, the stabilizer is elementary abelian and has
order dividing eight. For a four-group, an element of this stabilizer moving
a fixed vector then forces order eight. These are conditional reductions:
spanning and existence of that element remain geometric obligations.

Application: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(4), printed pp.3–4 and 481–482. The recognition configuration
on p.417 does not imply this extension result. Octonion coordinates follow
the licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
open Atlas.SplitOctonion

/-- The fixed character plane has no nonzero isotropic vector. -/
def FixedAnisotropic (E : Subgroup G) : Prop :=
  ∀ x ∈ characterSpace E 1, norm x = 0 → x = 0

/-- Nonzero homogeneous vectors on the canonically chosen norm lines. -/
def selected (E : Subgroup G) : Set V :=
  {x | (∃ χ : Character E, x ∈ characterSpace E χ) ∧
    norm x ≠ 0 ∧ (FixedAnisotropic E → norm x = 1)}

theorem selected_norm_ne_zero (E : Subgroup G) {x : V} (hx : x ∈ selected E) :
    norm x ≠ 0 := hx.2.1

theorem selected_ne_zero (E : Subgroup G) {x : V} (hx : x ∈ selected E) : x ≠ 0 := by
  intro h
  apply hx.2.1
  rw [h]
  rfl

/-- The identity is always one of the selected vectors. -/
theorem unit_selected (E : Subgroup G) : unit ∈ selected E := by
  refine ⟨⟨1, unit_mem E⟩, ?_, ?_⟩
  · decide +kernel
  · intro _; rfl

/-- Multiplicativity of the norm makes canonical selection multiplicatively closed. -/
theorem mul_selected (E : Subgroup G) {x y : V}
    (hx : x ∈ selected E) (hy : y ∈ selected E) : mul x y ∈ selected E := by
  obtain ⟨χ, hχ⟩ := hx.1
  obtain ⟨ψ, hψ⟩ := hy.1
  refine ⟨⟨χ * ψ, mul_mem hχ hψ⟩, ?_, ?_⟩
  · rw [norm_mul]; exact mul_ne_zero hx.2.1 hy.2.1
  · intro ha
    rw [norm_mul, hx.2.2 ha, hy.2.2 ha, one_mul]

/-- Fixing a ternary line means acting on its vectors by a sign. -/
def FixesLine (g : G) (x : V) : Prop := g.val x = x ∨ g.val x = -x

private theorem fixesLine_mul {g h : G} {x : V}
    (hg : FixesLine g x) (hh : FixesLine h x) : FixesLine (g*h) x := by
  change g.val (h.val x) = x ∨ g.val (h.val x) = -x
  rcases hg with hg | hg <;> rcases hh with hh | hh <;> simp [hh, hg]

private theorem fixesLine_inv {g : G} {x : V}
    (hg : FixesLine g x) : FixesLine g⁻¹ x := by
  rcases hg with hg | hg
  · left
    exact g.val.injective (by change g.val (g.val.symm x) = g.val x; rw [hg, g.val.apply_symm_apply])
  · right
    apply g.val.injective
    change g.val (g.val.symm x) = g.val (-x)
    rw [g.val.apply_symm_apply, map_neg, hg, neg_neg]

/-- The actual subgroup fixing each line represented by a set of vectors. -/
def lineFixer (S : Set V) : Subgroup G where
  carrier := {g | ∀ x ∈ S, FixesLine g x}
  one_mem' := by intro x _; exact Or.inl rfl
  mul_mem' := by
    intro g h hg hh x hx
    exact fixesLine_mul (hg x hx) (hh x hx)
  inv_mem' := by
    intro g hg x hx
    exact fixesLine_inv (hg x hx)

@[simp] theorem mem_lineFixer (S : Set V) (g : G) :
    g ∈ lineFixer S ↔ ∀ x ∈ S, FixesLine g x := Iff.rfl

/-- The canonical candidate, defined without choosing vectors or a basis. -/
def candidate (E : Subgroup G) : Subgroup G := lineFixer (selected E)

private def conjugationHom (E : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (E : Set G)) : E →* E where
  toFun e := ⟨g⁻¹ * e.val * g, (Subgroup.mem_normalizer_iff''.mp hg e.val).mp e.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- A normalizer element transports a character vector to a character vector. -/
theorem homogeneous_image (E : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {x : V}
    (hx : ∃ χ : Character E, x ∈ characterSpace E χ) :
    ∃ χ : Character E, g.val x ∈ characterSpace E χ := by
  obtain ⟨χ, hx⟩ := hx
  refine ⟨χ.comp (conjugationHom E g hg), ?_⟩
  intro e
  have h := congrArg g.val (hx (conjugationHom E g hg e))
  change g.val (g.val.symm (e.val.val (g.val x))) =
    g.val ((χ (conjugationHom E g hg e) : ZMod 3) • x) at h
  simpa only [LinearEquiv.apply_symm_apply, map_smul, MonoidHom.comp_apply] using h

/-- The whole ambient normalizer preserves the selected vectors. -/
theorem selected_image (E : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {x : V} (hx : x ∈ selected E) :
    g.val x ∈ selected E := by
  exact ⟨homogeneous_image E g hg hx.1, by simpa using hx.2.1,
    fun h => (automorphism_norm g x).trans (hx.2.2 h)⟩

/-- Every element of E acts by signs on every selected line. -/
theorem le_candidate (E : Subgroup G) : E ≤ candidate E := by
  intro e he x hx
  obtain ⟨χ, hχ⟩ := hx.1
  have h := hχ ⟨e,he⟩
  have hu := (by decide +kernel : ∀ u : (ZMod 3)ˣ, (u : ZMod 3) = 1 ∨ (u : ZMod 3) = -1) (χ ⟨e,he⟩)
  rcases hu with hu | hu
  · left; simpa only [hu, one_smul] using h
  · right; simpa only [hu, neg_one_smul] using h

private theorem conjugate_mem_candidate (E : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (E : Set G)) {f : G} (hf : f ∈ candidate E) :
    g*f*g⁻¹ ∈ candidate E := by
  intro x hx
  have hi := selected_image E g⁻¹ ((Subgroup.normalizer (E : Set G)).inv_mem hg) hx
  have h := hf ((g⁻¹).val x) hi
  change g.val (f.val (g.val.symm x)) = x ∨ g.val (f.val (g.val.symm x)) = -x
  change f.val (g.val.symm x) = g.val.symm x ∨
    f.val (g.val.symm x) = -(g.val.symm x) at h
  rcases h with h | h
  · left
    rw [h, g.val.apply_symm_apply]
  · right
    rw [h, map_neg, g.val.apply_symm_apply]

/-- Canonical norm selection yields containment of WHOLE ambient normalizers. -/
theorem normalizer_le (E : Subgroup G) :
    Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (candidate E : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff.mpr
  intro f
  constructor
  · exact conjugate_mem_candidate E g hg
  · intro hf
    have h := conjugate_mem_candidate E g⁻¹ ((Subgroup.normalizer (E : Set G)).inv_mem hg) hf
    simpa [mul_assoc] using h

/-- A spanning set of lines forces its pointwise stabilizer to have exponent two. -/
theorem lineFixer_square_eq_one (S : Set V)
    (hS : Submodule.span (ZMod 3) S = ⊤) (g : lineFixer S) : g^2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val.val (g.val.val x) = x
  have hx : x ∈ Submodule.span (ZMod 3) S := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases g.property y hy with h | h
      · rw [h, h]
      · rw [h, map_neg, h, neg_neg]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smul, hx]

/-- No commutativity assumption is needed: diagonal signs on a spanning set
make the actual line stabilizer an elementary two-group. -/
theorem lineFixer_elementary (S : Set V) (hS : Submodule.span (ZMod 3) S = ⊤) :
    IsElementaryAbelian 2 (lineFixer S) where
  is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun g => orderOf_dvd_of_pow_eq_one (lineFixer_square_eq_one S hS g)) a b).eq⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (lineFixer_square_eq_one S hS)

/-- A spanning canonical selection makes the candidate elementary. -/
theorem candidate_elementary_of_span (E : Subgroup G)
    (hS : Submodule.span (ZMod 3) (selected E) = ⊤) :
    IsElementaryAbelian 2 (candidate E) := lineFixer_elementary _ hS

/-- Once spanning is proved, the existing character dimension theorem bounds
this actual stabilizer by eight. -/
theorem candidate_card_dvd_eight_of_span (E : Subgroup G)
    (hS : Submodule.span (ZMod 3) (selected E) = ⊤) : Nat.card (candidate E) ∣ 8 := by
  let := candidate_elementary_of_span E hS
  exact elementary_card_dvd_eight (candidate E)

/-- An actual line-fixing automorphism outside E supplies the only remaining
order lower bound, once canonical spanning is known. -/
theorem candidate_card_eq_eight_of_span_of_outside (E : Subgroup G)
    (hE : Nat.card E = 4) (hS : Submodule.span (ZMod 3) (selected E) = ⊤)
    (hout : ∃ g ∈ candidate E, g ∉ E) : Nat.card (candidate E) = 8 := by
  have hlt : 4 < Nat.card (candidate E) := by
    by_contra h
    have heq : E = candidate E :=
      Subgroup.eq_of_le_of_card_ge (le_candidate E) (by omega)
    obtain ⟨g, hg, hn⟩ := hout
    exact hn (heq.symm ▸ hg)
  have hd := candidate_card_dvd_eight_of_span E hS
  have hle := Nat.le_of_dvd (by decide : 0 < 8) hd
  interval_cases h : Nat.card (candidate E) <;> simp_all

/-- Explicit geometric obligations for the normalizer-invariant extension.
This is a conditional reduction, not the completed four-group extension theorem. -/
theorem extension_of_span_of_moving_fixed (E : Subgroup G) (hE : Nat.card E = 4)
    (hS : Submodule.span (ZMod 3) (selected E) = ⊤)
    (hmove : ∃ g ∈ candidate E, ∃ x ∈ characterSpace E 1, g.val x ≠ x) :
    ∃ F : Subgroup G, IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
      E ≤ F ∧ Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (F : Set G) := by
  refine ⟨candidate E, candidate_elementary_of_span E hS, ?_, le_candidate E, normalizer_le E⟩
  apply candidate_card_eq_eight_of_span_of_outside E hE hS
  obtain ⟨g, hg, x, hx, hn⟩ := hmove
  refine ⟨g, hg, fun he => hn ?_⟩
  simpa using hx ⟨g,he⟩

end Atlas.G2.TernaryLocals.CharacterGeometry.CanonicalEight
