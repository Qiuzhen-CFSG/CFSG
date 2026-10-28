module

public import Theory.Representation.InvertedCubicTensor

/-!
# Separating a quadratic product action

A nonidentity involution normally generates S₃. Thus a mixed quadratic
identity for one transposition in each factor extends to all displacements
of the two factors: each factor fixes the other factor's commutator space.
Cubic averaging expresses every vector as a sum of the two commutator
spaces when the common A₃ × A₃ fixed space vanishes. Their intersection
is zero, and each is precisely the opposite factor's fixed space.

The summands are subrepresentations of the original ordered product action.
Only the common odd fixed space is assumed zero; either factor may have
nonzero fixed space on the ambient module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.2.6(5), printed p.336, PDF p.347, 1 March 2004 manuscript.
-/

@[expose] public section

open InvertedCubicTensor
namespace Representation.BinaryQuadraticPair.ProductDecomposition
variable {V : Type*} [AddCommGroup V] [Module F V]

private theorem conjugate_words : ∀ t : S₃, t * t = 1 → t ≠ 1 → ∀ g : S₃,
    g = 1 ∨ g = t ∨ g = cubic * t * cubic⁻¹ ∨
      g = (cubic * cubic) * t * (cubic * cubic)⁻¹ ∨
      g = t * (cubic * t * cubic⁻¹) ∨ g = (cubic * t * cubic⁻¹) * t := by
  decide +kernel

private theorem fixed_of_invariant (σ : Representation F S₃ V) (W : Submodule F V)
    (hW : ∀ g v, v ∈ W → σ g v ∈ W) (t : S₃) (ht : t * t = 1) (hn : t ≠ 1)
    (hf : ∀ v ∈ W, σ t v = v) : ∀ g v, v ∈ W → σ g v = v := by
  have hc (a : S₃) (v : V) (hv : v ∈ W) : σ (a * t * a⁻¹) v = v := by
    simp only [map_mul, Module.End.mul_apply, hf _ (hW _ _ hv)]
    change (σ a * σ a⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro g v hv
  rcases conjugate_words t ht hn g with rfl | rfl | rfl | rfl | rfl | rfl
  · simp
  · exact hf v hv
  · exact hc cubic v hv
  · exact hc (cubic * cubic) v hv
  · rw [map_mul, Module.End.mul_apply, hc cubic v hv, hf v hv]
  · rw [map_mul, Module.End.mul_apply, hf v hv, hc cubic v hv]

private theorem extend_displacement (σ τ : Representation F S₃ V)
    (hc : ∀ g h v, σ g (τ h v) = τ h (σ g v))
    (t : S₃) (ht : t * t = 1) (hn : t ≠ 1) (u : S₃)
    (hf : ∀ v, σ t (τ u v - v) = τ u v - v) :
    ∀ g v, σ g (τ u v - v) = τ u v - v := by
  have hW : ∀ g v, v ∈ LinearMap.range (τ u - 1) →
      σ g v ∈ LinearMap.range (τ u - 1) := by
    rintro g _ ⟨v, rfl⟩
    refine ⟨σ g v, ?_⟩
    change τ u (σ g v) - σ g v = σ g (τ u v - v)
    rw [map_sub, hc]
  intro g v
  simpa only [LinearMap.sub_apply, Module.End.one_apply] using
    fixed_of_invariant σ (LinearMap.range (τ u - 1)) hW t ht hn
      (by rintro _ ⟨w, rfl⟩; exact hf w) g _ ⟨v, rfl⟩

private theorem displacement_symm (σ τ : V →ₗ[F] V)
    (hc : ∀ v, σ (τ v) = τ (σ v))
    (hf : ∀ v, σ (τ v - v) = τ v - v) : ∀ v, τ (σ v - v) = σ v - v := by
  intro v
  have h := hf v
  rw [map_sub, hc] at h
  rw [map_sub]
  exact sub_eq_sub_iff_add_eq_add.mpr (by
    have := sub_eq_sub_iff_add_eq_add.mp h
    simpa only [add_comm] using this)

/-- Mixed quadraticity extends from the marked transpositions to both whole factors. -/
theorem mixed_all (ρ : Representation F (S₃ × S₃) V)
    (t₁ t₂ : S₃) (hs₁ : t₁ * t₁ = 1) (hn₁ : t₁ ≠ 1)
    (hs₂ : t₂ * t₂ = 1) (hn₂ : t₂ ≠ 1)
    (hm : (ρ (t₁, 1) - 1) * (ρ (1, t₂) - 1) = 0) :
    ∀ g h v, leftAction ρ g (rightAction ρ h v - v) = rightAction ρ h v - v := by
  have hf : ∀ v, leftAction ρ t₁ (rightAction ρ t₂ v - v) = rightAction ρ t₂ v - v := by
    intro v
    exact sub_eq_zero.mp (LinearMap.congr_fun hm v)
  have he := extend_displacement (leftAction ρ) (rightAction ρ) (product_commute ρ)
    t₁ hs₁ hn₁ t₂ hf
  intro g h
  have he' := extend_displacement (rightAction ρ) (leftAction ρ)
    (fun h g v => (product_commute ρ g h v).symm) t₂ hs₂ hn₂ g
    (displacement_symm _ _ (product_commute ρ g t₂) (he g)) h
  exact displacement_symm _ _ (fun v => (product_commute ρ g h v).symm) he'

private lemma double (v : V) : v + v = 0 := by
  simpa only [show (1 : F) + 1 = 0 by decide, zero_smul, one_smul] using
    (add_smul (1 : F) 1 v).symm

private lemma neg (v : V) : -v = v := neg_eq_iff_add_eq_zero.mpr (double v)

private def norm (σ : Representation F S₃ V) : V →ₗ[F] V :=
  1 + σ cubic + σ cubic * σ cubic

private lemma norm_apply (σ : Representation F S₃ V) (v : V) :
    norm σ v = v + σ cubic v + σ cubic (σ cubic v) := rfl

private lemma norm_fixed (σ : Representation F S₃ V) (v : V) :
    σ cubic (norm σ v) = norm σ v := by
  have hc : σ cubic (σ cubic (σ cubic v)) = v := by
    change (σ cubic * σ cubic * σ cubic) v = v
    rw [← map_mul, ← map_mul, cubic_cube, map_one, Module.End.one_apply]
  simp only [norm_apply, map_add, hc]
  abel

private lemma norm_commute (σ τ : Representation F S₃ V)
    (hc : ∀ g h v, σ g (τ h v) = τ h (σ g v)) (g : S₃) (v : V) :
    σ g (norm τ v) = norm τ (σ g v) := by
  simp only [norm_apply, map_add, hc]

private lemma alternating_words (g : S₃) (hg : g ∈ alternatingGroup (Fin 3)) :
    g = 1 ∨ g = cubic ∨ g = cubic * cubic := by
  have h : ∀ g : S₃, Equiv.Perm.sign g = 1 →
      g = 1 ∨ g = cubic ∨ g = cubic * cubic := by decide +kernel
  exact h g (Equiv.Perm.mem_alternatingGroup.mp hg)

open BinaryOffender

/-- The literal ordered factor subgroups. -/
abbrev leftFactor : Subgroup (S₃ × S₃) := (⊤ : Subgroup S₃).prod ⊥
abbrev rightFactor : Subgroup (S₃ × S₃) := (⊥ : Subgroup S₃).prod ⊤

variable (ρ : Representation F (S₃ × S₃) V)

private theorem common_zero
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥)
    (v : V) (hl : leftAction ρ cubic v = v) (hr : rightAction ρ cubic v = v) : v = 0 := by
  have hv : v ∈ fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) := by
    rintro ⟨⟨g, h⟩, hg, hh⟩
    have hfl : ∀ g ∈ alternatingGroup (Fin 3), leftAction ρ g v = v := by
      intro g hg
      rcases alternating_words g hg with rfl | rfl | rfl
      · simp
      · exact hl
      · simp only [map_mul, Module.End.mul_apply, hl]
    have hfr : ∀ h ∈ alternatingGroup (Fin 3), rightAction ρ h v = v := by
      intro h hh
      rcases alternating_words h hh with rfl | rfl | rfl
      · simp
      · exact hr
      · simp only [map_mul, Module.End.mul_apply, hr]
    change ρ (g, h) v = v
    have he : (g, h) = (g, 1) * (1, h) := by simp
    rw [he, map_mul, Module.End.mul_apply]
    exact (congrArg (leftAction ρ g) (hfr h hh)).trans (hfl g hg)
  simpa only [h0, Submodule.mem_bot] using hv

private lemma left_mem (g : S₃) (v : V) :
    leftAction ρ g v - v ∈ subspaceCommutator ρ ⊤ leftFactor :=
  Submodule.subset_span ⟨(g, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩,
    v, Submodule.mem_top, rfl⟩

private lemma right_mem (g : S₃) (v : V) :
    rightAction ρ g v - v ∈ subspaceCommutator ρ ⊤ rightFactor :=
  Submodule.subset_span ⟨(1, g), ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩,
    v, Submodule.mem_top, rfl⟩

private lemma norm_sub (σ : Representation F S₃ V) (v : V) :
    norm σ v - v = (σ cubic v - v) + (σ (cubic * cubic) v - v) := by
  simp only [norm_apply, sub_eq_add_neg, neg, map_mul, Module.End.mul_apply]
  abel

private theorem moved_sup
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    subspaceCommutator ρ ⊤ leftFactor ⊔ subspaceCommutator ρ ⊤ rightFactor = ⊤ := by
  apply top_unique
  intro v _
  have hn : norm (rightAction ρ) (norm (leftAction ρ) v) = 0 := by
    apply common_zero ρ h0
    · rw [norm_commute _ _ (product_commute ρ), norm_fixed]
    · exact norm_fixed _ _
  have hl : v - norm (leftAction ρ) v ∈ subspaceCommutator ρ ⊤ leftFactor := by
    rw [← neg_sub, norm_sub]
    exact Submodule.neg_mem _ (Submodule.add_mem _ (left_mem ρ _ _) (left_mem ρ _ _))
  have hr : norm (leftAction ρ) v ∈ subspaceCommutator ρ ⊤ rightFactor := by
    have hh := Submodule.add_mem _ (right_mem ρ cubic (norm (leftAction ρ) v))
      (right_mem ρ (cubic * cubic) (norm (leftAction ρ) v))
    rw [← norm_sub, hn, zero_sub, neg] at hh
    exact hh
  exact Submodule.mem_sup.mpr ⟨_, hl, _, hr, sub_add_cancel _ _⟩

private theorem moved_le_fixed
    (hm : ∀ g h v, leftAction ρ g (rightAction ρ h v - v) = rightAction ρ h v - v) :
    subspaceCommutator ρ ⊤ leftFactor ≤ fixedSpace ρ rightFactor ∧
      subspaceCommutator ρ ⊤ rightFactor ≤ fixedSpace ρ leftFactor := by
  constructor
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, h⟩, ⟨_, hh⟩, v, _, rfl⟩ ⟨⟨a, b⟩, ha, _⟩
    have hh : h = 1 := hh
    have ha : a = 1 := ha
    subst h; subst a
    exact displacement_symm _ _ (product_commute ρ g b) (hm g b) v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, h⟩, ⟨hg, _⟩, v, _, rfl⟩ ⟨⟨a, b⟩, _, hb⟩
    have hg : g = 1 := hg
    have hb : b = 1 := hb
    subst g; subst b
    exact hm a h v

private theorem fixed_disjoint
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    Disjoint (fixedSpace ρ leftFactor) (fixedSpace ρ rightFactor) := by
  rw [Submodule.disjoint_def]
  intro v hl hr
  exact common_zero ρ h0 v
    (hl ⟨(cubic, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩⟩)
    (hr ⟨(1, cubic), ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩⟩)

/-- Each factor commutator is exactly the fixed space of the opposite factor. -/
theorem moved_eq_fixed
    (hm : ∀ g h v, leftAction ρ g (rightAction ρ h v - v) = rightAction ρ h v - v)
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    subspaceCommutator ρ ⊤ leftFactor = fixedSpace ρ rightFactor ∧
      subspaceCommutator ρ ⊤ rightFactor = fixedSpace ρ leftFactor := by
  obtain ⟨hl, hr⟩ := moved_le_fixed ρ hm
  have hd := fixed_disjoint ρ h0
  have hs := moved_sup ρ h0
  have he {A B C D : Submodule F V} (hAC : A ≤ C) (hBD : B ≤ D)
      (hCD : Disjoint C D) (hAB : A ⊔ B = ⊤) : A = C := by
    apply le_antisymm hAC
    intro v hv
    have hv' : v ∈ A ⊔ B := hAB.symm ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv'
    have hbC : b ∈ C := by
      have hh := C.sub_mem hv (hAC ha)
      simpa only [← hab, add_sub_cancel_left] using hh
    have hb0 := Submodule.disjoint_def.mp hCD b hbC (hBD hb)
    simpa only [← hab, hb0, add_zero] using ha
  exact ⟨he hl hr hd.symm hs, he hr hl hd (by rwa [sup_comm])⟩

/-- The first summand is the subrepresentation fixed by the second factor. -/
noncomputable def leftSummand : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ rightFactor
  apply_mem_toSubmodule := Representation.le_comap_invariants ρ rightFactor

/-- The second summand is the subrepresentation fixed by the first factor. -/
noncomputable def rightSummand : Subrepresentation ρ where
  toSubmodule := fixedSpace ρ leftFactor
  apply_mem_toSubmodule := Representation.le_comap_invariants ρ leftFactor

/-- The two invariant fixed spaces form a direct sum equal to the whole module. -/
theorem summands_isCompl
    (hm : ∀ g h v, leftAction ρ g (rightAction ρ h v - v) = rightAction ρ h v - v)
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    IsCompl (leftSummand ρ).toSubmodule (rightSummand ρ).toSubmodule := by
  constructor
  · exact (fixed_disjoint ρ h0).symm
  · apply codisjoint_iff.mpr
    change fixedSpace ρ rightFactor ⊔ fixedSpace ρ leftFactor = ⊤
    rw [← (moved_eq_fixed ρ hm h0).1, ← (moved_eq_fixed ρ hm h0).2]
    exact moved_sup ρ h0

/-- The first cubic has no fixed vector on the first summand. -/
theorem leftSummand_fixedFree
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    ∀ v, leftAction (leftSummand ρ).toRepresentation cubic v = v → v = 0 := by
  intro v hv
  apply Subtype.ext
  exact common_zero ρ h0 v.val (congrArg Subtype.val hv)
    (v.property ⟨(1, cubic), ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩⟩)

/-- The second cubic has no fixed vector on the second summand. -/
theorem rightSummand_fixedFree
    (h0 : fixedSpace ρ ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))) = ⊥) :
    ∀ v, rightAction (rightSummand ρ).toRepresentation cubic v = v → v = 0 := by
  intro v hv
  apply Subtype.ext
  exact common_zero ρ h0 v.val
    (v.property ⟨(cubic, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩⟩)
    (congrArg Subtype.val hv)

/-- The second factor acts trivially on the first summand. -/
theorem leftSummand_action (g : S₃ × S₃) (v : (leftSummand ρ).toSubmodule) :
    (leftSummand ρ).toRepresentation g v =
      leftAction (leftSummand ρ).toRepresentation g.1 v := by
  apply Subtype.ext
  change ρ g v.val = ρ (g.1, 1) v.val
  have he : g = (g.1, 1) * (1, g.2) := by simp
  conv_lhs => rw [he, map_mul, Module.End.mul_apply]
  exact congrArg (ρ (g.1, 1))
    (v.property ⟨(1, g.2), ⟨Subgroup.one_mem _, Subgroup.mem_top _⟩⟩)

/-- The first factor acts trivially on the second summand. -/
theorem rightSummand_action (g : S₃ × S₃) (v : (rightSummand ρ).toSubmodule) :
    (rightSummand ρ).toRepresentation g v =
      rightAction (rightSummand ρ).toRepresentation g.2 v := by
  apply Subtype.ext
  change ρ g v.val = ρ (1, g.2) v.val
  have he : g = (1, g.2) * (g.1, 1) := by simp
  conv_lhs => rw [he, map_mul, Module.End.mul_apply]
  exact congrArg (ρ (1, g.2))
    (v.property ⟨(g.1, 1), ⟨Subgroup.mem_top _, Subgroup.one_mem _⟩⟩)

end Representation.BinaryQuadraticPair.ProductDecomposition
