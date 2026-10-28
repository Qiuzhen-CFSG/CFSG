module

public import Theory.Representation.SymplecticNaturalNormalizer.Centralizers
public import Theory.GroupTheory.CentricRadicalObstructions

/-!
# Field-line fixation removes the outer symplectic action

A binary natural normalizer is a scalar times an inner-field operator. If it
fixes every vector of a nonzero field line, semilinearity forces the field
automorphism to be the identity. Its conjugation on the matrix group is
therefore inner. For a centric normal component acting naturally, this implies
membership in that very component, with the ambient action retained.

Source: the containment Tstar <= Mstar in MS93 Section 7, p.933, using the
natural-normalizer theorem and the enlarged seed of (3.4), pp.868–869.
-/

public section
open Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open SymplecticConjugatePair.Ambient
open SymplecticConjugatePair.Ambient.Normalizer

namespace SymplecticNaturalNormalizer
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The field twist of an actual binary natural normalizer. -/
theorem exists_field_twist (s : naturalNormalizer (F := F)) :
    ∃ σ : F ≃+* F, ∀ (c : F) w, s.val (c • w) = σ c • s.val w := by
  obtain ⟨a,g,σ,he⟩ := naturalNormalizer_semilinear s.val s.property
  refine ⟨σ,fun c w => ?_⟩
  have hf : fieldVector σ (c • w) = σ c • fieldVector σ w := by
    funext i
    exact map_mul σ c (w i)
  rw [he,he]
  change a.val • symplecticNatural 2 g (fieldVector σ (c • w)) =
    σ c • (a.val • symplecticNatural 2 g (fieldVector σ w))
  rw [hf,map_smul,smul_comm]

/-- The whole ambient action normalizes the literal natural component image. -/
theorem operator_mem_naturalNormalizer
    {G : Type*} [Group G] (B : Subgroup G) [B.Normal]
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (x : G) : linearAction ρ x ∈ naturalNormalizer := by
  have hBe (b : B) : linearAction ρ (b:G) = naturalHom (e b) := by
    apply LinearEquiv.ext
    intro w
    exact hB b w
  have himage : B.map (linearAction ρ) = naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      rw [hBe ⟨b,hb⟩]
      exact naturalHom_mem hcard _
    · rintro _ ⟨b,rfl⟩
      refine ⟨e.symm b.val,(e.symm b.val).property,?_⟩
      rw [hBe,e.apply_symm_apply]
      rfl
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  change linearAction ρ x ∈ Subgroup.normalizer (naturalDerivedImage (F := F) : Set _)
  rw [← himage]
  exact B.le_normalizer_map (linearAction ρ) (Subgroup.mem_map_of_mem _ hxN)

theorem scalar_symplectic_of_fixes_field_line
    (s : naturalNormalizer (F := F)) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ c : F, s.val (c • v) = c • v) :
    ∃ (a : Fˣ) (g : Sp F), ∀ w, s.val w = a.val • symplecticNatural 2 g w := by
  obtain ⟨a,g,σ,he⟩ := naturalNormalizer_semilinear s.val s.property
  have hsemi (c : F) (w : Vector F) :
      innerFieldVector g σ (c • w) = σ c • innerFieldVector g σ w := by
    change symplecticNatural 2 g (fieldVector σ (c • w)) = _
    have hf : fieldVector σ (c • w) = σ c • fieldVector σ w := by
      funext i
      exact map_mul σ c (w i)
    rw [hf, map_smul]
    rfl
  have hs (c : F) (w : Vector F) : s.val (c • w) = σ c • s.val w := by
    rw [he, he, hsemi, smul_comm]
  have hσ : σ = RingEquiv.refl F := by
    apply RingEquiv.ext
    intro c
    apply smul_left_injective F hv
    have hh := hs c v
    rw [hfix, show s.val v = v by simpa using hfix 1] at hh
    exact hh.symm
  refine ⟨a,g,fun w => ?_⟩
  rw [he,hσ]
  rfl

theorem conjugation_inner_of_fixes_field_line
    (hcard : 2 < Nat.card F) (s : naturalNormalizer (F := F))
    (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ c : F, s.val (c • v) = c • v) :
    ∃ g : Sp F, conjugation hcard s = MulAut.conj g := by
  obtain ⟨a,g,he⟩ := scalar_symplectic_of_fixes_field_line s v hv hfix
  refine ⟨g,conjugation_eq_of_intertwines hcard s _ ?_⟩
  intro x w
  rw [he,he]
  change a.val • symplecticNatural 2 g (symplecticNatural 2 x w) =
    symplecticNatural 2 (g*x*g⁻¹) (a.val • symplecticNatural 2 g w)
  rw [map_smul]
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

theorem mem_component_of_fixes_field_line
    {G : Type*} [Group G] (B : Subgroup G) [B.Normal]
    (hcent : Subgroup.centralizer (B : Set G) ≤ B)
    (hcard : 2 < Nat.card F) (e : B ≃* Sp F)
    (ρ : Representation (ZMod 2) G (Vector F))
    (hB : ∀ b : B, ∀ w, ρ (b:G) w = symplecticNatural 2 (e b) w)
    (x : G) (v : Vector F) (hv : v ≠ 0)
    (hfix : ∀ c : F, ρ x (c • v) = c • v) : x ∈ B := by
  have hBe (b : B) : linearAction ρ (b:G) = naturalHom (e b) := by
    apply LinearEquiv.ext
    intro w
    exact hB b w
  have himage : B.map (linearAction ρ) = naturalDerivedImage := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      rw [hBe ⟨b,hb⟩]
      exact naturalHom_mem hcard _
    · rintro _ ⟨b,rfl⟩
      refine ⟨e.symm b.val,(e.symm b.val).property,?_⟩
      rw [hBe,e.apply_symm_apply]
      rfl
  have hxN : x ∈ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    trivial
  have hn : linearAction ρ x ∈ naturalNormalizer := by
    change linearAction ρ x ∈ Subgroup.normalizer (naturalDerivedImage (F := F) : Set _)
    rw [← himage]
    exact B.le_normalizer_map (linearAction ρ) (Subgroup.mem_map_of_mem _ hxN)
  let s : naturalNormalizer (F := F) := ⟨linearAction ρ x,hn⟩
  obtain ⟨g,hg⟩ := conjugation_inner_of_fixes_field_line hcard s v hv hfix
  have hc (b : B) : e (MulAut.conjNormal x b) = conjugation hcard s (e b) := by
    apply naturalHom_injective
    rw [← hBe]
    change linearAction ρ (x * (b:G) * x⁻¹) = _
    rw [map_mul,map_mul,map_inv,hBe]
    exact (conjugation_apply hcard s (e b)).symm
  apply Subgroup.mem_of_normalizerMonoidHom_mem_inner B hcent ⟨x,hxN⟩
  refine ⟨e.symm g,?_⟩
  apply MulEquiv.ext
  intro b
  apply e.injective
  change e (e.symm g * b * (e.symm g)⁻¹) = e (MulAut.conjNormal x b)
  rw [hc,hg,map_mul,map_mul,map_inv,e.apply_symm_apply]
  rfl

end SymplecticNaturalNormalizer
