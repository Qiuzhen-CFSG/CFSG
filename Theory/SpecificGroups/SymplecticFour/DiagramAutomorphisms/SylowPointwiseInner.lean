module

public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearLocalKernel
public import Theory.GroupAction.SylowPointwiseInner

/-!
# Automorphisms fixing a nonbinary symplectic Sylow subgroup pointwise

The two standard parabolic radicals lie inside the concrete unipotent Sylow.
An automorphism fixing that Sylow pointwise therefore fixes both radicals and
both of their full normalizers, hence preserves the diagram. Apply the explicit
premise that diagram-preserving automorphisms are inner times entrywise field
maps. Comparing the long-root matrix at parameters `t` and `1` forces the field
map to fix `t`. The remaining conjugating matrix centralizes the point radical;
its proved self-centralizing property places the matrix in the original Sylow.
Sylow conjugacy gives the result for every Sylow, with an actual matrix witness.

This proves more than the two-element assertion: no order hypothesis on the
pointwise-fixing automorphism is needed. The semilinear classification is the
only additional premise; its construction belongs to the classification owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 16.1.6, printed p.1172 of
`refs/quasithin.pdf`, for Sp₄(2ⁿ), n > 1. This module does not treat the
separate derived binary exception.
-/

public section

open Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)

omit [Finite F] in
private theorem point_radical_le : pointRadicalAmbient (F := F) ≤ unipotent := by
  rintro _ ⟨q, hq, rfl⟩
  rw [pointRadical_eq_element q hq]
  simp [mem_unipotent_iff, mem_borel_iff, pointRadicalElement, pointRadicalMatrix]

omit [Finite F] [CharP F 2] in
private theorem plane_radical_le : planeRadicalAmbient (F := F) ≤ unipotent := by
  rintro _ ⟨q, hq, rfl⟩
  rw [mem_unipotent_iff, mem_borel_iff]
  have hm := Plane.radical_matrix (⟨q, hq⟩ : Plane.radical)
  change (q.val.val (.inl 1) (.inl 0) = 0 ∧
    (∀ i j, q.val.val (.inr i) (.inl j) = 0)) ∧
    q.val.val (.inl 0) (.inl 0) = 1 ∧ q.val.val (.inl 1) (.inl 1) = 1
  rw [hm]
  simp [Matrix.fromBlocks]

private theorem map_eq_of_fixed {G : Type*} [Group G] (a : MulAut G) (H : Subgroup G)
    (h : ∀ x ∈ H, a x = x) : H.map a.toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    change a x ∈ H
    rw [h x hx]
    exact hx
  · intro x hx
    exact ⟨x, hx, h x hx⟩

include hcard hn in
/-- Pointwise fixation of the standard Sylow fixes both actual full parabolics. -/
theorem unipotent_fixed_parabolics (a : MulAut (Sp F))
    (ha : ∀ x ∈ unipotent (F := F), a x = x) :
    pointParabolic.map a.toMonoidHom = pointParabolic ∧
    planeParabolic.map a.toMonoidHom = planeParabolic := by
  have hp := map_eq_of_fixed a pointRadicalAmbient (fun x hx => ha x (point_radical_le hx))
  have hq := map_eq_of_fixed a planeRadicalAmbient (fun x hx => ha x (plane_radical_le hx))
  constructor
  · rw [← pointRadicalAmbient_normalizer hcard hn,
      Subgroup.map_normalizer_eq_of_bijective _ a.bijective, hp]
  · rw [← planeRadicalAmbient_normalizer hcard hn,
      Subgroup.map_normalizer_eq_of_bijective _ a.bijective, hq]

include hcard hn in
/-- The two radicals recover the diagram types from the pointwise-fixed Sylow. -/
theorem unipotent_fixed_preservesDiagram (a : MulAut (Sp F))
    (ha : ∀ x ∈ unipotent (F := F), a x = x) : PreservesDiagram a := by
  obtain ⟨hp, hq⟩ := unipotent_fixed_parabolics hcard hn a ha
  constructor
  · refine ⟨1, ?_⟩
    rw [map_one]
    change pointParabolic.map a.toMonoidHom = pointParabolic.map (MonoidHom.id (Sp F))
    simpa using hp
  · refine ⟨1, ?_⟩
    rw [map_one]
    change planeParabolic.map a.toMonoidHom = planeParabolic.map (MonoidHom.id (Sp F))
    simpa using hq

include hcard hn in
/-- The parameters of a positive long root detect the entrywise field automorphism. -/
theorem semilinear_fixing_unipotent_field_eq_refl (g : Sp F) (σ : F ≃+* F)
    (ha : ∀ x ∈ unipotent (F := F), (MulAut.conj g * fieldAutomorphism σ) x = x) :
    σ = RingEquiv.refl F := by
  have hP := (unipotent_fixed_parabolics hcard hn _ ha).1
  have hL := pointLocal_map hcard hn _ hP
  have hg := point_semilinear_mem_parabolic hcard hn g σ hL
  have hne : g.val (.inl 0) (.inl 0) ≠ 0 := by
    rw [← determinantCharacter_point_coe ⟨g, hg⟩]
    exact Units.ne_zero _
  have hc (t : F) : g * rootElement 0 (σ t) = rootElement 0 t * g := by
    have h := ha (rootElement 0 t) (positive_root_mem_unipotent 0 t (by simp))
    change g * fieldAutomorphism σ (rootElement 0 t) * g⁻¹ = rootElement 0 t at h
    rw [ExceptionalGraph.fieldAutomorphism_root] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have he (t : F) := congrArg (fun x : Sp F => x.val (.inl 0) (.inr 0)) (hc t)
  have he' (t : F) : g.val (.inl 0) (.inl 0) * σ t = t * g.val (.inr 0) (.inr 0) := by
    have h := he t
    simp [rootElement, rootMatrix, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.single, Matrix.one_apply] at h
    linear_combination h
  have he1 : g.val (.inl 0) (.inl 0) = g.val (.inr 0) (.inr 0) := by
    simpa using he' 1
  apply RingEquiv.ext
  intro t
  change σ t = t
  apply mul_left_cancel₀ hne
  simpa only [← he1, mul_comm] using he' t

include hcard hn in
/-- Under diagram-preserving semilinear coverage, the pointwise stabilizer of
the standard Sylow consists of conjugations by elements of that Sylow.
No order hypothesis on the automorphism is needed. -/
theorem aut_fixing_unipotent_inner
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : MulAut (Sp F)) (ha : ∀ x ∈ unipotent (F := F), a x = x) :
    ∃ g ∈ unipotent (F := F), a = MulAut.conj g := by
  obtain ⟨g, σ, he⟩ := hclass a (unipotent_fixed_preservesDiagram hcard hn a ha)
  have hσ := semilinear_fixing_unipotent_field_eq_refl hcard hn g σ (he ▸ ha)
  have hf : fieldAutomorphism (RingEquiv.refl F) = (1 : MulAut (Sp F)) := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hσ, hf, mul_one] at he
  refine ⟨g, point_radical_le (pointRadicalAmbient_selfCentralizing hcard hn ?_), he⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := ha x (point_radical_le hx)
  rw [he] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

include hcard hn in
/-- Sylow conjugacy transports the matrix calculation to any Sylow two-subgroup,
retaining its actual conjugating element inside the specified Sylow. -/
theorem aut_fixing_sylow_inner
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (P : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (ha : ∀ x ∈ (P : Subgroup (Sp F)), a x = x) :
    ∃ g ∈ (P : Subgroup (Sp F)), a = MulAut.conj g := by
  exact MulAut.fixing_inner_sylow (unipotentSylow hcard (by omega)) P
    (aut_fixing_unipotent_inner hcard hn hclass) a ha

include hcard hn in
/-- The nonbinary symplectic case of source Lemma 16.1.6 for arbitrary two-power
order. The stronger pointwise-stabilizer theorem makes an involution reduction
unnecessary. The sole classification premise remains explicit. -/
theorem twoPower_fixes_sylow_inner
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (P : Sylow 2 (Sp F)) (a : MulAut (Sp F)) {k : ℕ}
    (_hpow : a ^ (2 ^ k) = 1)
    (hfix : ∀ x ∈ (P : Subgroup (Sp F)), a x = x) :
    ∃ g ∈ (P : Subgroup (Sp F)), a = MulAut.conj g :=
  aut_fixing_sylow_inner hcard hn hclass P a hfix

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
