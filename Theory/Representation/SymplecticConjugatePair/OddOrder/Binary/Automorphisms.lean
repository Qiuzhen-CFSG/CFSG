module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFacts
public import Theory.SpecificGroups.SymplecticFour.Binary
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Parabolics
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.NormalizerGeometry

/-!
# Coverage of binary symplectic diagram-moving automorphisms

Each binary parabolic is `C₂ × S₄`. Its central involution places it inside a
two-local. The proved characteristic-two parabolic coverage and equal parabolic
orders identify that two-local with the parabolic itself. Automorphisms therefore
permute the two parabolic types, also over the binary field.

An automorphism preserving the point type has a projective intertwiner. The
proved suborbit geometry makes this intertwiner polar, and binary polar rigidity
makes the automorphism inner. Composing an automorphism that moves the diagram
with the graph map preserves the point type. Since the graph map squares to the
identity over the binary field, the original automorphism is inner times graph.
No semilinear-classification or automorphism-coverage premise remains.

Source: Aschbacher–Smith, F.1.12, printed pp.263–264, and the twist used in H.7,
printed p.389 of `refs/quasithin.pdf`, combined manuscript of 1 March 2004.
The imported normalizer geometry and field transport retain attribution for
their ATLAS adaptations; this module assembles their binary specializations.
-/

public section

open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open scoped Pointwise
namespace SymplecticConjugatePair.OddOrder.Binary
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private lemma contained_in_twoLocal (P : Subgroup (Sp F))
    (E : P ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) :
    ∃ M : Subgroup (Sp F), IsTwoLocal M ∧ P ≤ M := by
  let s : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  let z : P := E.symm (s, 1)
  have hz : orderOf z = 2 := by
    rw [show z = E.symm (s, 1) from rfl, E.symm.orderOf_eq]
    apply orderOf_eq_prime
    · change (s^2, (1 : Equiv.Perm (Fin 4))^2) = 1
      simp [s, pow_two]
    · intro h
      have := congrArg (fun p : Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4) => p.1 0) h
      simp [s] at this
  have hzc (x : P) : Commute z x := by
    apply E.injective
    rw [map_mul, map_mul]
    rw [show E z = (s, 1) from E.apply_symm_apply _]
    apply Prod.ext
    · exact (show ∀ p : Equiv.Perm (Fin 2), Equiv.swap 0 1 * p = p * Equiv.swap 0 1 by
        decide +kernel) (E x).1
    · simp
  let Q := Subgroup.zpowers (z : Sp F)
  have hQ : Q ≠ ⊥ := by
    intro h
    have hmem : (z : Sp F) ∈ Q := Subgroup.mem_zpowers _
    have hz1 : (z : Sp F) = 1 := by rwa [h, Subgroup.mem_bot] at hmem
    have hz1' : z = 1 := Subtype.ext hz1
    simp [hz1'] at hz
  have hp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
  refine ⟨Subgroup.normalizer (Q : Set (Sp F)), ⟨Q, hQ, hp, rfl⟩, ?_⟩
  intro x hx
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute (z : Sp F) x := congrArg Subtype.val (hzc ⟨x,hx⟩)
  exact (hc.zpow_left n).eq

private lemma binary_parabolic_isTwoLocal (hF : Nat.card F = 2)
    (P : Subgroup (Sp F)) (hP : P = pointParabolic ∨ P = planeParabolic) : IsTwoLocal P := by
  have hE : Nonempty (P ≃* (Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4))) := by
    rcases hP with rfl | rfl
    · exact ⟨Theory.SpecificGroups.SymplecticFour.Binary.pointParabolicEquivProd hF⟩
    · exact ⟨Theory.SpecificGroups.SymplecticFour.Binary.planeParabolicEquivProd hF⟩
  obtain ⟨E⟩ := hE
  obtain ⟨M, hM, hPM⟩ := contained_in_twoLocal P E
  obtain ⟨k, hk⟩ := twoLocal_parabolic_cover_of_charTwo M hM
  have hcard : Nat.card M ≤ Nat.card P := by
    have hmap : Nat.card (M.map (MulAut.conj k).toMonoidHom) = Nat.card M :=
      Subgroup.card_map_of_injective (MulAut.conj k).injective
    have hc := card_pointParabolic_eq_card_planeParabolic (F := F)
    rcases hk with hk | hk <;> have hh := Nat.card_le_card_of_injective (Subgroup.inclusion hk) (Subgroup.inclusion_injective hk) <;>
      rcases hP with rfl | rfl <;> omega
  have heq : P = M := Subgroup.eq_of_le_of_card_ge hPM hcard
  exact heq.symm ▸ hM

/-- Binary automorphisms permute the two actual parabolic conjugacy classes. -/
theorem binary_map_parabolic_eq_conjugate (hF : Nat.card F = 2) (τ : MulAut (Sp F))
    (P : Subgroup (Sp F)) (hP : P = pointParabolic ∨ P = planeParabolic) :
    ∃ Q : Subgroup (Sp F), (Q = pointParabolic ∨ Q = planeParabolic) ∧
      ∃ g : Sp F, P.map τ.toMonoidHom = Q.map (MulAut.conj g).toMonoidHom := by
  have hPlocal := binary_parabolic_isTwoLocal hF P hP
  obtain ⟨g, hg⟩ := twoLocal_parabolic_cover_of_charTwo
    (P.map τ.toMonoidHom) (Theory.GroupTheory.isTwoLocal_map_aut hPlocal τ)
  have hcard (Q : Subgroup (Sp F)) (hQ : Q = pointParabolic ∨ Q = planeParabolic) :
      Nat.card Q ≤ Nat.card ((P.map τ.toMonoidHom).map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective τ.injective]
    have hh := card_pointParabolic_eq_card_planeParabolic (F := F)
    rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl <;> omega
  have finish (Q : Subgroup (Sp F)) (hQ : Q = pointParabolic ∨ Q = planeParabolic)
      (hle : (P.map τ.toMonoidHom).map (MulAut.conj g).toMonoidHom ≤ Q) :
      P.map τ.toMonoidHom = Q.map (MulAut.conj g⁻¹).toMonoidHom := by
    have heq := Subgroup.eq_of_le_of_card_ge hle (hcard Q hQ)
    have hh := congrArg (fun R : Subgroup (Sp F) => (MulAut.conj g⁻¹) • R) heq
    change (MulAut.conj g⁻¹) • ((MulAut.conj g) • (τ • P)) =
      (MulAut.conj g⁻¹) • Q at hh
    change τ • P = (MulAut.conj g⁻¹) • Q
    simpa only [map_inv, inv_smul_smul] using hh
  rcases hg with hp | hp
  · exact ⟨pointParabolic, Or.inl rfl, g⁻¹, finish _ (Or.inl rfl) hp⟩
  · exact ⟨planeParabolic, Or.inr rfl, g⁻¹, finish _ (Or.inr rfl) hp⟩

open SemilinearClassification

private lemma inner_of_point_class (hF : Nat.card F = 2) (τ : MulAut (Sp F))
    (hτ : PreservesParabolicClass τ pointParabolic) : ∃ k : Sp F, τ = MulAut.conj k := by
  obtain ⟨φ, hφ⟩ := exists_projective_intertwiner τ hτ
  exact inner_of_polar_intertwining_of_card_two hF τ φ
    (orthogonal_iff_of_projective_intertwining τ φ hφ) hφ

/-- Every binary diagram-moving automorphism is inner times the constructed graph map. -/
theorem binary_moving_eq_inner_graph (hF : Nat.card F = 2) (τ : MulAut (Sp F))
    (hτ : ¬ PreservesDiagram τ) : ∃ k : Sp F, τ = MulAut.conj k * graphAut := by
  obtain ⟨Q, hQ, k, hk⟩ := binary_map_parabolic_eq_conjugate hF τ pointParabolic (Or.inl rfl)
  rcases hQ with rfl | rfl
  · obtain ⟨k, rfl⟩ := inner_of_point_class hF τ ⟨k,hk⟩
    exact False.elim (hτ (inner_preservesDiagram k))
  · have ha : PreservesParabolicClass (graphAut * τ) pointParabolic := by
      refine ⟨graphAut k, ?_⟩
      have he : graphAut (F := F) * MulAut.conj k = MulAut.conj (graphAut k) * graphAut := by
        ext x
        simp
      change (graphAut * τ) • pointParabolic (F := F) = (MulAut.conj (graphAut k)) • pointParabolic (F := F)
      change τ • pointParabolic (F := F) = (MulAut.conj k) • planeParabolic (F := F) at hk
      rw [mul_smul, hk, ← mul_smul, he, mul_smul]
      exact congrArg ((MulAut.conj (graphAut k)) • ·) graphAut_map_plane
    obtain ⟨u, hu⟩ := inner_of_point_class hF (graphAut * τ) ha
    refine ⟨graphAut u, ?_⟩
    have hs : graphAut (F := F) ^ 2 = 1 := by
      rw [graphAut_square, fieldAutomorphism_eq_one_of_card_two hF]
    apply MulEquiv.ext
    intro x
    have hh := congrArg (fun a : MulAut (Sp F) => a x) hu
    change graphAut (τ x) = u*x*u⁻¹ at hh
    have hh' := congrArg graphAut hh
    have htwice (y : Sp F) : graphAut (graphAut y) = y := by
      exact congrArg (fun a : MulAut (Sp F) => a y) hs
    change τ x = graphAut u * graphAut x * (graphAut u)⁻¹
    simpa only [htwice, map_mul, map_inv] using hh'

end SymplecticConjugatePair.OddOrder.Binary
