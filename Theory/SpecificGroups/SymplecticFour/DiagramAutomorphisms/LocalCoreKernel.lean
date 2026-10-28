module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Rigidity
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore

/-!
# The local two-core detects trivial symplectic quotient actions

A two-power automorphism preserving a determinant-one local factor and
acting trivially on its two-core quotient is conjugation by a member of
the actual two-core. The established semilinear kernel calculation gives
an inner representative in the local factor; the trivial center of its
SL₂ quotient puts that representative in the kernel. Fixing one local
factor also preserves its full parabolic and hence the two-node diagram.

Source: Aschbacher--Smith F.1.12, printed pp.263--264, used in the
ordinary 15.1.20(3b) parabolic placement, printed pp.1096--1097.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem inner_local_mem_core
    (K : Subgroup (Sp F)) (q : K →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 K)
    (a : MulAut (Sp F)) (hK : K.map a.toMonoidHom = K)
    (hc : ∀ x : K, restrict a K hK x / x ∈ pCore 2 K)
    (k : K) (he : a = MulAut.conj k.val) : k ∈ pCore 2 K := by
  rw [←hk]
  apply (mem_bot.mp : q k ∈ (⊥ : Subgroup SL(2,F)) → q k = 1)
  rw [←Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨x,rfl⟩ := hq y
  have hh := hc x
  rw [←hk,MonoidHom.mem_ker,map_div,div_eq_one] at hh
  have hx : restrict a K hK x = k*x*k⁻¹ := by
    apply Subtype.ext
    change a x.val = _
    rw [he]
    rfl
  rw [hx,map_mul,map_mul,map_inv] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- A two-power automorphism fixing the point quotient is induced by its actual two-core. -/
theorem point_core_inner_of_quotient_trivial {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : MulAut (Sp F)) (hK : pointLocal.map a.toMonoidHom = pointLocal)
    (htwo : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x : pointLocal (F := F),
      restrict a pointLocal hK x / x ∈ pCore 2 pointLocal) :
    ∃ k : pointLocal (F := F), k ∈ pCore 2 pointLocal ∧ a = MulAut.conj k.val := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hP : pointParabolic.map a.toMonoidHom = pointParabolic := by
    rw [←pointLocal_normalizer hF hn,map_equiv_normalizer_eq,hK]
  have hd := preservesDiagram_of_one_parabolic_class hlarge a
    (Or.inl ⟨1,by rw [map_one]; change pointParabolic.map a.toMonoidHom = pointParabolic.map (MonoidHom.id _) ; simpa only [Subgroup.map_id] using hP⟩)
  have hact : pointSL2Action hF hn a hK = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := pointQuotient_surjective y
    rw [pointSL2Action_quotient]
    have hh := hc x
    rw [pointLocal_core_eq hF hn] at hh
    change pointQuotient (restrict a pointLocal hK x / x) = 1 at hh
    change pointQuotient (restrict a pointLocal hK x) = pointQuotient x
    exact div_eq_one.mp (by simpa only [map_div] using hh)
  obtain ⟨k,he⟩ := pointSL2Action_kernel_of_preservesDiagram hF hn a hd hK htwo hact
  exact ⟨k,inner_local_mem_core pointLocal pointQuotient pointQuotient_surjective
    (pointLocal_core_eq hF hn).symm a hK hc k he,he⟩

/-- A two-power automorphism fixing the plane quotient is induced by its actual two-core. -/
theorem plane_core_inner_of_quotient_trivial {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1<n)
    (a : MulAut (Sp F)) (hK : planeLocal.map a.toMonoidHom = planeLocal)
    (htwo : ∃ k : ℕ, a^(2^k)=1)
    (hc : ∀ x : planeLocal (F := F),
      restrict a planeLocal hK x / x ∈ pCore 2 planeLocal) :
    ∃ k : planeLocal (F := F), k ∈ pCore 2 planeLocal ∧ a = MulAut.conj k.val := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2:ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) hn)
  have hP : planeParabolic.map a.toMonoidHom = planeParabolic := by
    rw [←planeLocal_normalizer hF hn,map_equiv_normalizer_eq,hK]
  have hd := preservesDiagram_of_one_parabolic_class hlarge a
    (Or.inr ⟨1,by rw [map_one]; change planeParabolic.map a.toMonoidHom = planeParabolic.map (MonoidHom.id _); simpa only [Subgroup.map_id] using hP⟩)
  have hact : planeSL2Action hF hn a hK = 1 := by
    apply MulEquiv.ext
    intro y
    obtain ⟨x,rfl⟩ := Plane.quotientMap_surjective y
    rw [planeSL2Action_quotient]
    have hh := hc x
    rw [planeLocal_core_eq hF hn] at hh
    change Plane.quotientMap (restrict a planeLocal hK x / x) = 1 at hh
    change Plane.quotientMap (restrict a planeLocal hK x) = Plane.quotientMap x
    exact div_eq_one.mp (by simpa only [map_div] using hh)
  obtain ⟨k,he⟩ := planeSL2Action_kernel_of_preservesDiagram hF hn a hd hK htwo hact
  exact ⟨k,inner_local_mem_core planeLocal Plane.quotientMap Plane.quotientMap_surjective
    (planeLocal_core_eq hF hn).symm a hK hc k he,he⟩
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
