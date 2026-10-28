module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.TorusRigidity
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveFlagAutomorphisms.RadicalNormalization

/-!
# Full radical normalization of a native U₅(4) involution

The same embedded plane radical supplies a flag-preserving inner correction
fixing an order-fifteen Levi torus element. The normalized actor has the
formula (x,z) ↦ (kx,k·conj(k)z) on every radical parameter. Its quotient
action is identity, its Levi displacement is central, and its original
involution cocycle remains explicit. This is not yet one unitary formula
on the whole projective carrier.

Source: Aschbacher–Smith F.4.29(2), printed p.289 of refs/quasithin.pdf.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
open Subgroup GreenBook.UnitaryFive Theory.SpecificGroups.UnitaryFive
variable (U : Model 4)

theorem rightCoordinates_inl_overlap (v : PlaneCore.Parameters U.form) :
    (rightCoordinates U (SemidirectProduct.inl v)).val ∈ U.overlap := by
  rw [rightCoordinates_val,FlagAutomorphisms.nativePlane_inl]
  exact U.flagRight_le_overlap (Subgroup.mem_sup_left
    (show PlaneCore.Parameters.toParabolic U.matrix v ∈ U.rightUnipotent from ⟨v,rfl⟩))

theorem rightCoordinateAction_inner (p : PlaneCore.PlaneSemidirect U.form)
    (hp : (rightCoordinates U p).val ∈ U.overlap) :
    rightCoordinateAction U (innerFlag U ⟨(rightCoordinates U p).val,hp⟩) = MulAut.conj p := by
  apply MulEquiv.ext
  intro q
  apply (rightCoordinates U).injective
  apply Subtype.ext
  rw [rightCoordinateAction_apply,rightLocalAction_val]
  change (rightCoordinates U p).val * (rightCoordinates U q).val *
    ((rightCoordinates U p).val)⁻¹ = (rightCoordinates U (p*q*p⁻¹)).val
  simp only [map_mul,map_inv,Subgroup.coe_mul,Subgroup.coe_inv]

/-- One genuine radical conjugation normalizes the chosen odd torus. The
full native flag is preserved because this radical fixes its plane pointwise. -/
theorem native_torus_normalize (a : flagAutomorphisms U) (ha : rightLinearAction U a = 1)
    (t : U.Fˣ) (ht : orderOf t = 15) :
    ∃ (v : PlaneCore.Parameters U.form) (b : U.overlap) (β : flagAutomorphisms U),
      b.val = (rightCoordinates U (SemidirectProduct.inl v)).val ∧
      a = innerFlag U b * β ∧ rightLinearAction U β = 1 ∧
      rightCoordinateAction U β (SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t)) =
        SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t) := by
  obtain ⟨v,hv,hfix⟩ := FlagAutomorphisms.exists_torus_normalization U.form U.conjugation
    (rightCoordinateAction U a) (rightCoordinateAction_right U a ha) t ht
  let b : U.overlap := ⟨(rightCoordinates U (SemidirectProduct.inl v)).val,rightCoordinates_inl_overlap U v⟩
  let β := (innerFlag U b)⁻¹ * a
  have hcoord : rightCoordinateAction U β =
      (MulAut.conj (SemidirectProduct.inl v : PlaneCore.PlaneSemidirect U.form))⁻¹ *
        rightCoordinateAction U a := by
    rw [map_mul,map_inv]
    rw [rightCoordinateAction_inner]
  refine ⟨v,b,β,rfl,?_,?_,?_⟩
  · exact (mul_inv_cancel_left (innerFlag U b) a).symm
  · have hb : rightLinearAction U (innerFlag U b) = 1 := by
      rw [rightLinearAction_innerFlag U _ (rightCoordinates_inl_overlap U v),rightQuotientProjection_coordinates]
      simp
    change rightLinearAction U ((innerFlag U b)⁻¹ * a) = 1
    rw [map_mul,map_inv,hb,ha,inv_one,one_mul]
  · rw [hcoord]
    exact hfix

/-- The actual native involution, after flag-compatible quotient and torus
normalization, acts by one scalar on every radical vector and its norm on
every radical matrix coordinate. The opposite endpoint and central Levi
cocycle have not been identified with a unitary representative. -/
theorem involution_plane_normalize (a : flagAutomorphisms U) (ha : a^2 = 1)
    (hc : rightCoefficient U a = U.form.conj) :
    ∃ (b : U.overlap) (γ : flagAutomorphisms U) (k : U.F) (t : U.Fˣ),
      b.val ∈ U.rightLocalImage ∧ k ≠ 0 ∧ orderOf t = 15 ∧
      a = innerFlag U b * γ * graphFlag U ∧ rightLinearAction U γ = 1 ∧
      rightCoordinateAction U γ (SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t)) =
        SemidirectProduct.inr (PlaneCore.ResidualAction.diagonalActor t) ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).x = k • u.x) ∧
      (∀ u : PlaneCore.Parameters U.form, (rightRadicalAction U γ u).z = (k * U.form.conj k) • u.z) ∧
      (∀ A : Matrix.SpecialLinearGroup (Fin 2) U.F,
        (FlagAutomorphisms.leviDeviation U.form (rightCoordinateAction U γ) A).x = 0) ∧
      (γ * graphFlag U) * innerFlag U b * (γ * graphFlag U) = (innerFlag U b)⁻¹ := by
  obtain ⟨b₀,β,hb₀,he,hq,_⟩ := rightLinearAction_normalize_involution U a ha
  obtain ⟨δ,hδ,hδq⟩ := normalize_graph U β (hc ▸ hq)
  obtain ⟨t,ht⟩ := PlaneCore.ResidualAction.exists_order_fifteen U.local_field_card
  obtain ⟨v,b₁,γ,hb₁,hγ,hγq,hfix⟩ := native_torus_normalize U δ hδq t ht
  obtain ⟨k,hk,hx,hz⟩ := FlagAutomorphisms.radicalAction_full_scalar U.form U.conjugation
    U.rightLeviTrace U.rightLeviTrace_spec (rightCoordinateAction U γ)
    (rightCoordinateAction_right U γ hγq) t ht hfix
  have hrepr : a = innerFlag U (b₀*b₁) * γ * graphFlag U := by
    rw [he,hδ,hγ,map_mul]
    simp only [mul_assoc]
  refine ⟨b₀*b₁,γ,k,t,?_,hk,ht,hrepr,hγq,hfix,hx,hz,?_,?_⟩
  · exact U.rightLocalImage.mul_mem hb₀ (hb₁ ▸ (rightCoordinates U (SemidirectProduct.inl v)).property)
  · exact FlagAutomorphisms.leviDeviation_center U.form U.rightLeviTrace U.rightLeviTrace_spec
      (rightCoordinateAction U γ) (rightCoordinateAction_right U γ hγq) k hx hz
  · apply eq_inv_of_mul_eq_one_right
    simpa only [hrepr,pow_two,mul_assoc] using ha
end CFSG.Quasithin.ChapterF.UnitaryFiveFlagAutomorphisms
