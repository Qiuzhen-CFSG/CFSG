module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.OmegaActions

/-!
# Cartan-invariant intersections with Suzuki roots

The source square map has fibers equal to cosets of Omega, for every Suzuki
parameter including zero. Cartan transitivity on nonidentity squares then
shows that a Cartan-invariant subgroup containing one element of order four
from a shifted root contains that entire root. Consequently a proper
intersection is contained in the root Omega.

This is the root-component separation needed on Fong--Seitz I (1973),
printed p.53. It does not assume that a nonabelian Suzuki root is central.
The CFSG PerpendicularSupport consumer applies it to the actual derived
radical, whose perpendicular-root noncontainment remains a separate step.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

/-- Equal squares detect precisely the same barred-root coordinate, including Sz(2). -/
theorem suzuki_square_eq_iff_firstCoordinate (x y : simpleRoot Q split i) :
    x^2 = y^2 ↔ suzukiFirstCoordinate Q split i m μ hB x =
      suzukiFirstCoordinate Q split i m μ hB y := by
  obtain ⟨⟨a,b⟩,rfl⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective x
  obtain ⟨⟨c,d⟩,rfl⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective y
  rw [suzukiParameter_square,suzukiParameter_square]
  simp only [suzukiFirstCoordinate_parameter]
  change _ ↔ a = c
  constructor
  · intro he
    have he' := congrArg Prod.snd ((suzukiParameter_bijective Q split i m μ hB).injective
      (a₁ := (0,a*suzukiTits m a)) (a₂ := (0,c*suzukiTits m c)) he)
    have hinj : Function.Injective (fun a : BinaryGaloisField (2*m+1) => a*suzukiTits m a) :=
      Finite.injective_iff_surjective.mpr (fun b => ⟨suzukiTits m b / b,tits_norm_inverse m b⟩)
    exact hinj he'
  · rintro rfl
    rfl

include μ hB in
/-- Square fibers on the literal simple root are its Omega cosets. -/
theorem suzuki_square_eq_iff_omega (x y : simpleRoot Q split i) :
    x^2 = y^2 ↔ (x : X ⧸ Q.D)⁻¹*y ∈ omegaOneAmbient (simpleRoot Q split i) := by
  rw [suzuki_square_eq_iff_firstCoordinate Q split i m μ hB]
  have hk := suzukiFirstCoordinate_kernel Q split i m μ hB
  change _ ↔ x⁻¹*y ∈ (omegaOneAmbient (simpleRoot Q split i)).subgroupOf (simpleRoot Q split i)
  rw [←hk,MonoidHom.mem_ker,map_mul,map_inv,inv_mul_eq_one]

include μ hB in
/-- The square-fiber identity uses the actual shifted root and right conjugation. -/
theorem suzuki_rootAt_square_eq_iff_omega (w : Weyl Q)
    (x y : X ⧸ Q.D) (hx : x ∈ rootAt Q split i w) (hy : y ∈ rootAt Q split i w) :
    x^2 = y^2 ↔ x⁻¹*y ∈ omegaOneAmbient (rootAt Q split i w) := by
  let e := MulAut.conj (representative w : X ⧸ Q.D)
  have he : (rootAt Q split i w).map e.toMonoidHom = simpleRoot Q split i :=
    map_comap_eq_self_of_surjective e.surjective _
  have hΩ : (omegaOneAmbient (rootAt Q split i w)).map e.toMonoidHom =
      omegaOneAmbient (simpleRoot Q split i) := by
    rw [map_omegaOneAmbient_injective e.toMonoidHom e.injective,he]
  have hh := suzuki_square_eq_iff_omega Q split i m μ hB ⟨e x,hx⟩ ⟨e y,hy⟩
  constructor
  · intro hs
    have hs' : (⟨e x,hx⟩ : simpleRoot Q split i)^2 = ⟨e y,hy⟩^2 :=
      Subtype.ext (by simpa only [map_pow,coe_pow] using congrArg e hs)
    have hmem := hh.mp hs'
    rw [←hΩ,mem_map_equiv] at hmem
    simpa only [←map_inv,←map_mul,MulEquiv.symm_apply_apply] using hmem
  · intro hmem
    have ht : e (x⁻¹*y) ∈ omegaOneAmbient (simpleRoot Q split i) :=
      hΩ ▸ mem_map_of_mem e.toMonoidHom hmem
    rw [map_mul,map_inv] at ht
    have hs := congrArg Subtype.val (hh.mpr ht)
    exact e.injective (by simpa only [map_pow,coe_pow] using hs)

include μ hB in
/-- One order-four root element in a Cartan-invariant subgroup forces the whole root. -/
theorem suzuki_rootAt_le_of_invariant_of_square_ne_one (w : Weyl Q)
    (D : Subgroup (X ⧸ Q.D))
    (hD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)))
    (a : X ⧸ Q.D) (ha : a ∈ rootAt Q split i w) (haD : a ∈ D) (ha2 : a^2 ≠ 1) :
    rootAt Q split i w ≤ D := by
  let A := rootAt Q split i w
  have square_omega (x : X ⧸ Q.D) (hx : x ∈ A) : x^2 ∈ omegaOneAmbient A := by
    apply (omegaOneAmbient_le_iff A _).mp le_rfl _ (A.pow_mem hx 2)
    let e : A ≃* simpleRoot Q split i :=
      RootAction.conjugateEquiv (simpleRoot Q split i) (representative w)
    have hp : (⟨x,hx⟩ : A)^4 = 1 := by
      apply e.injective
      rw [map_pow,map_one]
      obtain ⟨⟨b,c⟩,he⟩ := (suzukiParameter_bijective Q split i m μ hB).surjective (e ⟨x,hx⟩)
      rw [←he]
      exact suzukiParameter_pow_four Q split i m μ hB b c
    simpa only [coe_pow,OneMemClass.coe_one,←pow_mul] using congrArg Subtype.val hp
  have hΩ : omegaOneAmbient A ≤ D := suzuki_rootAt_omega_le_of_invariant Q split i m μ hB w D hD
    (a^2) (square_omega a ha) (D.pow_mem haD 2) ha2
  intro b hb
  by_cases hb2 : b^2 = 1
  · exact hΩ ((omegaOneAmbient_le_iff A _).mp le_rfl b hb hb2)
  · obtain ⟨h,hh⟩ := suzuki_rootAt_omega_cartan_transitive Q split i m μ hB w
      (a^2) (b^2) (square_omega a ha) (square_omega b hb) ha2 hb2
    let c := (h : X ⧸ Q.D)*a*(h : X ⧸ Q.D)⁻¹
    have hc : c ∈ A := (mem_normalizer_iff.mp (rootAt_torus_normalizes Q split i w h.property) a).mp ha
    have hcD : c ∈ D := (mem_normalizer_iff.mp (hD h.property) a).mp haD
    have hc2 : c^2 = b^2 := by
      change (MulAut.conj (h : X ⧸ Q.D) a)^2 = b^2
      rw [←map_pow]
      exact hh
    have hcb := (suzuki_rootAt_square_eq_iff_omega Q split i m μ hB w c b hc hb).mp hc2
    have he := D.mul_mem hcD (hΩ hcb)
    simpa only [mul_inv_cancel_left] using he

include μ hB in
/-- A proper Cartan-invariant root intersection has only Omega support. -/
theorem suzuki_rootAt_intersection_le_omega_of_not_le (w : Weyl Q)
    (D : Subgroup (X ⧸ Q.D))
    (hD : Q.tits.B ⊓ Q.tits.N ≤ normalizer (D : Set (X ⧸ Q.D)))
    (hnot : ¬ rootAt Q split i w ≤ D) :
    D ⊓ rootAt Q split i w ≤ omegaOneAmbient (rootAt Q split i w) := by
  intro a ha
  apply (omegaOneAmbient_le_iff _ _).mp le_rfl a ha.2
  by_contra hsq
  exact hnot (suzuki_rootAt_le_of_invariant_of_square_ne_one Q split i m μ hB w D hD a ha.2 ha.1 hsq)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
