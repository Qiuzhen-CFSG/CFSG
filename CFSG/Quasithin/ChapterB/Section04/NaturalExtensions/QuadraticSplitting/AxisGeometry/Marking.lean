module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.QuadraticSplitting.AxisGeometry
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Coherent quotient markings for the common axis in B.4.9(1)

The actual quotient of `DoubleNatural` admits natural coordinates with the
original actor marking or its inverse transpose. For the dual orientation,
a binary functional on the defining field taking 1 to 1 gives a nondegenerate
pairing on column vectors. Its equivariance identifies the binary dual with
the inverse-transpose action over the original defining field.

The common fixed space of the given four-group has defining-field codimension
one. A transposed shear carries its defining functional to a coordinate, and
rebasing the quotient by that same special-linear matrix records the required
marking equation. Thus `exists_marked_axis` supplies the actual witness
`∃ m : QuotientCoordinates d, ∃ j, E ≤ m.Q j` for the axis-generation consumer,
with no additional marking or model premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9(1),
printed pp.92–93 (PDF pp.103–104).
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterK.Linear.Natural
open Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.Marking
noncomputable section
variable (F : BinaryField) (n : ℕ)

private def fieldFunctional : F.Carrier →ₗ[ZMod 2] ZMod 2 :=
  Classical.choose (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F.Carrier) ≠ 0))

private theorem fieldFunctional_one : fieldFunctional F 1 = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one (ZMod 2) (one_ne_zero : (1 : F.Carrier) ≠ 0))

private def pairing : (Fin n → F.Carrier) →ₗ[ZMod 2] Module.Dual (ZMod 2) (Fin n → F.Carrier) where
  toFun w :=
    { toFun := fun v => fieldFunctional F (w ⬝ᵥ v)
      map_add' v u := by rw [dotProduct_add, map_add]
      map_smul' c v := by rw [dotProduct_smul, map_smul]; rfl }
  map_add' v w := by
    apply LinearMap.ext
    intro u
    change fieldFunctional F ((v + w) ⬝ᵥ u) = _
    rw [add_dotProduct, map_add]
    rfl
  map_smul' c w := by
    apply LinearMap.ext
    intro u
    change fieldFunctional F ((c • w) ⬝ᵥ u) = _
    rw [smul_dotProduct, map_smul]
    rfl

private theorem pairing_injective : Function.Injective (pairing F n) := by
  apply (pairing F n).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro w hw
  change w = 0
  funext i
  by_contra hi
  have h := LinearMap.congr_fun (show pairing F n w = 0 from hw) (Pi.single i ((w i)⁻¹))
  change fieldFunctional F (w ⬝ᵥ Pi.single i ((w i)⁻¹)) = 0 at h
  rw [dotProduct_single, mul_inv_cancel₀ hi, fieldFunctional_one] at h
  exact one_ne_zero h

/-- The binary dual, expressed as defining-field column coordinates. -/
def binaryPairingEquiv : (Fin n → F.Carrier) ≃ₗ[ZMod 2]
    Module.Dual (ZMod 2) (Fin n → F.Carrier) :=
  LinearEquiv.ofBijective (pairing F n) ⟨pairing_injective F n,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq (K := ZMod 2) (V := Fin n → F.Carrier)).symm).mp
        (pairing_injective F n)⟩

/-- The binary pairing transports the contragredient to inverse-transpose matrices. -/
theorem binaryPairingEquiv_intertwines (g : SpecialLinearGroup (Fin n) F.Carrier)
    (w : Fin n → F.Carrier) :
    binaryPairingEquiv F n (linearNatural F n (SpecialLinearGroup.inverseTranspose g) w) =
      (linearNatural F n).dual g (binaryPairingEquiv F n w) := by
  apply LinearMap.ext
  intro v
  change fieldFunctional F (((g⁻¹).val.transpose.mulVec w) ⬝ᵥ v) =
    fieldFunctional F (w ⬝ᵥ ((g⁻¹).val.mulVec v))
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec]

private def inverseTransposeEquiv : SpecialLinearGroup (Fin n) F.Carrier ≃*
    SpecialLinearGroup (Fin n) F.Carrier :=
  MulEquiv.ofBijective SpecialLinearGroup.inverseTranspose (by
    apply (Finite.injective_iff_bijective).mp
    intro g h he
    apply inv_injective
    apply Subtype.ext
    exact Matrix.transpose_injective (congrArg Subtype.val he))

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {F : BinaryField} {n : ℕ} {ρ : Representation (ZMod 2) G V}

private def dualAction (a : ActionEquiv ρ (linearNatural F n)) :
    ActionEquiv ρ.dual (linearNatural F n) where
  groupEquiv := a.groupEquiv.trans (inverseTransposeEquiv F n)
  linearEquiv := a.linearEquiv.symm.dualMap.trans (binaryPairingEquiv F n).symm
  intertwines g f := by
    apply (binaryPairingEquiv F n).injective
    change binaryPairingEquiv F n ((binaryPairingEquiv F n).symm _) =
      binaryPairingEquiv F n (linearNatural F n (SpecialLinearGroup.inverseTranspose
        (a.groupEquiv g)) ((binaryPairingEquiv F n).symm _))
    rw [LinearEquiv.apply_symm_apply, binaryPairingEquiv_intertwines,
      LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro w
    change f (ρ g⁻¹ (a.linearEquiv.symm w)) =
      f (a.linearEquiv.symm (linearNatural F n (a.groupEquiv g)⁻¹ w))
    apply congrArg f
    apply a.linearEquiv.injective
    rw [a.intertwines, a.linearEquiv.apply_symm_apply,
      a.linearEquiv.apply_symm_apply, map_inv]

/-- Quotient coordinates exist with the original actor marking or its contragredient. -/
theorem exists_coordinates (d : DoubleNatural F n ρ) : Nonempty (QuotientCoordinates d) := by
  rcases d.quotient with h | h
  · obtain ⟨e⟩ := h
    refine ⟨⟨{ groupEquiv := d.natural.groupEquiv
               linearEquiv := e.toLinearEquiv.trans d.natural.linearEquiv
               intertwines := ?_ }, 1, Or.inl ?_⟩⟩
    · intro g v
      exact (congrArg d.natural.linearEquiv (LinearMap.congr_fun (e.isIntertwining' g) v)).trans
        (d.natural.intertwines g (e v))
    · intro g
      simp
  · obtain ⟨e⟩ := h
    let a := dualAction d.natural
    refine ⟨⟨{ groupEquiv := a.groupEquiv
               linearEquiv := e.toLinearEquiv.trans a.linearEquiv
               intertwines := ?_ }, 1, Or.inr ?_⟩⟩
    · intro g v
      exact (congrArg a.linearEquiv (LinearMap.congr_fun (e.isIntertwining' g) v)).trans
        (a.intertwines g (e v))
    · intro g
      change SpecialLinearGroup.inverseTranspose (d.natural.groupEquiv g) = _
      simp only [one_mul, inv_one, mul_one]
      rfl

/-- Rebase both vector coordinates and the actor marking by the same determinant-one matrix. -/
def rebase {d : DoubleNatural F n ρ} (m : QuotientCoordinates d)
    (s : SpecialLinearGroup (Fin n) F.Carrier) : QuotientCoordinates d where
  action :=
    { groupEquiv := m.action.groupEquiv.trans (MulAut.conj s)
      linearEquiv := m.action.linearEquiv.trans
        (LinearMap.GeneralLinearGroup.toLinearEquiv ((linearNatural F n).asGroupHom s))
      intertwines g v := by
        change linearNatural F n s (m.action.linearEquiv (d.space.quotientRepresentation g v)) =
          linearNatural F n (s * m.action.groupEquiv g * s⁻¹)
            (linearNatural F n s (m.action.linearEquiv v))
        rw [m.action.intertwines]
        simp only [map_mul, Module.End.mul_apply]
        have hc : linearNatural F n s⁻¹ (linearNatural F n s (m.action.linearEquiv v)) =
            m.action.linearEquiv v := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rw [hc] }
  basisChange := s * m.basisChange
  marking := by
    rcases m.marking with h | h
    · left
      intro g
      change s * m.action.groupEquiv g * s⁻¹ = _
      rw [h g, _root_.mul_inv_rev]
      simp only [mul_assoc]
    · right
      intro g
      change s * m.action.groupEquiv g * s⁻¹ = _
      rw [h g, _root_.mul_inv_rev]
      simp only [mul_assoc]

/-- An arbitrary nonzero defining-field functional can be placed in one coordinate
by a transposed shear of determinant one. -/
theorem functional_coordinates (f : (Fin n → F.Carrier) →ₗ[F.Carrier] F.Carrier)
    (hf : f ≠ 0) : ∃ (s : SpecialLinearGroup (Fin n) F.Carrier) (j : Fin n),
      ∀ v, linearNatural F n s v j = 0 ↔ f v = 0 := by
  classical
  let a : Fin n → F.Carrier := (dotProductEquiv F.Carrier (Fin n)).symm f
  have ha (v) : a ⬝ᵥ v = f v :=
    LinearMap.congr_fun ((dotProductEquiv F.Carrier (Fin n)).apply_symm_apply f) v
  have ha0 : a ≠ 0 := by
    intro h
    apply hf
    apply LinearMap.ext
    intro v
    rw [← ha, h, zero_dotProduct]
    rfl
  obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
    by_contra! h
    exact ha0 (funext h)
  let w : coordinateHyperplane F n j :=
    ⟨(a j)⁻¹ • a - Pi.single j 1, by
      change (a j)⁻¹ * a j - (Pi.single j 1 : Fin n → F.Carrier) j = 0
      rw [inv_mul_cancel₀ hj, Pi.single_eq_same, sub_self]⟩
  refine ⟨(shear F n j w).transpose, j, ?_⟩
  intro v
  have he : linearNatural F n (shear F n j w).transpose v j = (a j)⁻¹ * f v := by
    change ((1 + vecMulVec w.val (Pi.single j 1)).transpose.mulVec v) j = _
    rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_vecMulVec,
      Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    change v j + (Pi.single j 1 : Fin n → F.Carrier) j * (w.val ⬝ᵥ v) = _
    rw [Pi.single_eq_same, one_mul]
    change v j + (((a j)⁻¹ • a - Pi.single j 1) ⬝ᵥ v) = _
    rw [sub_dotProduct, smul_dotProduct, single_dotProduct, one_mul, ha]
    change v j + ((a j)⁻¹ * f v - v j) = _
    ring
  rw [he, mul_eq_zero]
  exact or_iff_right (inv_ne_zero hj)

/-- A defining-field hyperplane is carried to the kernel of one coordinate
by an actual special-linear matrix. -/
theorem hyperplane_coordinates (H : Submodule F.Carrier (Fin n → F.Carrier))
    (hH : Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ H) = 1) :
    ∃ (s : SpecialLinearGroup (Fin n) F.Carrier) (j : Fin n),
      ∀ v, linearNatural F n s v j = 0 ↔ v ∈ H := by
  have hdim := H.finrank_quotient_add_finrank
  rw [hH] at hdim
  have htop : H < ⊤ := lt_top_iff_ne_top.mpr (by
    intro h
    rw [h, finrank_top] at hdim
    omega)
  obtain ⟨f, hf, hle⟩ := H.exists_le_ker_of_lt_top htop
  have heq : H = f.ker := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have h₁ := H.finrank_quotient_add_finrank
    have h₂ := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    omega
  obtain ⟨s, j, hs⟩ := functional_coordinates f hf
  exact ⟨s, j, fun v => (hs v).trans (by rw [heq]; rfl)⟩

/-- The common axis in the source hypothesis is also the fixed space of E itself. -/
theorem axisFour_fixedCodim (d : DoubleNatural F n ρ) {E : Subgroup G}
    (hE : IsAxisFour d E) : fixedCodim d.space.quotientRepresentation E = F.degree := by
  obtain ⟨_, hcard, I, hcod, haxes⟩ := hE
  obtain hb | ⟨e, he, hne⟩ := E.bot_or_exists_ne_one
  · rw [hb, Subgroup.card_bot] at hcard
    omega
  have hfixed : fixedSpace d.space.quotientRepresentation E = I := by
    apply le_antisymm
    · rw [← haxes e he hne]
      intro v hv
      exact (mem_fixedSpace_zpowers_iff d.space.quotientRepresentation e v).mpr (hv ⟨e, he⟩)
    · intro v hv g
      by_cases hg : (g : G) = 1
      · simp [hg]
      · exact (mem_fixedSpace_zpowers_iff d.space.quotientRepresentation (g : G) v).mp
          ((haxes g g.property hg).symm ▸ hv)
  change Module.finrank (ZMod 2) ((V ⧸ d.space.toSubmodule) ⧸
    fixedSpace d.space.quotientRepresentation E) = _
  rw [hfixed, hcod]

/-- Every source axis four-group admits coherently marked quotient coordinates
placing it in the full coordinate-axis group. The construction covers both
quotient orientations over every defining field. -/
theorem exists_marked_axis (d : DoubleNatural F n ρ) (_hfamily : SourceFamily F n)
    {E : Subgroup G} (hE : IsAxisFour d E) :
    ∃ m : QuotientCoordinates d, ∃ j : Fin n, E ≤ m.Q j := by
  obtain ⟨m⟩ := exists_coordinates d
  let A := E.map m.action.groupEquiv.toMonoidHom
  let H := fieldFixedSpace F n A
  have hcod : Module.finrank F.Carrier ((Fin n → F.Carrier) ⧸ H) = 1 := by
    have hc := fixedCodim_map_equivariant _ _ m.action.groupEquiv.toMonoidHom
      m.action.linearEquiv m.action.intertwines E
    rw [axisFour_fixedCodim d hE, fixedCodim_eq_field_codim] at hc
    exact Nat.eq_of_mul_eq_mul_left F.degree_pos (by simpa only [mul_one] using hc.symm)
  obtain ⟨s, j, hs⟩ := hyperplane_coordinates H hcod
  refine ⟨rebase m s, j, ?_⟩
  intro g hg
  refine ⟨Subgroup.mem_top _, ?_⟩
  intro v hv
  apply m.action.linearEquiv.injective
  rw [m.action.intertwines]
  have hv' : m.action.linearEquiv v ∈ H := (hs _).mp hv
  exact hv' ⟨m.action.groupEquiv g, Subgroup.mem_map.mpr ⟨g, hg, rfl⟩⟩

end
end CFSG.Quasithin.ChapterB.NaturalExtensions.QuadraticSplitting.Marking
