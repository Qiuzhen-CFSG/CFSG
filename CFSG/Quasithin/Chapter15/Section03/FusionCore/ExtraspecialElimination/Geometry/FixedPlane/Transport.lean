module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane.Model
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.LocalAlgebra
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Action

/-!
# The actual fixed plane and local two-core

The coordinate predicate identifies C_V(N_T(V₁)) with the fixed space of
the base part of the Sylow actor. Normality of O₂(H) in H puts its image
normally in the image of T. If it acts nontrivially on V, the dihedral
calculation supplies the central involution, and its displacement equation
transports back to Z_S ≤ [V,O₂(H)] in the ambient group.

The coordinate natural action and FusionCore's quadratic natural action are
kept distinct. Pulling the latter's form through the coordinate equivalence
gives an invariant quadratic function. Nondegeneracy makes it nonzero, so the
finite orbit calculation proves that the actual fixed plane is not totally
singular for that very form. No equality of independently chosen forms is
required. Normality throughout is relative to H or T.

The elementary coordinate-predicate transport follows the private argument
in CosetSetup.ExtraspecialLocal.NormalizerAction; its public WreathModel
calculation and the existing OrthogonalLocal.Action APIs are reused here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the orthogonal
setup on printed pp.1121–1122, 15.3.48–49 on pp.1141–1142, and (m), p.1144.
-/

@[expose] public section

open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane
open CosetSetup.ExtraspecialLocal.NormalizerAction.WreathModel
attribute [local instance] orthogonalAction
private instance : SMul OrthogonalActor OrthogonalVector := orthogonalAction.toMulAction.toSMul
private instance : MulAction OrthogonalActor OrthogonalVector := orthogonalAction.toMulAction
variable {G : Type*} [Group G] {M V : Subgroup G}


private theorem normalizer_iff_coordinatePredicate
    (d : Section03.NaturalOrthogonalAction M V) (H : Subgroup G) (hHV : H ≤ V)
    (F : OrthogonalVector → Prop)
    (hF : ∀ v : V, (v : G) ∈ H ↔ F (d.coordinates v)) (m : M) :
    (m : G) ∈ normalizer (H : Set G) ↔
      ∀ w, F w ↔ F (d.actor m • w) := by
  constructor
  · intro hn w
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    rw [← d.compatible]
    exact (hF v).symm.trans ((Subgroup.mem_normalizer_iff.mp hn v).trans
      (hF (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ v)))
  · intro hn
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    have hV : x ∈ V ↔ (m : G) * x * (m : G)⁻¹ ∈ V :=
      Subgroup.mem_normalizer_iff.mp (d.normalizes m.property) x
    constructor
    · intro hx
      have ht := (hn (d.coordinates ⟨x, hHV hx⟩)).mp ((hF _).mp hx)
      rw [← d.compatible] at ht
      exact (hF _).mpr ht
    · intro hx
      let v : V := ⟨x, hV.mpr (hHV hx)⟩
      apply (hF v).mpr
      apply (hn (d.coordinates v)).mpr
      rw [← d.compatible]
      exact (hF _).mp hx

private theorem mem_plane_coordinates (d : Section03.NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ d.plane i ↔ ∀ j, j ≠ i → d.coordinates v j = 1 := by
  constructor
  · rintro ⟨u, hu, he⟩
    have he' : u = v := Subtype.ext he
    subst u
    exact hu
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem normalizes_plane_iff (d : Section03.NaturalOrthogonalAction M V)
    (i : OrthogonalPlaneIndex) (m : M) :
    (m : G) ∈ normalizer (d.plane i : Set G) ↔ (d.actor m).right = 1 := by
  exact (normalizer_iff_coordinatePredicate d (d.plane i) (d.plane_le i)
    (fun v => ∀ j, j ≠ i → v j = 1) (mem_plane_coordinates d i) m).trans
    (plane_iff_shift (d.actor m) i)

private theorem compatible_fix_iff (d : Section03.NaturalOrthogonalAction M V) (m : M) (v : V) :
    d.actor m • d.coordinates v = d.coordinates v ↔
      (m : G) * (v : G) = (v : G) * (m : G) := by
  rw [← d.compatible]
  constructor
  · intro h
    have he := congrArg Subtype.val (d.coordinates.injective h)
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro h
    apply congrArg d.coordinates
    exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr h)

/-- The fixed plane uses the actual stabilizer N_T(V₁), not an arbitrary
four-subgroup of the Sylow actor. -/
theorem mem_fixedPlane_coordinates (d : Section03.NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (i : OrthogonalPlaneIndex) (v : V) :
    (v : G) ∈ fixedPlane V (planeStabilizer T (d.plane i)) ↔
      baseFixed (d.image (T : Subgroup G)) (d.coordinates v) := by
  constructor
  · intro hv a ha hr
    obtain ⟨m, hm, rfl⟩ := ha
    apply (compatible_fix_iff d m v).mpr
    exact hv.2 m ⟨hm, (normalizes_plane_iff d i m).mpr hr⟩
  · intro hv
    refine ⟨v.property, ?_⟩
    intro s hs
    let m : M := ⟨s, hTM hs.1⟩
    apply (compatible_fix_iff d m v).mp
    exact hv (d.actor m) ⟨m, hs.1, rfl⟩ ((normalizes_plane_iff d i m).mp hs.2)

private theorem image_normalized (d : Section03.NaturalOrthogonalAction M V) (T Q : Subgroup G)
    (hn : T ≤ normalizer (Q : Set G)) :
    d.image T ≤ normalizer (d.image Q : Set OrthogonalActor) := by
  apply le_normalizer_iff.mpr
  rintro _ ⟨t, ht, rfl⟩ _ ⟨q, hq, rfl⟩
  refine ⟨t*q*t⁻¹, ?_, by simp⟩
  exact le_normalizer_iff.mp hn t ht q hq

private theorem core_le_sylow [Finite G] (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : localTwoCore H ≤ (T : Subgroup G) := by
  rintro _ ⟨q, hq, rfl⟩
  exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) hq

private theorem core_normalized (H : Subgroup G) :
    H ≤ normalizer (localTwoCore H : Set G) := by
  simpa only [localTwoCore, normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] using
    (pCore 2 H).le_normalizer_map H.subtype

/-- Local normality and the normalization of V give both core bounds used
in the fixed-plane calculation. No ambient normality of Q_H is required. -/
theorem core_control [Finite G]
    (d : Section03.NaturalOrthogonalAction M V) (T : Sylow 2 G) (H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H) :
    H ≤ normalizer (localTwoCore H : Set G) ∧
      localTwoCore H ≤ (T : Subgroup G) ∧ ⁅V, localTwoCore H⁆ ≤ V := by
  have hQT := core_le_sylow T H hTH
  exact ⟨core_normalized H, hQT,
    le_normalizer_iff_commutator_le_left.mp ((hQT.trans hTM).trans d.normalizes)⟩

/-- The nontrivial Q_H image is normal in the actual dihedral Sylow actor,
so it contains the central involution. Its displacement image contains Z_S. -/
theorem core_image_central_involution [Finite G]
    (d : Section03.NaturalOrthogonalAction M V) (T : Sylow 2 G) (H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hnon : ⁅V, localTwoCore H⁆ ≠ ⊥) :
    ∃ z ∈ d.image (localTwoCore H), z ≠ 1 ∧ z ^ 2 = 1 ∧
      (∀ p ∈ d.image (T : Subgroup G), p*z = z*p) ∧
      ∀ v, baseFixed (d.image (T : Subgroup G)) v →
        ∃ u : OrthogonalVector, v = (z • u)*u⁻¹ := by
  let P := (T.subtype hTM).mapSurjective d.onto
  have hQT := core_le_sylow T H hTH
  have hQ : d.image (localTwoCore H) ≠ ⊥ := by
    intro hb
    have hc := (d.image_eq_bot_iff (hQT.trans hTM)).mp hb
    apply hnon
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  exact Model.sylow_fixed_commutator P (d.image (localTwoCore H))
    (map_mono (fun _ h => hQT h)) hQ (image_normalized d _ _ (hTH.trans (core_normalized H)))

/-- The central involution calculation gives Z_S ≤ [V,Q_H] in G itself. -/
theorem fixedPlane_le_commutator [Finite G]
    (d : Section03.NaturalOrthogonalAction M V) (T : Sylow 2 G) (H : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (i : OrthogonalPlaneIndex) (hnon : ⁅V, localTwoCore H⁆ ≠ ⊥) :
    fixedPlane V (planeStabilizer T (d.plane i)) ≤ ⁅V, localTwoCore H⁆ := by
  obtain ⟨z, hz, _, _, _, hdispl⟩ := core_image_central_involution d T H hTM hTH hnon
  obtain ⟨m, hm, rfl⟩ := hz
  intro v hv
  let v₀ : V := ⟨v, hv.1⟩
  have hfix := (mem_fixedPlane_coordinates d T hTM i v₀).mp hv
  obtain ⟨w, hw⟩ := hdispl (d.coordinates v₀) hfix
  let u : V := d.coordinates.symm w
  let u' : V := V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ u
  have he : v₀ = u' * u⁻¹ := by
    apply d.coordinates.injective
    rw [map_mul, map_inv]
    change d.coordinates v₀ = d.coordinates
      (V.normalizerMonoidHom ⟨m, d.normalizes m.property⟩ u) * (d.coordinates u)⁻¹
    rw [d.compatible, show d.coordinates u = w from d.coordinates.apply_symm_apply w]
    exact hw
  have he' := congrArg (fun x : V => (x : G)) he
  change v = (m : G) * (u : G) * (m : G)⁻¹ * (u : G)⁻¹ at he'
  rw [he', commutator_comm]
  exact commutator_mem_commutator hm u.property

/-- Compatibility with any nondegenerate invariant form on the actual V.
The two natural-action structures need not identify their chosen coordinates:
the quadratic identity and the full coordinate actor force nonsingularity. -/
theorem fixedPlane_not_totallySingular [Finite G] [IsElementaryAbelian 2 V]
    (d : Section03.NaturalOrthogonalAction M V) (o : FusionCore.NaturalOrthogonalAction M V)
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (i : OrthogonalPlaneIndex) :
    ¬ IsTotallySingular o.form (fixedPlane V (planeStabilizer T (d.plane i))) := by
  let P := (T.subtype hTM).mapSurjective d.onto
  let q : OrthogonalVector → ZMod 2 := fun w => o.form (Additive.ofMul (d.coordinates.symm w))
  have h1 : q 1 = 0 := by simp [q]
  have hi : ∀ a : OrthogonalActor, ∀ w, q (a • w) = q w := by
    intro a w
    obtain ⟨m, rfl⟩ := d.onto a
    obtain ⟨v, rfl⟩ := d.coordinates.surjective w
    dsimp [q]
    rw [← d.compatible, d.coordinates.symm_apply_apply, d.coordinates.symm_apply_apply]
    exact o.preserves m v
  have hq : ∀ x y z, q (x*y*z) + (q x + q y + q z) =
      q (x*y) + q (y*z) + q (z*x) := by
    intro x y z
    simpa only [q, map_mul, ofMul_mul] using
      o.form.map_add_add_add_map (Additive.ofMul (d.coordinates.symm x))
        (Additive.ofMul (d.coordinates.symm y)) (Additive.ofMul (d.coordinates.symm z))
  have hn : ¬ ∀ v, q v = 0 := by
    intro hz
    let : Nontrivial (Additive V) := Module.nontrivial_of_finrank_eq_succ o.dimension
    have hzero (v : Additive V) : o.form v = 0 := by
      simpa only [q, d.coordinates.symm_apply_apply, ofMul_toMul] using hz (d.coordinates v.toMul)
    obtain ⟨v, hv⟩ := exists_ne (0 : Additive V)
    apply hv
    apply o.nondegenerate.1 v
    intro w
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, hzero, sub_zero]
  obtain ⟨w, hw, hwq⟩ := Model.sylow_fixed_nonsingular P q h1 hi hq hn
  intro hs
  apply hwq
  apply hs.2 (d.coordinates.symm w)
  apply (mem_fixedPlane_coordinates d T hTM i _).mpr
  simpa only [d.coordinates.apply_symm_apply, P, Sylow.coe_mapSurjective,
    Sylow.coe_subtype, Section03.NaturalOrthogonalAction.image] using hw

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.FixedPlane
