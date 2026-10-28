module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Geometry under equivariant linear and group equivalences

Let f intertwine ρ with σ along a group equivalence e. The image under f
transports displacement ranges, fixed spaces, setwise stabilizers and vector
orbits. Restriction and quotient give genuine representation equivalences on
invariant sections. The lower space is mapped inside the upper image, and the
quotient equivalences send the class of v to the class of f(v).

These are standard functorial consequences of equivariance and bijectivity.
Their concrete application is the square/cube duality used in
Aschbacher--Smith §12.5; `LocalGeometry/Duality.lean` instantiates the maps and
subgroup markings with the actual binary exterior representations.
-/

@[expose] public section

namespace Representation.EquivariantGeometry
variable {k G H V W : Type*} [Field k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k H W)
  (e : G ≃* H) (f : V ≃ₗ[k] W)
  (hf : ∀ g v, f (ρ g v) = σ (e g) (f v))

include hf

theorem displacement_apply (g : G) (v : V) :
    f ((ρ g - (LinearMap.id : V →ₗ[k] V)) v) = (σ (e g) - (LinearMap.id : W →ₗ[k] W)) (f v) := by
  simpa only [LinearMap.sub_apply, LinearMap.id_apply, map_sub] using
    congrArg (fun w => w - f v) (hf g v)

theorem map_displacement_range (g : G) :
    (LinearMap.range (ρ g - LinearMap.id)).map f.toLinearMap =
      LinearMap.range (σ (e g) - LinearMap.id) := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, rfl⟩, rfl⟩
    exact ⟨f u, (displacement_apply ρ σ e f hf g u).symm⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := f.surjective w
    exact ⟨_, ⟨v, rfl⟩, displacement_apply ρ σ e f hf g v⟩

theorem displacement_rank (g : G) :
    Module.finrank k (LinearMap.range (ρ g - LinearMap.id)) =
      Module.finrank k (LinearMap.range (σ (e g) - LinearMap.id)) :=
  (f.ofSubmodules _ _ (map_displacement_range ρ σ e f hf g)).finrank_eq

theorem fixed_iff (g : G) (v : V) : ρ g v = v ↔ σ (e g) (f v) = f v := by
  rw [← hf, f.injective.eq_iff]

theorem map_fixed_kernel (g : G) :
    (LinearMap.ker (ρ g - LinearMap.id)).map f.toLinearMap =
      LinearMap.ker (σ (e g) - LinearMap.id) := by
  ext w
  obtain ⟨v, rfl⟩ := f.surjective w
  simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  exact fixed_iff ρ σ e f hf g v

theorem fixed_rank (g : G) :
    Module.finrank k (LinearMap.ker (ρ g - LinearMap.id)) =
      Module.finrank k (LinearMap.ker (σ (e g) - LinearMap.id)) :=
  (f.ofSubmodules _ _ (map_fixed_kernel ρ σ e f hf g)).finrank_eq

theorem map_subgroup_fixed (A : Subgroup G) :
    (Representation.invariants (ρ.comp A.subtype)).map f.toLinearMap =
      Representation.invariants (σ.comp (A.map e.toMonoidHom).subtype) := by
  ext w
  obtain ⟨v, rfl⟩ := f.surjective w
  simp only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, mem_invariants,
    MonoidHom.comp_apply]
  constructor
  · intro hv a
    obtain ⟨g, hg, hga⟩ := a.property
    change e g = (a : H) at hga
    change σ (a : H) (f v) = f v
    rw [← hga]
    exact (fixed_iff ρ σ e f hf g v).mp (hv ⟨g, hg⟩)
  · intro hv g
    exact (fixed_iff ρ σ e f hf g v).mpr
      (hv ⟨e g, Subgroup.mem_map.mpr ⟨g, g.property, rfl⟩⟩)

omit hf in
/-- Setwise stabilizer, with the representation and the subspace explicit. -/
def setwiseStabilizer (U : Submodule k V) : Subgroup G where
  carrier := {g | ∀ v, ρ g v ∈ U ↔ v ∈ U}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    simpa only [map_mul, Module.End.mul_apply] using (hg (ρ h v)).trans (hh v)
  inv_mem' := by
    intro g hg v
    have hi : ρ g (ρ g⁻¹ v) = v := by
      change (ρ g * ρ g⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    exact (hg (ρ g⁻¹ v)).symm.trans (by rw [hi])

theorem stabilizer_iff (U : Submodule k V) (g : G) :
    g ∈ setwiseStabilizer ρ U ↔ e g ∈ setwiseStabilizer σ (U.map f.toLinearMap) := by
  change (∀ v, ρ g v ∈ U ↔ v ∈ U) ↔
    ∀ w, σ (e g) w ∈ U.map f.toLinearMap ↔ w ∈ U.map f.toLinearMap
  constructor
  · intro hg w
    obtain ⟨v, rfl⟩ := f.surjective w
    rw [← hf]
    simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hg v
  · intro hg v
    have h := hg (f v)
    rw [← hf] at h
    simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using h

theorem map_stabilizer (U : Submodule k V) :
    (setwiseStabilizer ρ U).map e.toMonoidHom =
      setwiseStabilizer σ (U.map f.toLinearMap) := by
  ext h
  obtain ⟨g, rfl⟩ := e.surjective h
  constructor
  · rintro ⟨g', hg', he⟩
    have : g' = g := e.injective he
    subst g'
    exact (stabilizer_iff ρ σ e f hf U g).mp hg'
  · intro hg
    exact ⟨g, (stabilizer_iff ρ σ e f hf U g).mpr hg, rfl⟩

theorem orbit_iff (v w : V) :
    (∃ g, ρ g v = w) ↔ ∃ h, σ h (f v) = f w := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨e g, (hf g v).symm.trans (congrArg f hg)⟩
  · rintro ⟨h, hh⟩
    obtain ⟨g, rfl⟩ := e.surjective h
    exact ⟨g, f.injective ((hf g v).trans hh)⟩

theorem image_orbit (v : V) :
    f '' Set.range (fun g => ρ g v) = Set.range (fun h => σ h (f v)) := by
  ext w
  obtain ⟨u, rfl⟩ := f.surjective w
  simpa only [Set.mem_image, Set.mem_range, f.injective.eq_iff, exists_eq_right] using
    orbit_iff ρ σ e f hf v u

/-- An actual bijection of vector orbits, with the ambient map prescribed. -/
noncomputable def orbitEquiv (v : V) :
    Set.range (fun g => ρ g v) ≃ Set.range (fun h => σ h (f v)) where
  toFun u := ⟨f u, (orbit_iff ρ σ e f hf v u).mp u.property⟩
  invFun w := ⟨f.symm w, (orbit_iff ρ σ e f hf v (f.symm w)).mpr
    (by simpa only [Set.mem_range, LinearEquiv.apply_symm_apply] using w.property)⟩
  left_inv u := Subtype.ext (f.symm_apply_apply u)
  right_inv w := Subtype.ext (f.apply_symm_apply w)

theorem orbit_card (v : V) :
    Nat.card (Set.range (fun g => ρ g v)) = Nat.card (Set.range (fun h => σ h (f v))) :=
  Nat.card_congr (orbitEquiv ρ σ e f hf v)

theorem map_invariant (U : Submodule k V) (hU : ∀ g, U ≤ U.comap (ρ g)) :
    ∀ h, U.map f.toLinearMap ≤ (U.map f.toLinearMap).comap (σ h) := by
  intro h w hw
  obtain ⟨g, rfl⟩ := e.surjective h
  obtain ⟨v, hv, rfl⟩ := hw
  exact ⟨ρ g v, hU g hv, hf g v⟩

/-- Restrict simultaneously to a subgroup and its actual image under the group equivalence. -/
noncomputable def restrictionEquiv (A : Subgroup G) :
    Representation.Equiv (ρ.comp A.subtype)
      ((σ.comp (A.map e.toMonoidHom).subtype).comp (e.subgroupMap A).toMonoidHom) :=
  Representation.Equiv.mk f (fun g => LinearMap.ext (hf g))

noncomputable def subrepresentationEquiv (U : Submodule k V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) :
    (ρ.subrepresentation U hU).Equiv
      ((σ.subrepresentation (U.map f.toLinearMap) (map_invariant ρ σ e f hf U hU)).comp
        e.toMonoidHom) :=
  Representation.Equiv.mk (f.submoduleMap U) (fun g => by
    ext v
    exact hf g v)

noncomputable def quotientEquiv (U : Submodule k V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) :
    (ρ.quotient U hU).Equiv
      ((σ.quotient (U.map f.toLinearMap) (map_invariant ρ σ e f hf U hU)).comp
        e.toMonoidHom) :=
  Representation.Equiv.mk (Submodule.Quotient.equiv U (U.map f.toLinearMap) f rfl)
    (fun g => by
      apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ v =>
        change Submodule.Quotient.mk (f (ρ g v)) =
          (Submodule.Quotient.mk (σ (e g) (f v)) : W ⧸ U.map f.toLinearMap)
        rw [hf])

theorem quotientEquiv_mk (U : Submodule k V) (hU : ∀ g, U ≤ U.comap (ρ g)) (v : V) :
    quotientEquiv ρ σ e f hf U hU (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk (f v) : W ⧸ U.map f.toLinearMap) := rfl

omit hf in
/-- A lower subspace in a section maps to the literal image inside the upper image. -/
theorem lower_subspace_image (U L : Submodule k V) :
    (L.comap U.subtype).map (f.submoduleMap U).toLinearMap =
      (L.map f.toLinearMap).comap (U.map f.toLinearMap).subtype := by
  ext w
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, hvw⟩
    change f v = (w : W) at hvw
    have hvU : v ∈ U := by
      have hw := w.property
      rw [← hvw] at hw
      simpa only [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply] using hw
    exact ⟨⟨v, hvU⟩, hv, Subtype.ext hvw⟩

/-- Apply restriction and then quotient transport to a literal invariant section. -/
noncomputable def subquotientEquiv (U : Submodule k V)
    (hU : ∀ g, U ≤ U.comap (ρ g)) (B : Submodule k U)
    (hB : ∀ g, B ≤ B.comap (ρ.subrepresentation U hU g)) :=
  quotientEquiv (ρ.subrepresentation U hU)
    (σ.subrepresentation (U.map f.toLinearMap) (map_invariant ρ σ e f hf U hU))
    e (f.submoduleMap U) (fun g v => Subtype.ext (hf g v)) B hB

theorem subquotientEquiv_mk (U : Submodule k V) (hU : ∀ g, U ≤ U.comap (ρ g))
    (B : Submodule k U) (hB : ∀ g, B ≤ B.comap (ρ.subrepresentation U hU g)) (v : U) :
    subquotientEquiv ρ σ e f hf U hU B hB (Submodule.Quotient.mk v) =
      (Submodule.Quotient.mk (f.submoduleMap U v) :
        U.map f.toLinearMap ⧸ B.map (f.submoduleMap U).toLinearMap) := rfl

end Representation.EquivariantGeometry
