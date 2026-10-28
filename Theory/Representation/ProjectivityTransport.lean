module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.Projective

/-!
# Projectivity under group and module isomorphisms

An equivariant linear equivalence between representations of isomorphic groups
is semilinear over the induced group-algebra isomorphism. Thus the associated
group-algebra modules are simultaneously projective. Linearity on group-algebra
basis elements is exactly the given intertwining identity; sums and scalar
multiples give the full semilinear identity.

This transports the natural A₅ module's projectivity to the actual orthogonal
L₂(4) module in Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma I.1.6(3), printed p.408 (PDF p.419).
-/

open scoped MonoidAlgebra

namespace Representation
variable {k G H V W : Type*} [CommRing k] [Group G] [Group H]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Projectivity is preserved by an intertwining pair of group and module
isomorphisms. The group-algebra isomorphism is induced by the given group map. -/
public theorem projective_of_group_module_equiv (ρ : Representation k G V) (σ : Representation k H W)
    (eG : G ≃* H) (eV : V ≃ₗ[k] W)
    (he : ∀ g v, eV (ρ g v) = σ (eG g) (eV v))
    [Module.Projective k[H] σ.asModule] : Module.Projective k[G] ρ.asModule := by
  let eA := (MonoidAlgebra.domCongr k k eG).toRingEquiv
  let := RingHomInvPair.of_ringEquiv eA
  let := RingHomInvPair.of_ringEquiv_symm eA
  let E : ρ.asModule ≃ₛₗ[(eA : k[G] →+* k[H])] σ.asModule := by
    let e := ρ.asModuleEquiv.trans (eV.trans σ.asModuleEquiv.symm)
    refine { e.toAddEquiv with map_smul' := ?_ }
    intro r v
    apply σ.asModuleEquiv.injective
    change eV (ρ.asModuleEquiv (r • v)) =
      σ.asModuleEquiv ((MonoidAlgebra.domCongr k k eG r) • e v)
    simp only [asModuleEquiv_map_smul]
    induction r using MonoidAlgebra.induction_on with
    | of g =>
        simpa only [MonoidAlgebra.of_apply, MonoidAlgebra.domCongr_single,
          asAlgebraHom_single, one_smul, e, LinearEquiv.trans_apply,
          LinearEquiv.apply_symm_apply] using he g (ρ.asModuleEquiv v)
    | add r s hr hs =>
        simp only [map_add, LinearMap.add_apply, hr, hs]
    | smul c r hr =>
        simp only [map_smul, LinearMap.smul_apply, hr]
  exact Module.Projective.of_equiv E.symm
end Representation
