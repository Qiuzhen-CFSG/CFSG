module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneOrbit
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Counting hyperplane contributions

The contribution of a subgroup `H ≤ P` is the dimension of `C_V(H)` less
that of `C_V(P)`. Conjugation by the actual ambient normalizer preserves
this quantity. Summing over an orbit therefore bounds its length times
its contribution by the sum over all hyperplanes. Faithfulness and `P ≠ 1`
ensure that the common fixed space is a proper subspace.

These are the counting and conjugacy steps for Aschbacher--Smith,
*The Classification of Quasithin Groups*, G.7.1(3), printed p.347.
The hyperplane decomposition and prime-degree bound are separate inputs.
-/

@[expose] public section

namespace Representation.BinaryCoprimeDegree

variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- The dimension contributed by a hyperplane after removing the common fixed space. -/
noncomputable def hyperplaneMultiplicity (rho : Representation F G V)
    (P : Subgroup G) (H : Subgroup P) : ℕ :=
  Module.finrank F (invariants (rho.comp (P.subtype.comp H.subtype))) -
    Module.finrank F (invariants (rho.comp P.subtype))

/-- The finite set of subgroups of index `p`. -/
noncomputable def hyperplanes [Finite G] (P : Subgroup G) (p : ℕ) : Finset (Subgroup P) :=
  (Set.toFinite {H : Subgroup P | H.index = p}).toFinset

@[simp] theorem mem_hyperplanes [Finite G] (P : Subgroup G) (p : ℕ) (H : Subgroup P) :
    H ∈ hyperplanes P p ↔ H.index = p :=
  Set.Finite.mem_toFinset _

/-- Total dimension of the hyperplane contributions. -/
noncomputable def hyperplaneDimensionSum [Finite G] (rho : Representation F G V)
    (P : Subgroup G) (p : ℕ) : ℕ :=
  ∑ H ∈ hyperplanes P p, hyperplaneMultiplicity rho P H

theorem invariants_le_hyperplane_invariants (rho : Representation F G V)
    (P : Subgroup G) (H : Subgroup P) :
    invariants (rho.comp P.subtype) ≤ invariants (rho.comp (P.subtype.comp H.subtype)) :=
  fun _ hv h => hv h.val

theorem hyperplaneMultiplicity_add_fixed_finrank [FiniteDimensional F V]
    (rho : Representation F G V) (P : Subgroup G) (H : Subgroup P) :
    hyperplaneMultiplicity rho P H + Module.finrank F (invariants (rho.comp P.subtype)) =
      Module.finrank F (invariants (rho.comp (P.subtype.comp H.subtype))) :=
  Nat.sub_add_cancel (Submodule.finrank_mono (invariants_le_hyperplane_invariants rho P H))

theorem hyperplane_fixed_finrank_conjugate (rho : Representation F G V)
    (P : Subgroup G) (H : Subgroup P) (g : Subgroup.normalizer (P : Set G)) :
    Module.finrank F (invariants (rho.comp (P.subtype.comp H.subtype))) =
      Module.finrank F (invariants (rho.comp
        (P.subtype.comp (H.map (P.normalizerMonoidHom g).toMonoidHom).subtype))) := by
  let K := H.map (P.normalizerMonoidHom g).toMonoidHom
  have hinv (x : V) : rho (g : G)⁻¹ (rho g x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hginv (x : V) : rho g (rho (g : G)⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hforward (v : invariants (rho.comp (P.subtype.comp H.subtype))) :
      rho g v ∈ invariants (rho.comp (P.subtype.comp K.subtype)) := by
    intro k
    obtain ⟨a, ha, hka⟩ := k.property
    have hv : rho (a : G) v = v := v.property ⟨a, ha⟩
    change rho ((k : P) : G) (rho g v) = rho g v
    rw [← hka]
    change rho ((g : G) * (a : G) * (g : G)⁻¹) (rho g v) = _
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, hinv, hv]
  have hback (v : invariants (rho.comp (P.subtype.comp K.subtype))) :
      rho (g : G)⁻¹ v ∈ invariants (rho.comp (P.subtype.comp H.subtype)) := by
    intro a
    have hmem : P.normalizerMonoidHom g (a : P) ∈ K := ⟨a, a.property, rfl⟩
    have hv : rho ((g : G) * ((a : P) : G) * (g : G)⁻¹) v = v :=
      v.property ⟨_, hmem⟩
    change rho ((a : P) : G) (rho (g : G)⁻¹ v) = rho (g : G)⁻¹ v
    have h := congrArg (fun x : V => rho (g : G)⁻¹ x) hv
    rw [map_mul, map_mul] at h
    simpa only [Module.End.mul_apply, hinv] using h
  let e : invariants (rho.comp (P.subtype.comp H.subtype)) ≃ₗ[F]
      invariants (rho.comp (P.subtype.comp K.subtype)) :=
    { toFun := fun v => ⟨rho g v, hforward v⟩
      invFun := fun v => ⟨rho (g : G)⁻¹ v, hback v⟩
      left_inv := fun v => Subtype.ext (hinv v)
      right_inv := fun v => Subtype.ext (hginv v)
      map_add' := fun v w => Subtype.ext (map_add (rho g) (v : V) (w : V))
      map_smul' := fun c v => Subtype.ext (map_smul (rho g) c (v : V)) }
  exact e.finrank_eq

theorem hyperplaneMultiplicity_eq_of_mem_orbit (rho : Representation F G V)
    (P : Subgroup G) (H K : Subgroup P) (hK : K ∈ normalizerHyperplaneOrbit P H) :
    hyperplaneMultiplicity rho P K = hyperplaneMultiplicity rho P H := by
  obtain ⟨g, rfl⟩ := hK
  unfold hyperplaneMultiplicity
  rw [hyperplane_fixed_finrank_conjugate rho P H g]

theorem orbit_mul_multiplicity_le_sum [Finite G]
    (rho : Representation F G V) (P : Subgroup G) {p : ℕ}
    (H : Subgroup P) (hH : H.index = p) :
    Nat.card (normalizerHyperplaneOrbit P H) * hyperplaneMultiplicity rho P H ≤
      hyperplaneDimensionSum rho P p := by
  classical
  let s := (Set.toFinite (normalizerHyperplaneOrbit P H)).toFinset
  have hsub : s ⊆ hyperplanes P p := by
    intro K hK
    apply (mem_hyperplanes P p K).mpr
    exact (index_eq_of_mem_normalizerHyperplaneOrbit P H K
      ((Set.Finite.mem_toFinset _).mp hK)).trans hH
  calc
    _ = ∑ K ∈ s, hyperplaneMultiplicity rho P H := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card]
      rfl
    _ = ∑ K ∈ s, hyperplaneMultiplicity rho P K := by
      apply Finset.sum_congr rfl
      intro K hK
      exact (hyperplaneMultiplicity_eq_of_mem_orbit rho P H K
        ((Set.Finite.mem_toFinset _).mp hK)).symm
    _ ≤ hyperplaneDimensionSum rho P p := Finset.sum_le_sum_of_subset hsub

theorem fixed_finrank_lt_of_faithful [FiniteDimensional F V]
    (rho : Representation F G V) (hf : Function.Injective rho)
    (P : Subgroup G) (hP : P ≠ ⊥) :
    Module.finrank F (invariants (rho.comp P.subtype)) < Module.finrank F V := by
  apply Submodule.finrank_lt
  intro he
  apply hP
  apply bot_unique
  intro g hg
  change g = 1
  apply hf
  ext v
  have hv : v ∈ invariants (rho.comp P.subtype) := he ▸ Submodule.mem_top
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, map_one,
    Module.End.one_apply] using hv ⟨g, hg⟩

end Representation.BinaryCoprimeDegree
