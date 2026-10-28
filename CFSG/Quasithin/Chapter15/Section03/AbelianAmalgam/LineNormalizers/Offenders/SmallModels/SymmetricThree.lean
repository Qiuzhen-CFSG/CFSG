module

public import Theory.Representation.FixedQuotientCoprime
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.Marked

/-!
# The marked S₃ alternative

A central quotient is identified with the actual even-weight permutation plane.
Averaging over the normal cubic shows that the commutator space is disjoint from
the central kernel; its image is the whole plane, so its dimension is two.
Every permutation fixing a nonzero plane vector squares to one. Sylow maximality
therefore identifies the pointwise stabilizer of a Sylow-fixed marker, and its
index is three. Orbit generation supplies nonvanishing of the marker's projection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of 15.3.67,
printed p.1154. No original ambient action kernel or normalizer is identified here.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
open BestReduction
namespace SymmetricThree
abbrev Actor := Equiv.Perm (Fin 3)
abbrev Space := BinaryPermutation.core (Fin 3)
abbrev natural := BinaryPermutation.coreRepresentation (Fin 3)
private instance : DecidablePred (fun v : Fin 3 → ZMod 2 => v ∈ Space) := by
  intro v
  change Decidable (∑ i, v i = 0)
  infer_instance
private instance : Fintype Space := Subtype.fintype _

def cycle : Actor := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem cycle_fixed_zero : ∀ v : Space, natural cycle v = v → v = 0 := by
  decide +kernel

private theorem displacement_surjective :
    ∀ v : Space, ∃ w : Space, natural cycle w - w = v := by
  decide +kernel

private theorem nonzero_fixer_square :
    ∀ g : Actor, ∀ v : Space, v ≠ 0 → natural g v = v → g ^ 2 = 1 := by
  decide +kernel

variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]

private theorem moved_top (ρ : Representation (ZMod 2) D W) :
    Coinvariants.ker (ρ.comp (⊤ : Subgroup D).subtype) = Coinvariants.ker ρ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ) g.val v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := ρ.comp (⊤ : Subgroup D).subtype) ⟨g, trivial⟩ v

/-- A central extension of the natural S₃ plane has moved space of dimension
two. Averaging over the normal cubic proves injectivity on that moved space. -/
theorem finrank_moved (ρ : Representation (ZMod 2) D W) (e : D ≃* Actor)
    (q : W →ₗ[ZMod 2] Space) (hs : Function.Surjective q)
    (hq : ∀ g v, q (ρ g v) = natural (e g) (q v))
    (hk : ∀ v, q v = 0 → v ∈ ρ.invariants) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 2 := by
  classical
  let : Finite D := Finite.of_equiv Actor e.symm.toEquiv
  let N := (alternatingGroup (Fin 3)).comap e.toMonoidHom
  let en : N ≃* alternatingGroup (Fin 3) :=
    { toFun := fun n => ⟨e n, n.property⟩
      invFun := fun n => ⟨e.symm n, by
        change e (e.symm n) ∈ alternatingGroup (Fin 3)
        simpa only [e.apply_symm_apply] using n.property⟩
      left_inv := by intro n; apply Subtype.ext; exact e.symm_apply_apply n
      right_inv := by intro n; apply Subtype.ext; exact e.apply_symm_apply n
      map_mul' := by intros; apply Subtype.ext; exact e.map_mul _ _ }
  have hcard : Nat.card N = 3 := by
    rw [Nat.card_congr en.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  let : Fintype N := Fintype.ofFinite N
  have hcop : (Fintype.card N : ZMod 2) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcard]
    decide
  have hinv : Representation.invariants (ρ.comp N.subtype) ≤ ρ.invariants := by
    intro v hv
    apply hk
    apply cycle_fixed_zero
    have hc : e.symm cycle ∈ N := by
      change e (e.symm cycle) ∈ alternatingGroup (Fin 3)
      rw [e.apply_symm_apply, Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have he := congrArg q (hv ⟨e.symm cycle, hc⟩)
    change q (ρ (e.symm cycle) v) = q v at he
    simpa only [hq, e.apply_symm_apply] using he
  have hd := disjoint_moved_invariants_of_normal_coprime ρ N hcop hinv (⊤ : Subgroup D)
  rw [moved_top] at hd
  let f := q.comp (Coinvariants.ker ρ).subtype
  have hfi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hd v v.property (hk v hv)
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨w, hw⟩ := displacement_surjective v
    obtain ⟨u, hu⟩ := hs w
    refine ⟨⟨ρ (e.symm cycle) u - u, Coinvariants.sub_mem_ker _ _⟩, ?_⟩
    change q (ρ (e.symm cycle) u - u) = v
    rw [map_sub, hq, e.apply_symm_apply, hu, hw]
  exact (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).finrank_eq.trans
    (by simpa using BinaryPermutation.finrank_core (Fin 3))

/-- The pointwise stabilizer of the original marked subspace. -/
def markerStabilizer (ρ : Representation (ZMod 2) D W) (U : Submodule (ZMod 2) W) :
    Subgroup D where
  carrier := {g | ∀ v ∈ U, ρ g v = v}
  one_mem' := by simp
  mul_mem' := by intro g h hg hh v hv; simp [map_mul, Module.End.mul_apply, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    have h := congrArg (ρ g⁻¹) (hg v hv)
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using h.symm

/-- A Sylow-fixed marker with a nonzero natural image has exactly that Sylow
subgroup as pointwise stabilizer, even before proving the central extension splits. -/
theorem markerStabilizer_eq_sylow
    (ρ : Representation (ZMod 2) D W) (e : D ≃* Actor)
    (q : W →ₗ[ZMod 2] Space)
    (hq : ∀ g v, q (ρ g v) = natural (e g) (q v))
    (U : Submodule (ZMod 2) W) (S : Sylow 2 D)
    (hS : U ≤ fixedSpace ρ (S : Subgroup D)) (hne : ∃ v ∈ U, q v ≠ 0) :
    markerStabilizer ρ U = (S : Subgroup D) := by
  apply S.is_maximal'
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    change (g.val : D) ^ (2 ^ 1) = 1
    apply e.injective
    rw [map_pow, map_one, pow_one]
    obtain ⟨v, hv, hqv⟩ := hne
    exact nonzero_fixer_square (e g.val) (q v) hqv
      ((hq g.val v).symm.trans (congrArg q (g.property v hv)))
  · intro g hg v hv
    exact hS hv ⟨g, hg⟩

/-- The marked stabilizer has index three in the actual actor. -/
theorem markerStabilizer_index [Finite D]
    (ρ : Representation (ZMod 2) D W) (e : D ≃* Actor)
    (q : W →ₗ[ZMod 2] Space)
    (hq : ∀ g v, q (ρ g v) = natural (e g) (q v))
    (U : Submodule (ZMod 2) W) (S : Sylow 2 D)
    (hS : U ≤ fixedSpace ρ (S : Subgroup D)) (hne : ∃ v ∈ U, q v ≠ 0) :
    (markerStabilizer ρ U).index = 3 := by
  rw [markerStabilizer_eq_sylow ρ e q hq U S hS hne]
  have hD : Nat.card D = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hcard : Nat.card S = 2 := by
    rw [S.card_eq_multiplicity, hD]
    decide +kernel
  have h := (S : Subgroup D).card_mul_index
  rw [hcard, hD] at h
  omega

/-- The source orbit-generation hypothesis supplies the required nonzero
projection; it is not added as a stronger marker hypothesis. -/
theorem marked_conclusions [Finite D]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J) (c : CentralQuotientCoordinates ρ natural) :
    Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 2 ∧
      markerStabilizer ρ d.marker = (d.sylow : Subgroup D) ∧
      (markerStabilizer ρ d.marker).index = 3 := by
  have : Nontrivial Space := Module.nontrivial_of_finrank_pos (by
    rw [BinaryPermutation.finrank_core]; decide)
  let q := c.coordinates.toLinearMap.comp ρ.invariants.mkQ
  have hq : ∀ g v, q (ρ g v) = natural (c.actor g) (q v) := c.intertwines
  have hk (v : W) (hv : q v = 0) : v ∈ ρ.invariants := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    exact c.coordinates.injective (hv.trans c.coordinates.map_zero.symm)
  have hs : Function.Surjective q := c.coordinates.surjective.comp ρ.invariants.mkQ_surjective
  have hn : ∃ v ∈ d.marker, q v ≠ 0 := d.exists_nonzero_quotient_image c
  exact ⟨finrank_moved ρ c.actor q hs hq hk,
    markerStabilizer_eq_sylow ρ c.actor q hq d.marker d.sylow d.sylow_fixes hn,
    markerStabilizer_index ρ c.actor q hq d.marker d.sylow d.sylow_fixes hn⟩

end SymmetricThree
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SmallModels
