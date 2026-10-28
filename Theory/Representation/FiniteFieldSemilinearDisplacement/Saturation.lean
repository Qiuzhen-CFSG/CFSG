module
public import Theory.Representation.SL2NaturalOffenders.FieldAction.Basic
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Equality in the half-space bound for semilinear actors

If a faithful elementary binary actor moves the coefficient field while fixing
at least half the whole binary space, two scalar translates of its common fixed
space fill the module. Its coefficient action is therefore injective. Finite-field
automorphisms are cyclic, so the actor has rank at most one.

The Schur-normalizer application excludes equality in the Hermitian square's
full-actor budget, retaining the original group rather than one factor image.
Source: Aschbacher--Smith D.3.7, pp.198--199, and the scalar displacement
argument of Guralnick--Malle, Classification of 2F-modules II, Section 3.5.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.FiniteFieldSemilinearDisplacement
variable {F G V : Type*} [Field F] [Finite F] [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module F V]
  [FiniteDimensional (ZMod 2) V] [Algebra (ZMod 2) F]

omit [Finite F] [Algebra (ZMod 2) F] in
/-- The common fixed space and a moved scalar translate detect every actor. -/
theorem coefficient_injective_of_half_fixed
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (τ : G →* (F ≃+* F))
    (hsemi : ∀ g c v, ρ g (c • v) = τ g c • ρ g v)
    (A : Subgroup G) {a : G} (ha : a ∈ A) (hne : τ a ≠ 1)
    (hd : 2 * fixedCodim ρ A ≤ Module.finrank (ZMod 2) V) :
    Function.Injective (τ.comp A.subtype) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨c,hc⟩ : ∃ c : F, τ a c ≠ c := by
    by_contra! h
    exact hne (RingEquiv.ext h)
  let W := fixedSpace ρ A
  let f : W × W → V := fun p => p.1.val+c•p.2.val
  have hi : Function.Injective f := by
    rintro ⟨w,z⟩ ⟨w',z'⟩ he
    change w.val+c•z.val=w'.val+c•z'.val at he
    have hh : c•(z.val-z'.val)=w'.val-w.val := by
      rw [smul_sub]
      exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using he)
    have hh' := congrArg (ρ a) hh
    have hfixed (u : W) : ρ a u.val = u.val := u.property ⟨a,ha⟩
    rw [hsemi,map_sub,map_sub,hfixed,hfixed,hfixed,hfixed,←hh] at hh'
    have hz : (τ a c-c) • (z.val-z'.val)=0 := by rw [sub_smul,hh',sub_self]
    have hez : z=z' := Subtype.ext (sub_eq_zero.mp
      ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hc)))
    have hew : w=w' := by
      rw [hez] at he
      exact Subtype.ext (add_right_cancel he)
    exact Prod.ext hew hez
  have hcard : Nat.card V ≤ Nat.card (W × W) := by
    rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W),Nat.card_zmod,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have hh := fixedCodim_add_finrank ρ A
    change Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) W + Module.finrank (ZMod 2) W
    change fixedCodim ρ A + Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) V at hh
    omega
  have hs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨hi,(Nat.card_le_card_of_injective f hi).antisymm hcard⟩).2
  intro x y hxy
  apply Subtype.ext
  apply hf
  apply LinearMap.ext
  intro v
  obtain ⟨⟨w,z⟩,rfl⟩ := hs v
  change ρ x.val (w.val+c•z.val) = ρ y.val (w.val+c•z.val)
  have hfixed (u : W) (g : A) : ρ g.val u.val = u.val := u.property g
  change τ x.val = τ y.val at hxy
  rw [map_add,map_add,hsemi,hsemi,hfixed w x,hfixed w y,hfixed z x,hfixed z y,hxy]

/-- A faithful elementary actor attaining the half-space bound has rank at most one. -/
theorem rank_le_one_of_half_fixed
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (τ : G →* (F ≃+* F))
    (hsemi : ∀ g c v, ρ g (c • v) = τ g c • ρ g v)
    (A : Subgroup G) [Finite A] [IsElementaryAbelian 2 A]
    {a : G} (ha : a ∈ A) (hne : τ a ≠ 1)
    (hd : 2 * fixedCodim ρ A ≤ Module.finrank (ZMod 2) V) : rank A ≤ 1 := by
  have hfi := coefficient_injective_of_half_fixed ρ hf τ hsemi A ha hne hd
  have hc := SL2NaturalOffenders.fieldAction_range_card_le_two A inferInstance (τ.comp A.subtype)
  rw [←Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv] at hc
  exact (Nat.log_mono_right (b := 2) hc).trans_eq (by decide)
end Representation.FiniteFieldSemilinearDisplacement
