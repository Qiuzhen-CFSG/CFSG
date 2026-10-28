module

public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# Generated cores of binary representations

The generated core is the sum of the fixed spaces of actor subgroups of
corank at most `k`. Surjective changes of actors preserve this sum: images
can only decrease corank, and inverse images preserve it exactly. This
includes passage to the faithful action image.

If the displacement of a vector lies in a subspace of dimension at most
`k`, its orbit has at most `2^k` elements. Its stabilizer is consequently one
of the subgroups defining the core. This supplies the parabolic-radical
argument in H.9.2(5) and H.9.3(4).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Definition
E.3.30, printed p.237, and H.9, printed pp.390–392. The equality with the
group-theoretic E.3.30 definition is proved in the Chapter H adapter.
-/

@[expose] public section

namespace BinaryNaturalDual
open Representation.BinaryOffender
variable {G D V W : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- The actual span of centralizers, with corank computed in the actor group. -/
noncomputable def generatedCore (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    Submodule (ZMod 2) V :=
  ⨆ (X : Subgroup G) (_ : Nat.log 2 X.index ≤ k), fixedSpace ρ X

theorem fixedSpace_le_generatedCore (ρ : Representation (ZMod 2) G V)
    {k : ℕ} {X : Subgroup G} (hX : Nat.log 2 X.index ≤ k) :
    fixedSpace ρ X ≤ generatedCore ρ k :=
  le_iSup_of_le X (le_iSup_of_le hX le_rfl)

theorem generatedCore_le (ρ : Representation (ZMod 2) G V)
    {k : ℕ} {U : Submodule (ZMod 2) V}
    (h : ∀ X : Subgroup G, Nat.log 2 X.index ≤ k → fixedSpace ρ X ≤ U) :
    generatedCore ρ k ≤ U := iSup_le fun X => iSup_le (h X)

/-- Quotients of finite actor groups and simultaneous equivariant changes of
module coordinates preserve the whole generated core. -/
theorem generatedCore_map_surjective [Finite G]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) D W)
    (f : G →* D) (hf : Function.Surjective f) (E : V ≃ₗ[ZMod 2] W)
    (hE : ∀ g v, E (ρ g v) = σ (f g) (E v)) (k : ℕ) :
    (generatedCore ρ k).map E.toLinearMap = generatedCore σ k := by
  simp only [generatedCore, Submodule.map_iSup,
    fixedSpace_map_equivariant ρ σ f E hE]
  apply le_antisymm
  · refine iSup_le fun X => iSup_le fun hX => ?_
    apply le_iSup_of_le (X.map f)
    apply le_iSup_of_le (le_trans (Nat.log_mono_right
      (Nat.le_of_dvd (Nat.pos_of_ne_zero X.index_ne_zero_of_finite)
        (X.index_map_dvd hf))) hX)
    exact le_rfl
  · refine iSup_le fun X => iSup_le fun hX => ?_
    apply le_iSup_of_le (X.comap f)
    apply le_iSup_of_le (show Nat.log 2 (X.comap f).index ≤ k by
      simpa only [Subgroup.index_comap_of_surjective X hf] using hX)
    rw [Subgroup.map_comap_eq_self_of_surjective hf]

/-- Reinterpret a linear action as an action on the multiplicative type tag
of its additive group; no quotient of the vector space is taken. -/
def multiplicativeAction (ρ : Representation (ZMod 2) G V) :
    G →* MulAut (Multiplicative V) where
  toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv
    (ρ.asGroupHom g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext v
    exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun ρ.map_one v.toAdd)
  map_mul' g h := by
    ext v
    exact congrArg Multiplicative.ofAdd (LinearMap.congr_fun (ρ.map_mul g h) v.toAdd)

/-- Every additive subgroup of a binary space is a binary subspace. -/
def subgroupOrderIso : Submodule (ZMod 2) V ≃o Subgroup (Multiplicative V) :=
  (AddSubgroup.toZModSubmodule 2).symm.trans AddSubgroup.toSubgroup

/-- A small displacement space bounds the orbit, so the vector's own
stabilizer contributes it to the generated core. -/
theorem mem_generatedCore_of_displacement [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (v : V)
    (U : Submodule (ZMod 2) V) {k : ℕ} (hdim : Module.finrank (ZMod 2) U ≤ k)
    (hU : ∀ g, ρ g v - v ∈ U) : v ∈ generatedCore ρ k := by
  let : MulAction G V := {
    smul g w := ρ g w
    one_smul w := LinearMap.congr_fun ρ.map_one w
    mul_smul g h w := LinearMap.congr_fun (ρ.map_mul g h) w }
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let d : MulAction.orbit G v → U := fun w => ⟨w.val - v, by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp w.property
    change ρ g v = w.val at hg
    rw [← hg]
    exact hU g⟩
  have hd : Function.Injective d := by
    intro x y h
    apply Subtype.ext
    exact sub_left_injective (congrArg Subtype.val h)
  have hcard : Nat.card (MulAction.orbit G v) ≤ Nat.card U :=
    Nat.card_le_card_of_injective d hd
  have hidx : Nat.log 2 (MulAction.stabilizer G v).index ≤ k := by
    rw [MulAction.index_stabilizer]
    have hlog := Nat.log_mono_right (b := 2) hcard
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U),
      Nat.card_zmod, Nat.log_pow (by decide)] at hlog
    exact hlog.trans hdim
  exact fixedSpace_le_generatedCore ρ hidx (fun g => g.property)

/-- The core can be computed in the actual faithful action image. -/
theorem generatedCore_actionImage [Finite G]
    (ρ : Representation (ZMod 2) G V) (k : ℕ) :
    generatedCore ρ k = generatedCore (imageRepresentation ρ) k := by
  simpa using generatedCore_map_surjective ρ (imageRepresentation ρ)
    (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective
    (LinearEquiv.refl (ZMod 2) V) (fun _ _ => rfl) k

end BinaryNaturalDual
