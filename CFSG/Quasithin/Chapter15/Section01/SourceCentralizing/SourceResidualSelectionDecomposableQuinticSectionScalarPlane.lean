module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.ScalarCoinvariants

/-!
# A nonbinary scalar-linear plane cannot support a strong offender

Scalar restriction multiplies the whole moved dimension by the field degree.
Thus a binary moved plane over a larger defining field has field dimension
at most one. Faithful displacement maps then embed the actor into maps from
the fixed quotient to a line, bounding its order by that quotient's order.
This excludes the strong-offender inequality on the actual scalar-linear
module, without replacing the actor or losing a central kernel.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.DecomposableQuinticControl
open ChapterB.QuasisimpleSource

/-- The literal scalar-linear action over a nonbinary field has no strong
actor whose full binary moved space has dimension at most two. -/
theorem not_strong_of_nonbinary_scalar_plane
    (F : BinaryField) {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module F.Carrier W] [Module (ZMod 2) W]
    [IsScalarTower (ZMod 2) F.Carrier W] [FiniteDimensional F.Carrier W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation F.Carrier G W) (hf : Function.Injective ρ)
    (hlarge : 1 < F.degree) (A : Subgroup G)
    (hd : Module.finrank (ZMod 2)
      (subspaceCommutator (restrictScalars (k := ZMod 2) ρ) ⊤ A) ≤ 2) :
    ¬IsStrongOffender (restrictScalars (k := ZMod 2) ρ) A := by
  have hdegree : Module.finrank (ZMod 2) F.Carrier = F.degree := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.Carrier)
    rw [Nat.card_zmod,F.card_eq] at hh
    exact (Nat.pow_right_injective (by decide : 1 < 2) hh).symm
  let U := invariants (ρ.comp A.subtype)
  let C := Coinvariants.ker (ρ.comp A.subtype)
  have hline : Module.finrank F.Carrier C ≤ 1 := by
    rw [moved_finrank_restrictScalars,hdegree] at hd
    change F.degree * Module.finrank F.Carrier C ≤ 2 at hd
    nlinarith
  let δ (a : A) : W →ₗ[F.Carrier] C :=
    (ρ a - LinearMap.id).codRestrict C
      (fun w => Coinvariants.sub_mem_ker (ρ := ρ.comp A.subtype) a w)
  let D (a : A) : (W ⧸ U) →ₗ[F.Carrier] C := U.liftQ (δ a) (by
    intro w hw
    apply Subtype.ext
    exact sub_eq_zero.mpr (hw a))
  have hinj : Function.Injective D := by
    intro a b he
    apply Subtype.ext
    apply hf
    apply LinearMap.ext
    intro w
    have hh := congrArg (fun f : (W ⧸ U) →ₗ[F.Carrier] C => (f (U.mkQ w) : W)) he
    change ρ a w - w = ρ b w - w at hh
    exact sub_left_injective hh
  let : Finite ((W ⧸ U) →ₗ[F.Carrier] C) := Module.finite_of_finite F.Carrier
  have hcard := Nat.card_le_card_of_injective D hinj
  rw [Module.natCard_eq_pow_finrank (K := F.Carrier)
    (V := (W ⧸ U) →ₗ[F.Carrier] C),F.card_eq,
    Module.finrank_linearMap,←pow_mul] at hcard
  have hr := Nat.log_monotone (b := 2) hcard
  rw [Nat.log_pow (by decide : 1 < 2)] at hr
  change rank A ≤ F.degree * (Module.finrank F.Carrier (W ⧸ U) *
    Module.finrank F.Carrier C) at hr
  have hbound : rank A ≤ fixedCodim (restrictScalars (k := ZMod 2) ρ) A := by
    rw [fixedCodim_restrictScalars,hdegree]
    exact hr.trans (by
      simpa only [mul_one] using Nat.mul_le_mul_left F.degree
        (Nat.mul_le_mul_left (Module.finrank F.Carrier (W ⧸ U)) hline))
  exact fun hstrong => (not_lt_of_ge hbound) hstrong.2

end CFSG.Quasithin.Chapter15.DecomposableQuinticControl
