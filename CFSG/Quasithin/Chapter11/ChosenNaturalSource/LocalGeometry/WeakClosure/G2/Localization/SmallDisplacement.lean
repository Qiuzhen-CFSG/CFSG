module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module
public import Mathlib.GroupTheory.Index

/-!
# Small displacement spaces and the source A_k condition

The displacement of a specified vector defines a homomorphism from the
actor to a pointwise fixed subspace. Its kernel has index at most the
order of that subspace. The A_k equality of fixed spaces then makes the
whole actor fix the vector. Exact lifting through a quotient preserves
this argument without a complement to the central kernel.

The concrete G₂ radical application is in Localization.Model.
Source: Aschbacher--Smith B.4.6(12) and 11.2.2(6), pp.89,768.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
variable {H X W : Type*} [Group H]
  [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup W] [Module (ZMod 2) W]

/-- A family member fixes a quotient vector whose displacements lie in a
small pointwise fixed subspace, provided fixed quotient vectors lift. -/
theorem fixes_of_small_displacement
    (σ : Representation (ZMod 2) H X) (ρ : Representation (ZMod 2) H W)
    (q : X →ₗ[ZMod 2] W) (hq : Function.Surjective q)
    (he : ∀ a x, q (σ a x) = ρ a (q x))
    {A : Subgroup H} {k n : ℕ} (hA : A ∈ fixedSpaceFamily σ k)
    (hn : n < k) (U : Submodule (ZMod 2) W) [Finite U]
    (hcard : Nat.card U ≤ 2 ^ n) (v : W)
    (hdisp : ∀ a : A, ρ a v - v ∈ U)
    (hfix : ∀ a : A, ∀ u ∈ U, ρ a u = u)
    (hlift : ∀ a : A, ∀ x, ρ a (q x) = q x → σ a x = x) :
    ∀ a : A, ρ a v = v := by
  let d : A →* Multiplicative U := {
    toFun a := Multiplicative.ofAdd ⟨ρ a v - v, hdisp a⟩
    map_one' := by
      apply Subtype.ext
      change ρ (1 : H) v - v = 0
      simp
    map_mul' a b := by
      apply Subtype.ext
      change ρ (a.val * b.val) v - v = (ρ a.val v - v) + (ρ b.val v - v)
      have hh := hfix a (ρ b.val v - v) (hdisp b)
      rw [map_sub] at hh
      rw [map_mul, Module.End.mul_apply]
      calc
        ρ a.val (ρ b.val v) - v =
            (ρ a.val (ρ b.val v) - ρ a.val v) + (ρ a.val v - v) := by abel
        _ = (ρ a.val v - v) + (ρ b.val v - v) := by rw [hh]; abel }
  let B := d.ker.map A.subtype
  have hBA : B ≤ A := map_subtype_le _
  have hindex : B.relIndex A = Nat.card d.range := by
    have hh := relIndex_map_map_of_injective d.ker (⊤ : Subgroup A) A.subtype_injective
    simpa only [← MonoidHom.range_eq_map, A.range_subtype, relIndex_top_right, index_ker] using hh
  have hsmall : Nat.log 2 (B.relIndex A) < k := by
    rw [hindex]
    have hh := Nat.log_mono_right ((card_le_card_group d.range).trans hcard) (b := 2)
    rw [Nat.log_pow (by decide : 1 < 2)] at hh
    omega
  have hfixed := hA.2.2 B hBA hsmall
  obtain ⟨x,rfl⟩ := hq v
  have hx : x ∈ fixedSpace σ B := by
    rintro ⟨b,hb⟩
    obtain ⟨a,ha,rfl⟩ := hb
    apply hlift a x
    have hd := congrArg (fun z : Multiplicative U => (z.toAdd : W)) ha
    change ρ a (q x) - q x = 0 at hd
    exact sub_eq_zero.mp hd
  rw [← hfixed] at hx
  intro a
  exact (he a x).symm.trans (congrArg q (hx a))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Localization
