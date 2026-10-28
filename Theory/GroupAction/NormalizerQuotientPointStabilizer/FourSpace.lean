module

public import Theory.GroupAction.NormalizerQuotientPointStabilizer
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.LinearAlgebra.BinaryFourPointStabilizer

/-!
# The point-fixing action on an elementary sixteen

Conjugation embeds the literal normalizer/centralizer quotient faithfully in
GL₄(2). Restricting an actor that fixes a nonidentity point embeds its image
in the point stabilizer of order 1344. In particular its image order is not
divisible by nine.

Application: the residual normalizer in the split branch of Aschbacher–Smith,
14.4.4(6), printed p.1007. The argument retains the ambient quotient map.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace Subgroup.NormalizerAction
/-- An actor fixing a nonidentity point of an elementary sixteen has image
order dividing the order 1344 of the binary four-space point stabilizer. -/
theorem sylowImage_card_dvd_of_fixed_point_sixteen {G : Type*} [Group G] [Finite G]
    (A R : Subgroup G) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 16) (z : A) (hz : z ≠ 1)
    (hfix : R ≤ centralizer ({(z : G)} : Set G)) :
    Nat.card (sylowImage A R) ∣ 1344 := by
  let autLinear : MulAut A →* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun a => { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
      map_one' := by ext; rfl
      map_mul' := by intros; ext; rfl }
  have hdim : Module.finrank (ZMod 2) (Additive A) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    change Nat.card A = _ at hc
    simpa only [Nat.card_zmod, hcard] using hc.symm
  let S := Theory.LinearAlgebra.BinaryFivePointStabilizer.stabilizer (Additive.ofMul z)
  let f : sylowImage A R →* S :=
    ((autLinear.comp (action A)).comp (sylowImage A R).subtype).codRestrict S (by
      rintro ⟨x,hx⟩
      obtain ⟨n,hn,rfl⟩ := hx
      exact (quotient_mem_pointStabilizer A z n).mpr (hfix hn))
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply action_injective A
    apply MulEquiv.ext
    intro a
    exact congrArg (fun k : S => k.val (Additive.ofMul a)) he
  have hd := card_dvd_of_injective f hf
  rwa [Theory.LinearAlgebra.BinaryFourPointStabilizer.card_stabilizer
    (Additive.ofMul z) hz hdim] at hd
end Subgroup.NormalizerAction
