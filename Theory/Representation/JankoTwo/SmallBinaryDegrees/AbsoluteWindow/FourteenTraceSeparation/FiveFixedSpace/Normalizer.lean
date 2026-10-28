module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.LocalGeometry
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.Normalizer.Words
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.Normalizer.Orbit
public import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic.Group

/-!
# The actual J₂ five-plane and its cubic normalizer

The checked words define a homomorphism C₅ × C₅ → J₂. Distinct images of
point zero make it injective, so its image is elementary abelian of order 25.
The two conjugation equations put n⁻¹ in the ambient normalizer of this
image. Its cube is one, and the coordinate certificate says its only fixed
point on the image is the identity. The cubic orbit argument then supplies
three distinct conjugates of every subgroup of index five.

This discharges the group input to the degree-fourteen fixed-space argument,
using the actual degree-100 ATLAS carrier and literal ambient conjugation.
Source: the ATLAS J₂ subgroup 5²:D₁₂ and Guralnick–Malle, Classification of
2F-modules I, Proposition 5.1, manuscript p.16. No representation assumption
or certification of the full order or simplicity of J₂ is needed here.
-/

namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
namespace FiveNormalizer
open Sporadic.LeechRelated.J2 Subgroup Words

private abbrev Model := Multiplicative (ZMod 5 × ZMod 5)
variable {G : Type*} [Group G]
private def planeMap (x y : G) (hx : x ^ 5 = 1) (hy : y ^ 5 = 1) (hc : Commute x y) : Model →* G where
  toFun u := x ^ u.toAdd.1.val * y ^ u.toAdd.2.val
  map_one' := by simp
  map_mul' u v := by
    change x ^ (u.toAdd.1 + v.toAdd.1).val * y ^ (u.toAdd.2 + v.toAdd.2).val = _
    rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ hx, ← pow_eq_pow_mod _ hy,
      pow_add, pow_add]
    calc
      x ^ u.toAdd.1.val * x ^ v.toAdd.1.val * (y ^ u.toAdd.2.val * y ^ v.toAdd.2.val) =
          x ^ u.toAdd.1.val * (x ^ v.toAdd.1.val * y ^ u.toAdd.2.val) * y ^ v.toAdd.2.val := by group
      _ = _ := by rw [(hc.pow_pow _ _).eq]; group

private instance : IsElementaryAbelian 5 Model where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

private theorem card_model : Nat.card Model = 25 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem range_elementary (f : Model →* G) : IsElementaryAbelian 5 f.range where
  toIsMulCommutative := ⟨⟨fun a b => by
    obtain ⟨u, rfl⟩ := f.rangeRestrict_surjective a
    obtain ⟨v, rfl⟩ := f.rangeRestrict_surjective b
    rw [← map_mul, ← map_mul, mul_comm u v]⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro a
    obtain ⟨u, rfl⟩ := f.rangeRestrict_surjective a
    rw [← map_pow, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 5 Model), map_one])

private def coordinates : Model →* Carrier := planeMap x y x_five y_five xy_commute

private theorem coordinates_injective : Function.Injective coordinates := by
  intro u v huv
  have hh := congrArg (fun g : Carrier => (g : Equiv.Perm (Fin 100)) 0) huv
  change ((x : Equiv.Perm (Fin 100)) ^ u.toAdd.1.val * (y : Equiv.Perm (Fin 100)) ^ u.toAdd.2.val) 0 =
    ((x : Equiv.Perm (Fin 100)) ^ v.toAdd.1.val * (y : Equiv.Perm (Fin 100)) ^ v.toAdd.2.val) 0 at hh
  have h := coordinate_injective u.toAdd.1 u.toAdd.2 v.toAdd.1 v.toAdd.2 hh
  exact Prod.ext h.1 h.2

private def P : Subgroup Carrier := coordinates.range

private theorem P_card : Nat.card P = 25 :=
  (Nat.card_congr (MonoidHom.ofInjective coordinates_injective).toEquiv).symm.trans card_model

private theorem P_elementary : IsElementaryAbelian 5 P := range_elementary coordinates

private theorem x_mem : x ∈ P := by
  refine ⟨Multiplicative.ofAdd (1, 0), ?_⟩
  change x ^ 1 * y ^ 0 = x
  simp
private theorem y_mem : y ∈ P := by
  refine ⟨Multiplicative.ofAdd (0, 1), ?_⟩
  change x ^ 0 * y ^ 1 = y
  simp

private theorem nInv_normalizes : n⁻¹ ∈ normalizer (P : Set Carrier) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨g, ⟨u, rfl⟩, rfl⟩
    change (MulAut.conj n⁻¹) (x ^ u.toAdd.1.val * y ^ u.toAdd.2.val) ∈ P
    rw [map_mul, map_pow, map_pow]
    have hx : (MulAut.conj n⁻¹) x = y := by simpa only [MulAut.conj_apply, inv_inv] using conj_x
    have hy : (MulAut.conj n⁻¹) y = x⁻¹ * y⁻¹ := by simpa only [MulAut.conj_apply, inv_inv] using conj_y
    rw [hx, hy]
    exact P.mul_mem (P.pow_mem y_mem _) (P.pow_mem (P.mul_mem (P.inv_mem x_mem) (P.inv_mem y_mem)) _)
  · exact (card_map_of_injective (MulAut.conj n⁻¹).injective).ge

private def normalizerCubic : normalizer (P : Set Carrier) := ⟨n⁻¹, nInv_normalizes⟩

private theorem normalizerCubic_three : normalizerCubic ^ 3 = 1 := by
  apply Subtype.ext
  change (n⁻¹) ^ 3 = 1
  rw [inv_pow, n_three, inv_one]

private theorem normalizerCubic_fixed (u : P) (hu : P.normalizerMonoidHom normalizerCubic u = u) : u = 1 := by
  obtain ⟨v, hv⟩ := u.property
  have hh := congrArg (fun g : P => ((g : Carrier) : Equiv.Perm (Fin 100)) 0) hu
  change ((n : Equiv.Perm (Fin 100))⁻¹ * (u : Carrier) * ((n : Equiv.Perm (Fin 100))⁻¹)⁻¹) 0 =
    ((u : Carrier) : Equiv.Perm (Fin 100)) 0 at hh
  simp only [inv_inv] at hh
  rw [← hv] at hh
  change ((n : Equiv.Perm (Fin 100))⁻¹ *
    ((x : Equiv.Perm (Fin 100)) ^ v.toAdd.1.val * (y : Equiv.Perm (Fin 100)) ^ v.toAdd.2.val) * n) 0 =
    ((x : Equiv.Perm (Fin 100)) ^ v.toAdd.1.val * (y : Equiv.Perm (Fin 100)) ^ v.toAdd.2.val) 0 at hh
  have hz := fixed_coordinate v.toAdd.1 v.toAdd.2 hh
  have hv1 : v = 1 := Prod.ext hz.1 hz.2
  apply Subtype.ext
  rw [← hv, hv1, map_one]
  rfl


end FiveNormalizer

open FiveNormalizer in
/-- An elementary five-plane in the actual Hall–Janko carrier whose ambient
normalizer has no hyperplane orbit of length below three. -/
public theorem fiveNormalizerGeometry : FiveNormalizerGeometry :=
  ⟨P, P_card, P_elementary, orbit_three P P_card normalizerCubic
    normalizerCubic_three normalizerCubic_fixed⟩

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow
