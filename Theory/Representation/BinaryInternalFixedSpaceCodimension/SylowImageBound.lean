module

public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.ElementaryAbelian.EightQuotientRank
public import Mathlib.GroupTheory.Sylow

/-!
# The faithful normalizer image of an original Sylow quotient

Squares of the actual ambient Sylow lying in W make its action image
elementary. The original orders512 and64 bound that image by eight. Sylow
conjugacy transfers these statements to every Sylow of the faithful image,
without identifying the full normalizer action kernel with W.
-/

namespace Representation.BinaryInternalFixedSpaceCodimension
open Subgroup BinaryOffender
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

public theorem sylow_image_elementary_eight
    (T : Sylow 2 G) (W : Subgroup G) [IsElementaryAbelian 2 W]
    (hWT : W≤(T : Subgroup G)) (hTW : (T : Subgroup G)≤normalizer (W : Set G))
    (hTc : Nat.card T=512) (hWc : Nat.card W=64)
    (hsq : ∀ x∈(T : Subgroup G), x^2∈W) :
    let I := normalizer (W : Set G)
    let ρ := representation W I le_rfl
    ∀ S : Sylow 2 (actionImage ρ), IsElementaryAbelian 2 S ∧ Nat.card S≤8 := by
  let I := normalizer (W : Set G)
  let ρ := representation W I le_rfl
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  let Q := T.subtype hTW
  let P := Q.mapSurjective (f := q) hq
  have hWker : W.subgroupOf I≤q.ker := by
    intro x hx
    apply (actionHom_eq_one_iff ρ x).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x:G)*(w.toMul:G)*(x:G)⁻¹=(w.toMul:G)
    have he : (x:G)*(w.toMul:G)=(w.toMul:G)*(x:G) :=
      congrArg Subtype.val ((IsMulCommutative.is_comm (M := W)).comm ⟨x,hx⟩ w.toMul)
    rw [he,mul_inv_cancel_right]
  have hpow (x : P) : x^2=1 := by
    obtain ⟨y,hy,he⟩ := x.property
    apply Subtype.ext
    change (x : actionImage ρ)^2=1
    rw [←he,←map_pow]
    exact hWker (hsq y hy)
  have hPe : IsElementaryAbelian 2 P := {
    toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }
  have hPc : Nat.card P≤8 := by
    have hh := IsElementaryAbelian.card_inf_ker_mul_card_map (Q : Subgroup I) q
    have hQc : Nat.card Q=512 :=
      (Nat.card_congr (subgroupOfEquivOfLe hTW).toEquiv).trans hTc
    have hWQ : W.subgroupOf I≤(Q : Subgroup I) := subgroupOf_mono I hWT
    have hkle : 64≤Nat.card ((Q : Subgroup I)⊓q.ker : Subgroup I) := by
      have hh := card_le_of_le (le_inf hWQ hWker)
      rwa [Nat.card_congr (subgroupOfEquivOfLe W.le_normalizer).toEquiv,hWc] at hh
    change Nat.card ((Q : Subgroup I)⊓q.ker : Subgroup I)*Nat.card P=Nat.card Q at hh
    rw [hQc] at hh
    nlinarith
  change ∀ S : Sylow 2 (actionImage ρ), IsElementaryAbelian 2 S ∧ Nat.card S≤8
  intro S
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (actionImage ρ) P S
  have he := congrArg Sylow.toSubgroup hg
  change (P : Subgroup (actionImage ρ)).map (MulAut.conj g).toMonoidHom=(S : Subgroup (actionImage ρ)) at he
  let := hPe
  constructor
  · rw [←he]
    exact IsElementaryAbelian.map _
  · rw [←he,card_map_of_injective (MulAut.conj g).injective]
    exact hPc

end Representation.BinaryInternalFixedSpaceCodimension
